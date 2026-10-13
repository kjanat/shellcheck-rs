package main

import (
	"archive/tar"
	"archive/zip"
	"bytes"
	"compress/gzip"
	"crypto/sha256"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"runtime"
	"runtime/debug"
	"strings"
	"time"
)

const (
	releaseBase    = "https://github.com/kjanat/shellcheck-rs/releases/download"
	tagPrefix      = "rshellcheck-v"
	maxArchive     = 256 << 20
	installWait    = 2 * time.Minute
	staleLock      = 10 * time.Minute
	pollInterval   = 100 * time.Millisecond
	wrapperFailure = 2
)

var targets = map[string]string{
	"linux/amd64":   "x86_64-unknown-linux-musl",
	"linux/386":     "i686-unknown-linux-musl",
	"linux/arm64":   "aarch64-unknown-linux-musl",
	"linux/arm":     "armv7-unknown-linux-musleabihf",
	"darwin/amd64":  "x86_64-apple-darwin",
	"darwin/arm64":  "aarch64-apple-darwin",
	"windows/amd64": "x86_64-pc-windows-msvc",
	"windows/386":   "i686-pc-windows-msvc",
	"windows/arm64": "aarch64-pc-windows-msvc",
	"freebsd/amd64": "x86_64-unknown-freebsd",
	"freebsd/386":   "i686-unknown-freebsd",
	"android/arm64": "aarch64-linux-android",
	"android/arm":   "armv7-linux-androideabi",
	"android/amd64": "x86_64-linux-android",
	"android/386":   "i686-linux-android",
}

var (
	taggedVersion = regexp.MustCompile(`^v\d+\.\d+\.\d+(-[0-9A-Za-z.]+)?$`)
	pseudoVersion = regexp.MustCompile(`-\d{14}-[0-9a-f]{12}$`)
)

type release struct {
	label   string
	target  string
	windows bool
	base    string
	dir     string
}

func main() {
	os.Exit(run(os.Args[1:], os.Stdin, os.Stdout, os.Stderr))
}

func run(args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	cache, err := os.UserCacheDir()
	if err != nil {
		fmt.Fprintf(stderr, "shellcheck: %v\n", err)
		return wrapperFailure
	}
	rel, err := resolve(moduleVersion(), runtime.GOOS, runtime.GOARCH, releaseBase, cache)
	if err != nil {
		fmt.Fprintf(stderr, "shellcheck: %v\n", err)
		return wrapperFailure
	}
	binary, err := rel.ensure(&http.Client{Timeout: 5 * time.Minute})
	if err != nil {
		fmt.Fprintf(stderr, "shellcheck: %v\n", err)
		return wrapperFailure
	}
	return execute(binary, args, stdin, stdout, stderr)
}

func moduleVersion() string {
	info, ok := debug.ReadBuildInfo()
	if !ok {
		return ""
	}
	return info.Main.Version
}

func resolve(version, goos, goarch, base, cache string) (*release, error) {
	if !taggedVersion.MatchString(version) || pseudoVersion.MatchString(version) {
		return nil, fmt.Errorf("built from %q; install a tagged version, for example go install github.com/kjanat/shellcheck-rs/go/cmd/shellcheck@v0.11.0", version)
	}
	target, ok := targets[goos+"/"+goarch]
	if !ok {
		return nil, fmt.Errorf("no rshellcheck release for %s/%s", goos, goarch)
	}
	label := strings.TrimPrefix(version, "v")
	return &release{
		label:   label,
		target:  target,
		windows: goos == "windows",
		base:    base + "/" + tagPrefix + label,
		dir:     filepath.Join(cache, "rshellcheck", label, target),
	}, nil
}

func (r *release) archive() string {
	if r.windows {
		return fmt.Sprintf("rshellcheck-%s-%s.zip", r.label, r.target)
	}
	return fmt.Sprintf("rshellcheck-%s-%s.tar.gz", r.label, r.target)
}

func (r *release) member() string {
	name := "rshellcheck"
	if r.windows {
		name += ".exe"
	}
	return fmt.Sprintf("rshellcheck-%s-%s/%s", r.label, r.target, name)
}

func (r *release) binary() string {
	return filepath.Join(r.dir, filepath.Base(r.member()))
}

func (r *release) ensure(client *http.Client) (string, error) {
	binary := r.binary()
	if _, err := os.Stat(binary); err == nil {
		return binary, nil
	}
	if err := os.MkdirAll(r.dir, 0o755); err != nil {
		return "", err
	}
	lock := binary + ".lock"
	deadline := time.Now().Add(installWait)
	for {
		handle, err := os.OpenFile(lock, os.O_CREATE|os.O_EXCL|os.O_WRONLY, 0o644)
		if err == nil {
			handle.Close()
			if _, err := os.Stat(binary); err == nil {
				os.Remove(lock)
				return binary, nil
			}
			err = r.install(client, binary)
			os.Remove(lock)
			if err != nil {
				return "", err
			}
			return binary, nil
		}
		if !errors.Is(err, os.ErrExist) {
			return "", err
		}
		if _, err := os.Stat(binary); err == nil {
			return binary, nil
		}
		if info, err := os.Stat(lock); err == nil && time.Since(info.ModTime()) > staleLock {
			os.Remove(lock)
			continue
		}
		if time.Now().After(deadline) {
			return "", fmt.Errorf("another process has been installing %s for over %s", binary, installWait)
		}
		time.Sleep(pollInterval)
	}
}

func (r *release) install(client *http.Client, binary string) error {
	sums, err := fetch(client, r.base+"/SHA256SUMS")
	if err != nil {
		return err
	}
	want, err := checksum(sums, r.archive())
	if err != nil {
		return err
	}
	data, err := fetch(client, r.base+"/"+r.archive())
	if err != nil {
		return err
	}
	got := sha256.Sum256(data)
	if hex.EncodeToString(got[:]) != want {
		return fmt.Errorf("%s: SHA-256 %x does not match SHA256SUMS", r.archive(), got)
	}
	var contents []byte
	if r.windows {
		contents, err = fromZip(data, r.member())
	} else {
		contents, err = fromTarGz(data, r.member())
	}
	if err != nil {
		return fmt.Errorf("%s: %w", r.archive(), err)
	}
	temp, err := os.CreateTemp(r.dir, ".rshellcheck-*")
	if err != nil {
		return err
	}
	name := temp.Name()
	if _, err := temp.Write(contents); err != nil {
		temp.Close()
		os.Remove(name)
		return err
	}
	if err := temp.Close(); err != nil {
		os.Remove(name)
		return err
	}
	if err := os.Chmod(name, 0o755); err != nil {
		os.Remove(name)
		return err
	}
	if err := os.Rename(name, binary); err != nil {
		os.Remove(name)
		if _, statErr := os.Stat(binary); statErr == nil {
			return nil
		}
		return err
	}
	return nil
}

func fetch(client *http.Client, url string) ([]byte, error) {
	response, err := client.Get(url)
	if err != nil {
		return nil, err
	}
	defer response.Body.Close()
	if response.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("GET %s: %s", url, response.Status)
	}
	data, err := io.ReadAll(io.LimitReader(response.Body, maxArchive+1))
	if err != nil {
		return nil, fmt.Errorf("GET %s: %w", url, err)
	}
	if len(data) > maxArchive {
		return nil, fmt.Errorf("GET %s: response exceeds %d bytes", url, maxArchive)
	}
	return data, nil
}

func checksum(sums []byte, name string) (string, error) {
	for _, line := range strings.Split(string(sums), "\n") {
		fields := strings.Fields(line)
		if len(fields) == 2 && fields[1] == name && len(fields[0]) == sha256.Size*2 {
			return strings.ToLower(fields[0]), nil
		}
	}
	return "", fmt.Errorf("SHA256SUMS has no entry for %s", name)
}

func fromTarGz(data []byte, member string) ([]byte, error) {
	unzipped, err := gzip.NewReader(bytes.NewReader(data))
	if err != nil {
		return nil, err
	}
	archive := tar.NewReader(unzipped)
	for {
		header, err := archive.Next()
		if errors.Is(err, io.EOF) {
			return nil, fmt.Errorf("no member %s", member)
		}
		if err != nil {
			return nil, err
		}
		if header.Name == member && header.Typeflag == tar.TypeReg {
			return io.ReadAll(io.LimitReader(archive, maxArchive))
		}
	}
}

func fromZip(data []byte, member string) ([]byte, error) {
	archive, err := zip.NewReader(bytes.NewReader(data), int64(len(data)))
	if err != nil {
		return nil, err
	}
	for _, file := range archive.File {
		if file.Name != member {
			continue
		}
		handle, err := file.Open()
		if err != nil {
			return nil, err
		}
		defer handle.Close()
		return io.ReadAll(io.LimitReader(handle, maxArchive))
	}
	return nil, fmt.Errorf("no member %s", member)
}

func execute(binary string, args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	command := exec.Command(binary, args...)
	command.Stdin = stdin
	command.Stdout = stdout
	command.Stderr = stderr
	err := command.Run()
	if err == nil {
		return 0
	}
	var exit *exec.ExitError
	if errors.As(err, &exit) && exit.ExitCode() >= 0 {
		return exit.ExitCode()
	}
	fmt.Fprintf(stderr, "shellcheck: %v\n", err)
	return wrapperFailure
}
