package main

import (
	"archive/tar"
	"archive/zip"
	"bytes"
	"compress/gzip"
	"crypto/sha256"
	"fmt"
	"io"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"runtime"
	"strings"
	"sync/atomic"
	"testing"
	"time"
)

const (
	helperEnv = "RSHELLCHECK_HELPER_PROCESS"
	ghEnv     = "RSHELLCHECK_HELPER_GH"
	ghLogEnv  = "RSHELLCHECK_HELPER_GH_LOG"
)

func TestMain(m *testing.M) {
	if mode := os.Getenv(ghEnv); mode != "" {
		if log := os.Getenv(ghLogEnv); log != "" {
			handle, err := os.OpenFile(log, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0o644)
			if err != nil {
				os.Exit(99)
			}
			fmt.Fprintln(handle, strings.Join(os.Args[1:], " "))
			handle.Close()
		}
		switch mode {
		case "ok":
			os.Exit(0)
		case "noauth":
			fmt.Fprintln(os.Stderr, "To get started with GitHub CLI, please run:  gh auth login")
			os.Exit(4)
		default:
			fmt.Fprintln(os.Stderr, "Error: HTTP 404: Not Found")
			os.Exit(1)
		}
	}
	if os.Getenv(helperEnv) == "1" {
		args := os.Args[1:]
		for i, arg := range args {
			if arg == "--" {
				args = args[i+1:]
				break
			}
		}
		fmt.Println(strings.Join(args, " "))
		input, _ := io.ReadAll(os.Stdin)
		fmt.Fprintf(os.Stderr, "stdin=%s", input)
		os.Exit(3)
	}
	os.Exit(m.Run())
}

func TestResolveCoversEveryReleaseTarget(t *testing.T) {
	for platform, target := range targets {
		goos, goarch, _ := strings.Cut(platform, "/")
		rel, err := resolve("v0.11.0", goos, goarch, "https://example.test/d", "/cache")
		if err != nil {
			t.Fatalf("%s: %v", platform, err)
		}
		if rel.target != target || rel.label != "0.11.0" {
			t.Fatalf("%s: %+v", platform, rel)
		}
		if rel.base != "https://example.test/d/rshellcheck-v0.11.0" {
			t.Fatalf("%s: base %s", platform, rel.base)
		}
		if rel.dir != filepath.Join("/cache", "rshellcheck", "0.11.0", target) {
			t.Fatalf("%s: dir %s", platform, rel.dir)
		}
		if rel.windows != (goos == "windows") {
			t.Fatalf("%s: windows %v", platform, rel.windows)
		}
	}
}

func TestResolveNamesArchivesLikeTheRelease(t *testing.T) {
	linux, _ := resolve("v0.11.0", "linux", "amd64", "b", "c")
	if linux.archive() != "rshellcheck-0.11.0-x86_64-unknown-linux-musl.tar.gz" {
		t.Fatal(linux.archive())
	}
	if linux.member() != "rshellcheck-0.11.0-x86_64-unknown-linux-musl/rshellcheck" {
		t.Fatal(linux.member())
	}
	windows, _ := resolve("v0.12.0-rc.1", "windows", "arm64", "b", "c")
	if windows.archive() != "rshellcheck-0.12.0-rc.1-aarch64-pc-windows-msvc.zip" {
		t.Fatal(windows.archive())
	}
	if windows.member() != "rshellcheck-0.12.0-rc.1-aarch64-pc-windows-msvc/rshellcheck.exe" {
		t.Fatal(windows.member())
	}
	if filepath.Base(windows.binary()) != "rshellcheck.exe" {
		t.Fatal(windows.binary())
	}
}

func TestWrapperRevisionsShareTheirRelease(t *testing.T) {
	cases := map[string]string{
		"v0.11.0":                     "0.11.0",
		"v0.11.0-wrapper.1":           "0.11.0",
		"v0.11.0-wrapper.12":          "0.11.0",
		"v0.12.0-rc.1":                "0.12.0-rc.1",
		"v0.12.0-rc.1-wrapper.2":      "0.12.0-rc.1",
		"v0.11.0-wrapper":             "0.11.0-wrapper",
		"v0.11.0-wrapper.x":           "0.11.0-wrapper.x",
		"v0.11.0-wrapper.1-rc.1":      "0.11.0-wrapper.1-rc.1",
		"v0.11.0-wrapper.1-wrapper.2": "0.11.0-wrapper.1",
		"v0.12.0-rc.1.wrapper.2":      "0.12.0-rc.1.wrapper.2",
	}
	for version, label := range cases {
		if got := releaseLabel(version); got != label {
			t.Errorf("%s: %s", version, got)
		}
	}
	rel, err := resolve("v0.11.0-wrapper.1", "linux", "amd64", "https://example.test/d", "/cache")
	if err != nil {
		t.Fatal(err)
	}
	if rel.base != "https://example.test/d/rshellcheck-v0.11.0" || rel.archive() != "rshellcheck-0.11.0-x86_64-unknown-linux-musl.tar.gz" {
		t.Fatalf("%+v", rel)
	}
	if rel.dir != filepath.Join("/cache", "rshellcheck", "0.11.0", "x86_64-unknown-linux-musl") {
		t.Fatal(rel.dir)
	}
	pre, err := resolve("v0.12.0-rc.1-wrapper.2", "windows", "amd64", "https://example.test/d", "/cache")
	if err != nil {
		t.Fatal(err)
	}
	if pre.base != "https://example.test/d/rshellcheck-v0.12.0-rc.1" || pre.archive() != "rshellcheck-0.12.0-rc.1-x86_64-pc-windows-msvc.zip" {
		t.Fatalf("%+v", pre)
	}
}

func TestResolveRejectsUntaggedBuildsAndUnknownPlatforms(t *testing.T) {
	for _, version := range []string{"", "(devel)", "v0.0.0-20261013094512-67f912e61b5a", "v0.11.0+dirty", "0.11.0"} {
		if _, err := resolve(version, "linux", "amd64", "b", "c"); err == nil {
			t.Fatalf("%q resolved", version)
		}
	}
	if _, err := resolve("v0.11.0", "linux", "riscv64", "b", "c"); err == nil {
		t.Fatal("riscv64 resolved")
	}
}

func TestChecksumFindsTheNamedEntry(t *testing.T) {
	sums := []byte("" +
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef  a.tar.gz\n" +
		"FEDCBA9876543210FEDCBA9876543210FEDCBA9876543210FEDCBA9876543210  b.tar.gz\n")
	got, err := checksum(sums, "b.tar.gz")
	if err != nil || got != "fedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210" {
		t.Fatal(got, err)
	}
	if _, err := checksum(sums, "c.tar.gz"); err == nil {
		t.Fatal("missing entry accepted")
	}
}

type fakeRelease struct {
	server *httptest.Server
	hits   atomic.Int32
}

func serve(t *testing.T, files map[string][]byte) *fakeRelease {
	t.Helper()
	fake := &fakeRelease{}
	fake.server = httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		fake.hits.Add(1)
		data, ok := files[r.URL.Path]
		if !ok {
			http.NotFound(w, r)
			return
		}
		w.Write(data)
	}))
	t.Cleanup(fake.server.Close)
	return fake
}

func tarGz(t *testing.T, member string, contents []byte) []byte {
	t.Helper()
	var buf bytes.Buffer
	gz := gzip.NewWriter(&buf)
	tw := tar.NewWriter(gz)
	for _, name := range []string{"rshellcheck-0.11.0-x/LICENSE", member} {
		body := []byte("license")
		if name == member {
			body = contents
		}
		if err := tw.WriteHeader(&tar.Header{Name: name, Mode: 0o755, Size: int64(len(body)), Typeflag: tar.TypeReg}); err != nil {
			t.Fatal(err)
		}
		if _, err := tw.Write(body); err != nil {
			t.Fatal(err)
		}
	}
	if err := tw.Close(); err != nil {
		t.Fatal(err)
	}
	if err := gz.Close(); err != nil {
		t.Fatal(err)
	}
	return buf.Bytes()
}

func zipped(t *testing.T, member string, contents []byte) []byte {
	t.Helper()
	var buf bytes.Buffer
	zw := zip.NewWriter(&buf)
	for _, name := range []string{"rshellcheck-0.11.0-x/LICENSE", member} {
		body := []byte("license")
		if name == member {
			body = contents
		}
		w, err := zw.Create(name)
		if err != nil {
			t.Fatal(err)
		}
		if _, err := w.Write(body); err != nil {
			t.Fatal(err)
		}
	}
	if err := zw.Close(); err != nil {
		t.Fatal(err)
	}
	return buf.Bytes()
}

func sumsFor(archive string, data []byte) []byte {
	sum := sha256.Sum256(data)
	return fmt.Appendf(nil, "%x  other.tar.gz\n%x  %s\n", sha256.Sum256([]byte("other")), sum, archive)
}

func TestEnsureDownloadsVerifiesAndCaches(t *testing.T) {
	rel, _ := resolve("v0.11.0", "linux", "amd64", "", t.TempDir())
	var log bytes.Buffer
	rel.log = &log
	defer func() {
		if log.String() != "shellcheck: rshellcheck-0.11.0-x86_64-unknown-linux-musl.tar.gz: provenance not verified, gh is not installed\n" {
			t.Errorf("log %q", log.String())
		}
	}()
	payload := []byte("#!/bin/sh\necho native\n")
	archive := tarGz(t, rel.member(), payload)
	fake := serve(t, map[string][]byte{
		"/rshellcheck-v0.11.0/SHA256SUMS":                                          sumsFor(rel.archive(), archive),
		"/rshellcheck-v0.11.0/rshellcheck-0.11.0-x86_64-unknown-linux-musl.tar.gz": archive,
	})
	rel.base = fake.server.URL + "/rshellcheck-v0.11.0"

	binary, err := rel.ensure(fake.server.Client())
	if err != nil {
		t.Fatal(err)
	}
	got, err := os.ReadFile(binary)
	if err != nil || !bytes.Equal(got, payload) {
		t.Fatalf("%q %v", got, err)
	}
	info, err := os.Stat(binary)
	if err != nil {
		t.Fatal(err)
	}
	if runtime.GOOS != "windows" && info.Mode()&0o100 == 0 {
		t.Fatalf("mode %v", info.Mode())
	}
	if fake.hits.Load() != 2 {
		t.Fatalf("%d requests", fake.hits.Load())
	}
	if _, err := os.Stat(binary + ".lock"); !os.IsNotExist(err) {
		t.Fatal("lock left behind")
	}

	again, err := rel.ensure(fake.server.Client())
	if err != nil || again != binary {
		t.Fatal(again, err)
	}
	if fake.hits.Load() != 2 {
		t.Fatalf("%d requests after a cache hit", fake.hits.Load())
	}
}

func ghRelease(t *testing.T, mode string) (*release, *fakeRelease, string) {
	t.Helper()
	rel, _ := resolve("v0.11.0", "linux", "amd64", "", t.TempDir())
	archive := tarGz(t, rel.member(), []byte("native"))
	fake := serve(t, map[string][]byte{
		"/rshellcheck-v0.11.0/SHA256SUMS":                                          sumsFor(rel.archive(), archive),
		"/rshellcheck-v0.11.0/rshellcheck-0.11.0-x86_64-unknown-linux-musl.tar.gz": archive,
	})
	rel.base = fake.server.URL + "/rshellcheck-v0.11.0"
	rel.gh = os.Args[0]
	calls := filepath.Join(t.TempDir(), "gh.log")
	t.Setenv(ghEnv, mode)
	t.Setenv(ghLogEnv, calls)
	return rel, fake, calls
}

func TestInstallVerifiesProvenanceWithGh(t *testing.T) {
	rel, fake, calls := ghRelease(t, "ok")
	var log bytes.Buffer
	rel.log = &log
	binary, err := rel.ensure(fake.server.Client())
	if err != nil {
		t.Fatal(err)
	}
	got, _ := os.ReadFile(binary)
	if string(got) != "native" {
		t.Fatalf("%q", got)
	}
	if log.Len() != 0 {
		t.Fatalf("log %q", log.String())
	}
	invocation, err := os.ReadFile(calls)
	if err != nil {
		t.Fatal(err)
	}
	line := strings.TrimSpace(string(invocation))
	for _, want := range []string{
		"attestation verify " + filepath.Join(rel.dir, ".archive-"),
		" --repo kjanat/shellcheck-rs ",
		" --signer-workflow kjanat/shellcheck-rs/.github/workflows/release.yml ",
		" --source-ref refs/tags/rshellcheck-v0.11.0",
	} {
		if !strings.Contains(line, want) {
			t.Errorf("gh invocation %q lacks %q", line, want)
		}
	}
	if strings.Count(string(invocation), "\n") != 1 {
		t.Fatalf("gh ran %d times", strings.Count(string(invocation), "\n"))
	}
	entries, err := os.ReadDir(rel.dir)
	if err != nil {
		t.Fatal(err)
	}
	if len(entries) != 1 || entries[0].Name() != "rshellcheck" {
		t.Fatalf("cache dir holds %v", entries)
	}
}

func TestInstallFailsWhenProvenanceVerificationFails(t *testing.T) {
	rel, fake, _ := ghRelease(t, "fail")
	_, err := rel.ensure(fake.server.Client())
	if err == nil || !strings.Contains(err.Error(), "provenance verification failed") || !strings.Contains(err.Error(), "HTTP 404") {
		t.Fatal(err)
	}
	if _, err := os.Stat(rel.binary()); !os.IsNotExist(err) {
		t.Fatal("binary installed despite a failed verification")
	}
	entries, _ := os.ReadDir(rel.dir)
	if len(entries) != 0 {
		t.Fatalf("cache dir holds %v", entries)
	}
}

func TestInstallSkipsVerificationWhenGhIsSignedOut(t *testing.T) {
	rel, fake, _ := ghRelease(t, "noauth")
	var log bytes.Buffer
	rel.log = &log
	binary, err := rel.ensure(fake.server.Client())
	if err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(binary); err != nil {
		t.Fatal(err)
	}
	if log.String() != "shellcheck: rshellcheck-0.11.0-x86_64-unknown-linux-musl.tar.gz: provenance not verified, gh is not signed in\n" {
		t.Fatalf("log %q", log.String())
	}
}

func TestEnsureUnpacksZipReleases(t *testing.T) {
	rel, _ := resolve("v0.11.0", "windows", "amd64", "", t.TempDir())
	payload := []byte("MZ fake")
	archive := zipped(t, rel.member(), payload)
	fake := serve(t, map[string][]byte{
		"/rshellcheck-v0.11.0/SHA256SUMS":                                    sumsFor(rel.archive(), archive),
		"/rshellcheck-v0.11.0/rshellcheck-0.11.0-x86_64-pc-windows-msvc.zip": archive,
	})
	rel.base = fake.server.URL + "/rshellcheck-v0.11.0"
	binary, err := rel.ensure(fake.server.Client())
	if err != nil {
		t.Fatal(err)
	}
	if filepath.Base(binary) != "rshellcheck.exe" {
		t.Fatal(binary)
	}
	got, _ := os.ReadFile(binary)
	if !bytes.Equal(got, payload) {
		t.Fatalf("%q", got)
	}
}

func TestEnsureRejectsAChecksumMismatch(t *testing.T) {
	rel, _ := resolve("v0.11.0", "linux", "amd64", "", t.TempDir())
	archive := tarGz(t, rel.member(), []byte("real"))
	fake := serve(t, map[string][]byte{
		"/rshellcheck-v0.11.0/SHA256SUMS":                                          sumsFor(rel.archive(), []byte("something else")),
		"/rshellcheck-v0.11.0/rshellcheck-0.11.0-x86_64-unknown-linux-musl.tar.gz": archive,
	})
	rel.base = fake.server.URL + "/rshellcheck-v0.11.0"
	_, err := rel.ensure(fake.server.Client())
	if err == nil || !strings.Contains(err.Error(), "does not match SHA256SUMS") {
		t.Fatal(err)
	}
	if _, err := os.Stat(rel.binary()); !os.IsNotExist(err) {
		t.Fatal("binary installed despite mismatch")
	}
	if _, err := os.Stat(rel.binary() + ".lock"); !os.IsNotExist(err) {
		t.Fatal("lock left behind")
	}
}

func TestEnsureRejectsAMissingChecksumEntryBeforeDownloading(t *testing.T) {
	rel, _ := resolve("v0.11.0", "linux", "amd64", "", t.TempDir())
	fake := serve(t, map[string][]byte{
		"/rshellcheck-v0.11.0/SHA256SUMS": sumsFor("rshellcheck-0.11.0-other.tar.gz", []byte("x")),
	})
	rel.base = fake.server.URL + "/rshellcheck-v0.11.0"
	_, err := rel.ensure(fake.server.Client())
	if err == nil || !strings.Contains(err.Error(), "no entry for") {
		t.Fatal(err)
	}
	if fake.hits.Load() != 1 {
		t.Fatalf("%d requests", fake.hits.Load())
	}
}

func TestEnsureRejectsAnArchiveWithoutTheBinary(t *testing.T) {
	rel, _ := resolve("v0.11.0", "linux", "amd64", "", t.TempDir())
	archive := tarGz(t, "rshellcheck-0.11.0-x86_64-unknown-linux-musl/README.md", []byte("docs"))
	fake := serve(t, map[string][]byte{
		"/rshellcheck-v0.11.0/SHA256SUMS":                                          sumsFor(rel.archive(), archive),
		"/rshellcheck-v0.11.0/rshellcheck-0.11.0-x86_64-unknown-linux-musl.tar.gz": archive,
	})
	rel.base = fake.server.URL + "/rshellcheck-v0.11.0"
	_, err := rel.ensure(fake.server.Client())
	if err == nil || !strings.Contains(err.Error(), "no member") {
		t.Fatal(err)
	}
}

func TestEnsureWaitsForAnotherInstaller(t *testing.T) {
	rel, _ := resolve("v0.11.0", "linux", "amd64", "", t.TempDir())
	fake := serve(t, map[string][]byte{})
	rel.base = fake.server.URL + "/rshellcheck-v0.11.0"
	if err := os.MkdirAll(rel.dir, 0o755); err != nil {
		t.Fatal(err)
	}
	lock := rel.binary() + ".lock"
	if err := os.WriteFile(lock, nil, 0o644); err != nil {
		t.Fatal(err)
	}
	go func() {
		time.Sleep(300 * time.Millisecond)
		os.WriteFile(rel.binary(), []byte("installed elsewhere"), 0o755)
		os.Remove(lock)
	}()
	binary, err := rel.ensure(fake.server.Client())
	if err != nil {
		t.Fatal(err)
	}
	got, _ := os.ReadFile(binary)
	if string(got) != "installed elsewhere" {
		t.Fatalf("%q", got)
	}
	if fake.hits.Load() != 0 {
		t.Fatalf("%d requests while another installer held the lock", fake.hits.Load())
	}
}

func TestEnsureBreaksAStaleLock(t *testing.T) {
	rel, _ := resolve("v0.11.0", "linux", "amd64", "", t.TempDir())
	payload := []byte("fresh")
	archive := tarGz(t, rel.member(), payload)
	fake := serve(t, map[string][]byte{
		"/rshellcheck-v0.11.0/SHA256SUMS":                                          sumsFor(rel.archive(), archive),
		"/rshellcheck-v0.11.0/rshellcheck-0.11.0-x86_64-unknown-linux-musl.tar.gz": archive,
	})
	rel.base = fake.server.URL + "/rshellcheck-v0.11.0"
	if err := os.MkdirAll(rel.dir, 0o755); err != nil {
		t.Fatal(err)
	}
	lock := rel.binary() + ".lock"
	if err := os.WriteFile(lock, nil, 0o644); err != nil {
		t.Fatal(err)
	}
	old := time.Now().Add(-staleLock - time.Minute)
	if err := os.Chtimes(lock, old, old); err != nil {
		t.Fatal(err)
	}
	binary, err := rel.ensure(fake.server.Client())
	if err != nil {
		t.Fatal(err)
	}
	got, _ := os.ReadFile(binary)
	if !bytes.Equal(got, payload) {
		t.Fatalf("%q", got)
	}
}

func TestExecutePassesThroughArgumentsStreamsAndExitCode(t *testing.T) {
	t.Setenv(helperEnv, "1")
	var stdout, stderr bytes.Buffer
	code := execute(os.Args[0], []string{"--", "--norc", "-f", "json1", "-"}, strings.NewReader("echo $x\n"), &stdout, &stderr)
	if code != 3 {
		t.Fatalf("exit %d, stderr %q", code, stderr.String())
	}
	if stdout.String() != "--norc -f json1 -\n" {
		t.Fatalf("stdout %q", stdout.String())
	}
	if stderr.String() != "stdin=echo $x\n" {
		t.Fatalf("stderr %q", stderr.String())
	}
}

func TestExecuteReportsAMissingBinary(t *testing.T) {
	var stderr bytes.Buffer
	code := execute(filepath.Join(t.TempDir(), "absent"), nil, strings.NewReader(""), io.Discard, &stderr)
	if code != wrapperFailure || !strings.HasPrefix(stderr.String(), "shellcheck: ") {
		t.Fatal(code, stderr.String())
	}
}
