package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"testing"
)

func TestSourcePinnedWrapperUsesBundledRelease(t *testing.T) {
	for _, version := range []string{"v0.0.0-20261013094512-67f912e61b5a", "v0.11.1-0.20261021094512-67f912e61b5a", "v0.11.0-wrapper.1.0.20261021094512-67f912e61b5a"} {
		rel, err := resolve(version, "linux", "amd64", releaseBase, t.TempDir())
		if err != nil || rel.label != bundledVersion || rel.proof == nil {
			t.Fatalf("%s: %+v %v", version, rel, err)
		}
	}
	other, err := resolve("v0.12.0", "linux", "amd64", releaseBase, t.TempDir())
	if err != nil || other.proof != nil || other.label != "0.12.0" {
		t.Fatalf("%+v %v", other, err)
	}
}

func TestReviewedAssetsMatchEverySignedReleaseSubject(t *testing.T) {
	var bundle struct {
		Envelope struct {
			Payload []byte `json:"payload"`
		} `json:"dsseEnvelope"`
	}
	if err := json.Unmarshal(provenanceBundle, &bundle); err != nil {
		t.Fatal(err)
	}
	var statement struct {
		Subjects []struct {
			Name   string `json:"name"`
			Digest struct {
				SHA256 string `json:"sha256"`
			} `json:"digest"`
		} `json:"subject"`
	}
	if err := json.Unmarshal(bundle.Envelope.Payload, &statement); err != nil {
		t.Fatal(err)
	}
	if len(reviewedAssets) != len(targets) {
		t.Fatalf("%d reviewed assets for %d targets", len(reviewedAssets), len(targets))
	}
	for platform := range targets {
		goos, goarch, _ := strings.Cut(platform, "/")
		rel, err := resolve("v"+bundledVersion, goos, goarch, releaseBase, t.TempDir())
		if err != nil {
			t.Fatal(err)
		}
		matches := 0
		for _, subject := range statement.Subjects {
			if subject.Name == rel.archive() && subject.Digest.SHA256 == rel.proof.archiveSHA256 {
				matches++
			}
		}
		if matches != 1 || len(rel.proof.binarySHA256) != sha256.Size*2 {
			t.Fatalf("%s has %d matching signed subjects", platform, matches)
		}
	}
}

func TestReviewedInstallAndWarmCacheUseIndependentPins(t *testing.T) {
	rel, fake, calls := ghRelease(t, "ok")
	archive, err := fetch(fake.server.Client(), rel.base+"/"+rel.archive())
	if err != nil {
		t.Fatal(err)
	}
	rel.proof = &assetProof{
		archiveSHA256: fmt.Sprintf("%x", sha256.Sum256(archive)),
		binarySHA256:  fmt.Sprintf("%x", sha256.Sum256([]byte("native"))),
	}
	fake.hits.Store(0)
	binary, err := rel.ensure(fake.server.Client())
	if err != nil {
		t.Fatal(err)
	}
	if _, err := rel.ensure(fake.server.Client()); err != nil {
		t.Fatal(err)
	}
	if fake.hits.Load() != 1 {
		t.Fatalf("%d HTTP requests; want archive only, then a warm hit", fake.hits.Load())
	}
	invocation, err := os.ReadFile(calls)
	if err != nil {
		t.Fatal(err)
	}
	for _, flag := range []string{"--bundle", "--custom-trusted-root", "--source-digest " + bundledSource, "--signer-digest " + bundledSource, "--deny-self-hosted-runners"} {
		if !strings.Contains(string(invocation), flag) {
			t.Fatalf("missing %s: %s", flag, invocation)
		}
	}
	if err := os.WriteFile(binary, []byte("tampered"), 0o755); err != nil {
		t.Fatal(err)
	}
	if _, err := rel.ensure(fake.server.Client()); err == nil || !strings.Contains(err.Error(), "cached binary does not match") {
		t.Fatalf("corrupt warm cache: %v", err)
	}
	if fake.hits.Load() != 1 {
		t.Fatal("a corrupt cache must fail before any download")
	}
}

func TestReviewedInstallRequiresVerification(t *testing.T) {
	for _, mode := range []string{"missing", "noauth", "fail"} {
		t.Run(mode, func(t *testing.T) {
			rel, fake, _ := ghRelease(t, mode)
			archive, err := fetch(fake.server.Client(), rel.base+"/"+rel.archive())
			if err != nil {
				t.Fatal(err)
			}
			rel.proof = &assetProof{archiveSHA256: fmt.Sprintf("%x", sha256.Sum256(archive))}
			if mode == "missing" {
				rel.gh = ""
			}
			if _, err := rel.ensure(fake.server.Client()); err == nil {
				t.Fatal("installed without successful provenance verification")
			}
			if _, err := os.Stat(rel.binary()); !os.IsNotExist(err) {
				t.Fatal("failed verification installed a binary")
			}
		})
	}
}

func TestReviewedReleaseArchivePinsRejectMutableChecksums(t *testing.T) {
	rel, fake, _ := ghRelease(t, "ok")
	rel.proof = &assetProof{archiveSHA256: strings.Repeat("0", 64)}
	if _, err := rel.ensure(fake.server.Client()); err == nil || !strings.Contains(err.Error(), "does not match expected checksum") {
		t.Fatalf("unreviewed archive accepted: %v", err)
	}
	if fake.hits.Load() != 1 {
		t.Fatalf("downloaded mutable SHA256SUMS: %d HTTP requests", fake.hits.Load())
	}
}

func TestReviewedInstallRejectsUnexpectedExtractedBinary(t *testing.T) {
	rel, fake, _ := ghRelease(t, "ok")
	archive, err := fetch(fake.server.Client(), rel.base+"/"+rel.archive())
	if err != nil {
		t.Fatal(err)
	}
	rel.proof = &assetProof{
		archiveSHA256: fmt.Sprintf("%x", sha256.Sum256(archive)),
		binarySHA256:  strings.Repeat("0", 64),
	}
	if _, err := rel.ensure(fake.server.Client()); err == nil || !strings.Contains(err.Error(), "extracted binary does not match") {
		t.Fatalf("wrong native member accepted: %v", err)
	}
	if _, err := os.Stat(rel.binary()); !os.IsNotExist(err) {
		t.Fatal("installed an unreviewed native member")
	}
}

// Uses already-downloaded published archives; the actual verifier has no network.
// Set RSHELLCHECK_RELEASE_ARCHIVES to exercise the complete release locally.
func TestPublishedReleaseOfflineVerification(t *testing.T) {
	dir := os.Getenv("RSHELLCHECK_RELEASE_ARCHIVES")
	if dir == "" {
		t.Skip("set RSHELLCHECK_RELEASE_ARCHIVES to the published archive directory")
	}
	gh, err := exec.LookPath("gh")
	if err != nil {
		t.Fatal(err)
	}
	t.Setenv("GH_TOKEN", "")
	t.Setenv("GITHUB_TOKEN", "")
	t.Setenv("GH_CONFIG_DIR", t.TempDir())
	for _, key := range []string{"HTTP_PROXY", "HTTPS_PROXY", "ALL_PROXY"} {
		t.Setenv(key, "http://127.0.0.1:1")
	}
	t.Setenv("NO_PROXY", "")
	for platform := range targets {
		t.Run(platform, func(t *testing.T) {
			goos, goarch, _ := strings.Cut(platform, "/")
			rel, err := resolve("v"+bundledVersion, goos, goarch, releaseBase, t.TempDir())
			if err != nil {
				t.Fatal(err)
			}
			rel.gh = gh
			data, err := os.ReadFile(filepath.Join(dir, rel.archive()))
			if err != nil {
				t.Fatal(err)
			}
			fake := serve(t, map[string][]byte{"/" + rel.archive(): data})
			rel.base = fake.server.URL
			client := &http.Client{Transport: &http.Transport{Proxy: nil}}
			defer client.CloseIdleConnections()
			binary, err := rel.ensure(client)
			if err != nil {
				t.Fatal(err)
			}
			if _, err := rel.ensure(client); err != nil || fake.hits.Load() != 1 {
				t.Fatalf("warm verification: %v, %d requests", err, fake.hits.Load())
			}
			if goos == runtime.GOOS && goarch == runtime.GOARCH {
				var output bytes.Buffer
				if status := execute(binary, []string{"--version"}, strings.NewReader(""), &output, io.Discard); status != 0 || !strings.Contains(output.String(), bundledVersion) {
					t.Fatalf("native execution: %d %q", status, output.String())
				}
			}
			if err := os.WriteFile(binary, []byte("corrupt"), 0o755); err != nil {
				t.Fatal(err)
			}
			if _, err := rel.ensure(client); err == nil {
				t.Fatal("corrupt real cached binary accepted")
			}
			if err := rel.verify(append(data, byte(0))); err == nil {
				t.Fatal("real attestation accepted an altered archive")
			}
			if goos == runtime.GOOS && goarch == runtime.GOARCH {
				verifyOfflinePolicyFailures(t, gh, filepath.Join(dir, rel.archive()))
			}
		})
	}
}

func verifyOfflinePolicyFailures(t *testing.T, gh, archive string) {
	t.Helper()
	for _, failure := range []string{"wrong-source", "bad-root", "bad-signature"} {
		t.Run(failure, func(t *testing.T) {
			dir := t.TempDir()
			args, err := offlineArguments([]string{"attestation", "verify", archive, "--repo", repository,
				"--signer-workflow", signerWorkflow, "--source-ref", "refs/tags/" + tagPrefix + bundledVersion}, dir)
			if err != nil {
				t.Fatal(err)
			}
			switch failure {
			case "wrong-source":
				for i, arg := range args {
					if arg == "--source-digest" {
						args[i+1] = strings.Repeat("0", 40)
					}
				}
			case "bad-root":
				if err := os.WriteFile(filepath.Join(dir, "trusted-root.jsonl"), []byte("{}\n"), 0o600); err != nil {
					t.Fatal(err)
				}
			case "bad-signature":
				var bundle struct {
					Envelope struct {
						Signatures []struct {
							Signature string `json:"sig"`
						} `json:"signatures"`
					} `json:"dsseEnvelope"`
				}
				if err := json.Unmarshal(provenanceBundle, &bundle); err != nil {
					t.Fatal(err)
				}
				if len(bundle.Envelope.Signatures) != 1 {
					t.Fatal("expected one release signature")
				}
				signature := bundle.Envelope.Signatures[0].Signature
				replacement := "A" + signature[1:]
				if replacement == signature {
					replacement = "B" + signature[1:]
				}
				broken := bytes.Replace(provenanceBundle, []byte(signature), []byte(replacement), 1)
				if err := os.WriteFile(filepath.Join(dir, "provenance.sigstore.json"), broken, 0o600); err != nil {
					t.Fatal(err)
				}
			}
			if output, err := exec.Command(gh, args...).CombinedOutput(); err == nil {
				t.Fatalf("accepted %s: %s", failure, output)
			}
		})
	}
}
