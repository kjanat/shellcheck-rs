package main

import (
	"crypto/sha256"
	_ "embed"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"path/filepath"
)

const (
	bundledVersion = "0.11.0"
	bundledSource  = "e0f0d77845e0bccfccf7ef2e46b50e968e534328"
)

//go:embed proofs/0.11.0/provenance.sigstore.json
var provenanceBundle []byte

//go:embed proofs/0.11.0/trusted-root.jsonl
var trustedRoot []byte

type assetProof struct {
	archiveSHA256 string
	binarySHA256  string
}

func (r *release) cachedBinary() (bool, error) {
	info, err := os.Lstat(r.binary())
	if os.IsNotExist(err) {
		return false, nil
	}
	if err != nil {
		return false, err
	}
	if r.proof == nil {
		return true, nil
	}
	if !info.Mode().IsRegular() || info.Size() > maxArchive {
		return false, fmt.Errorf("%s: cached binary is not a bounded regular file", r.binary())
	}
	file, err := os.Open(r.binary())
	if err != nil {
		return false, err
	}
	defer file.Close()
	digest := sha256.New()
	if _, err := io.Copy(digest, io.LimitReader(file, maxArchive+1)); err != nil {
		return false, err
	}
	if hex.EncodeToString(digest.Sum(nil)) != r.proof.binarySHA256 {
		return false, fmt.Errorf("%s: cached binary does not match reviewed checksum; remove it and retry", r.binary())
	}
	return true, nil
}

func offlineArguments(args []string, dir string) ([]string, error) {
	bundle := filepath.Join(dir, "provenance.sigstore.json")
	root := filepath.Join(dir, "trusted-root.jsonl")
	for path, contents := range map[string][]byte{bundle: provenanceBundle, root: trustedRoot} {
		if err := os.WriteFile(path, contents, 0o600); err != nil {
			return nil, err
		}
	}
	return append(args,
		"--bundle", bundle,
		"--custom-trusted-root", root,
		"--source-digest", bundledSource,
		"--signer-digest", bundledSource,
		"--predicate-type", "https://slsa.dev/provenance/v1",
		"--deny-self-hosted-runners"), nil
}
