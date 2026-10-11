package shellcheck

import (
	"context"
	"encoding/json"
	"os"
	"reflect"
	"testing"
)

func TestNativeParity(t *testing.T) {
	wasm, err := os.ReadFile("../../../target/wasm32-unknown-unknown/release/shellcheck_wasm.wasm")
	if err != nil {
		t.Fatal(err)
	}
	raw, err := os.ReadFile("../../../.cache/wasm-parity.json")
	if err != nil {
		t.Fatal(err)
	}
	var fixtures []struct {
		Request json.RawMessage
		Result  map[string]any
	}
	if err = json.Unmarshal(raw, &fixtures); err != nil {
		t.Fatal(err)
	}
	ctx := context.Background()
	c, err := New(ctx, wasm)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close(ctx)
	for i, f := range fixtures {
		raw, err := c.Check(ctx, f.Request)
		if msg, ok := f.Result["error"]; ok {
			if err == nil || err.Error() != msg {
				t.Fatalf("case %d: %v, want %v", i, err, msg)
			}
			continue
		}
		if err != nil {
			t.Fatalf("case %d: %v", i, err)
		}
		var result map[string]any
		if err = json.Unmarshal(raw, &result); err != nil {
			t.Fatal(err)
		}
		if !reflect.DeepEqual(result, f.Result) {
			t.Fatalf("case %d differs from native", i)
		}
	}
	for i := 0; i < 100; i++ {
		if _, err = c.Check(ctx, fixtures[1].Request); err != nil {
			t.Fatal(err)
		}
	}
	canceled, cancel := context.WithCancel(ctx)
	cancel()
	if _, err = c.Check(canceled, fixtures[0].Request); err == nil {
		t.Fatal("canceled check succeeded")
	}
	if _, err = c.Check(ctx, fixtures[0].Request); err == nil {
		t.Fatal("closed instance reused")
	}
}
