// Package shellcheck runs the import-free ShellCheck core using wazero (no CGO).
package shellcheck

import (
	"context"
	"encoding/json"
	"fmt"
	"sync"

	"github.com/tetratelabs/wazero"
	"github.com/tetratelabs/wazero/api"
)

// Checker serializes calls to a reusable module instance. Create a pool for concurrency.
type Checker struct {
	mu      sync.Mutex
	runtime wazero.Runtime
	module  api.Module
	closed  bool
}

// New compiles the module. A canceled Check context permanently closes its instance.
func New(ctx context.Context, wasm []byte) (*Checker, error) {
	r := wazero.NewRuntimeWithConfig(ctx, wazero.NewRuntimeConfig().WithCloseOnContextDone(true))
	m, err := r.Instantiate(ctx, wasm)
	if err != nil {
		r.Close(ctx)
		return nil, err
	}
	c := &Checker{runtime: r, module: m}
	for _, name := range []string{"sc_abi_version", "sc_prepare", "sc_check", "sc_output_len"} {
		if m.ExportedFunction(name) == nil {
			c.Close(ctx)
			return nil, fmt.Errorf("missing export %s", name)
		}
	}
	version, err := m.ExportedFunction("sc_abi_version").Call(ctx)
	if err != nil || len(version) != 1 || version[0] != 1 || m.Memory() == nil {
		c.Close(ctx)
		return nil, fmt.Errorf("unsupported ShellCheck ABI: %v", err)
	}
	return c, nil
}

// Check accepts the shared JSON request and returns diagnostics, fixes, dataflowError and sources.
// Request validation errors leave the instance usable; runtime traps invalidate it.
func (c *Checker) Check(ctx context.Context, request json.RawMessage) (json.RawMessage, error) {
	c.mu.Lock()
	defer c.mu.Unlock()
	if c.closed {
		return nil, fmt.Errorf("checker closed; create a new instance")
	}
	if len(request) > 16*1024*1024 {
		return nil, fmt.Errorf("request exceeds 16 MiB")
	}
	run := func() (json.RawMessage, error) {
		ptr, err := c.module.ExportedFunction("sc_prepare").Call(ctx, uint64(len(request)))
		if err != nil {
			return nil, err
		}
		if ptr[0] == 0 || !c.module.Memory().Write(uint32(ptr[0]), request) {
			return nil, fmt.Errorf("request rejected")
		}
		ptr, err = c.module.ExportedFunction("sc_check").Call(ctx)
		if err != nil {
			return nil, err
		}
		size, err := c.module.ExportedFunction("sc_output_len").Call(ctx)
		if err != nil {
			return nil, err
		}
		bytes, ok := c.module.Memory().Read(uint32(ptr[0]), uint32(size[0]))
		if !ok {
			return nil, fmt.Errorf("invalid output range")
		}
		return append(json.RawMessage(nil), bytes...), nil
	}
	result, err := run()
	if err != nil {
		c.closed = true
		c.runtime.Close(context.Background())
		return nil, err
	}
	var envelope struct {
		Error string `json:"error"`
	}
	if err = json.Unmarshal(result, &envelope); err != nil {
		return nil, err
	}
	if envelope.Error != "" {
		return nil, fmt.Errorf("%s", envelope.Error)
	}
	return result, nil
}

// Close releases runtime resources.
func (c *Checker) Close(ctx context.Context) error {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.closed = true
	return c.runtime.Close(ctx)
}
