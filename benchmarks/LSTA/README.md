# LSTA Benchmarks

This directory contains a subset of benchmarks from `benchmarks/all/` that are specifically used for LSTA experiments.

## Automatic Hardlink Creation

The repository includes git hooks that automatically create hardlinks from `benchmarks/all/` to `benchmarks/LSTA/` when:

1. **git pull** is performed (post-merge hook)
2. **git clone** is performed (post-checkout hook)
3. **git checkout** is performed (post-checkout hook)

## Manual Hardlink Creation

You can also manually create hardlinks by running:

```bash
cd benchmarks/LSTA
./create_hardlinks.sh
```

## Benchmark Structure

The following benchmarks are automatically linked:

### BV
- Links directories: `95`, `96`, `97`, `98`, `99`
- Source: `benchmarks/all/BV/`

### Grover
- Links directories: `12`, `14`, `16`, `18`, `20`
- Source: `benchmarks/all/Grover/`

### MOGrover
- Links directories: `06`, `07`, `08`, `09`, `10`
- Source: `benchmarks/all/MOGrover/`

### MCToffoli
- Links directories: `08`, `10`, `12`, `14`, `16`
- Source: `benchmarks/all/MCToffoli/`

### H2
- Links directories: `012`, `013`, `064`, `128`, `256`
- Source: `benchmarks/all/H2/`

### HXH
- Links directories: `10`, `11`, `12`, `13`, `99`
- Source: `benchmarks/all/HXH/`

### MOBV_reorder
- Links directories: `09`, `10`, `11`, `12`, `13`
- Source: `benchmarks/all/MOBV_reorder/`

### GHZzero
- Links directories: `064`, `128`, `256`, `384`, `512`
- Source: `benchmarks/all/GHZzero/`

### GHZall
- Links directories: `008`, `016`, `032`, `064`, `128`
- Source: `benchmarks/all/GHZall/`

### OEGrover
- Links directories: `02`, `18`, `50`, `75`, `100`
- Source: `benchmarks/all/OEGrover/`

## Git Hooks

The git hooks are located in `.git/hooks/`:
- `post-merge`: Runs after `git pull`
- `post-checkout`: Runs after `git clone` and `git checkout`

Both hooks use the same logic as the manual script to ensure consistency.

## Notes

- Hardlinks are created using `cp -rlf` to force overwrite existing files
- Error messages are suppressed to avoid cluttering the output
- The hooks will create target directories if they don't exist
- If a source directory doesn't exist, a warning is shown but the process continues
- Only essential files (`circuit.qasm`, `post.hsl`, `pre.hsl`) are linked, unnecessary files like `*.lsta`, `produce.py`, and `*.png` are excluded 