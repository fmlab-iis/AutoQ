# CAV23 Benchmarks

This directory contains a subset of benchmarks from `benchmarks/all/` that are specifically used for CAV23 experiments.

## Automatic Hardlink Creation

The repository includes git hooks that automatically create hardlinks from `benchmarks/all/` to `benchmarks/CAV23/` when:

1. **git pull** is performed (post-merge hook)
2. **git clone** is performed (post-checkout hook)
3. **git checkout** is performed (post-checkout hook)

## Manual Hardlink Creation

You can also manually create hardlinks by running:

```bash
cd benchmarks/CAV23
./create_hardlinks.sh
```

## Benchmark Structure

The following benchmarks are automatically linked:

### BVSym
- Links directories: `01`, `99`, `999`
- Source: `benchmarks/all/BVSym/`

### OEGrover
- Links directories: `02`, `18`, `50`, `75`, `100`
- Source: `benchmarks/all/OEGrover/`

### GroverSym
- Links directories: `03`, `16`, `18`, `20`
- Source: `benchmarks/all/GroverSym/`

### MOGroverSym
- Links directories: `03`, `08`, `09`
- Source: `benchmarks/all/MOGroverSym/`

### File-based Benchmarks
The following benchmarks link all files from their source directories:
- `H2BugSym`
- `H2Sym`
- `BVBugSym`

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