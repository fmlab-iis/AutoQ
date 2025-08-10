# TACAS25 Benchmarks

This directory contains a subset of benchmarks from `benchmarks/all/` that are specifically used for TACAS25 experiments.

## Automatic Hardlink Creation

The repository includes git hooks that automatically create hardlinks from `benchmarks/all/` to `benchmarks/TACAS25/` when:

1. **git pull** is performed (post-merge hook)
2. **git clone** is performed (post-checkout hook)
3. **git checkout** is performed (post-checkout hook)

## Manual Hardlink Creation

You can also manually create hardlinks by running:

```bash
cd benchmarks/TACAS25
./create_hardlinks.sh
```

## Benchmark Structure

The following benchmarks are automatically linked:

### GroverWhile
- Links directories: `03`, `10`, `20`, `30`, `40`, `50`
- Source: `benchmarks/all/GroverWhile/`

### File-based Benchmarks
The following benchmarks link all files from their source directories:
- `RUS`

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