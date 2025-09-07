#!/bin/bash

# Comprehensive script to create hardlinks for TACAS25 benchmarks
# This script can be run manually or called from git hooks

echo "Creating hardlinks for TACAS25 benchmarks..."

# Get the script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

# Function to create hardlinks for a specific benchmark
create_hardlinks_for_benchmark() {
    local benchmark_name=$1
    local source_dir="$REPO_ROOT/benchmarks/all/$benchmark_name"
    local target_dir="$REPO_ROOT/benchmarks/TACAS25/$benchmark_name"

    # Check if source directory exists
    if [ ! -d "$source_dir" ]; then
        echo "Warning: Source directory $source_dir does not exist"
        return
    fi

    # Create target directory if it doesn't exist
    mkdir -p "$target_dir"

    # Get the list of directories that should be linked
    # This is based on the existing TACAS25 structure
    case $benchmark_name in
        "GroverWhile")
            # Link specific directories: 03, 10, 20, 30, 40, 50
            for dir in "03" "10" "20" "30" "40" "50"; do
                if [ -d "$source_dir/$dir" ]; then
                    echo "Linking $benchmark_name/$dir"
                    cp -rlf "$source_dir/$dir" "$target_dir/" 2>/dev/null || true
                fi
            done
            ;;
        "RUS")
            # For these benchmarks, link all files from the source directory
            echo "Linking all files from $benchmark_name"
            cp -rlf "$source_dir"/* "$target_dir/" 2>/dev/null || true
            ;;
        *)
            # For any other benchmarks, try to link all directories
            echo "Linking all directories from $benchmark_name"
            for item in "$source_dir"/*; do
                if [ -d "$item" ]; then
                    local dir_name=$(basename "$item")
                    cp -rl "$item" "$target_dir/"
                fi
            done
            ;;
    esac
}

# List of benchmark directories to process
benchmarks=("GroverWhile" "RUS")

# Process each benchmark
for benchmark in "${benchmarks[@]}"; do
    echo "Processing $benchmark..."
    create_hardlinks_for_benchmark "$benchmark"
done

echo "Hardlink creation completed!"