#!/bin/bash

# Comprehensive script to create hardlinks for CAV23 benchmarks
# This script can be run manually or called from git hooks

echo "Creating hardlinks for CAV23 benchmarks..."

# Get the script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

# Function to create hardlinks for a specific benchmark
create_hardlinks_for_benchmark() {
    local benchmark_name=$1
    local source_dir="$REPO_ROOT/benchmarks/all/$benchmark_name"
    local target_dir="$REPO_ROOT/benchmarks/CAV23/$benchmark_name"
    
    # Check if source directory exists
    if [ ! -d "$source_dir" ]; then
        echo "Warning: Source directory $source_dir does not exist"
        return
    fi
    
    # Create target directory if it doesn't exist
    mkdir -p "$target_dir"
    
    # Get the list of directories that should be linked
    # This is based on the existing CAV23 structure
    case $benchmark_name in
        "BVSym")
            # Link specific directories: 01, 99, 999
            for dir in "01" "99" "999"; do
                if [ -d "$source_dir/$dir" ]; then
                    echo "Linking $benchmark_name/$dir"
                    cp -rlf "$source_dir/$dir" "$target_dir/" 2>/dev/null || true
                fi
            done
            ;;
        "OEGrover")
            # Link specific directories: 02, 18, 50, 75, 100
            for dir in "02" "18" "50" "75" "100"; do
                if [ -d "$source_dir/$dir" ]; then
                    echo "Linking $benchmark_name/$dir"
                    cp -rlf "$source_dir/$dir" "$target_dir/" 2>/dev/null || true
                fi
            done
            ;;
        "GroverSym")
            # Link specific directories: 03, 16, 18, 20
            for dir in "03" "16" "18" "20"; do
                if [ -d "$source_dir/$dir" ]; then
                    echo "Linking $benchmark_name/$dir"
                    cp -rlf "$source_dir/$dir" "$target_dir/" 2>/dev/null || true
                fi
            done
            ;;
        "MOGroverSym")
            # Link specific directories: 03, 08, 09
            for dir in "03" "08" "09"; do
                if [ -d "$source_dir/$dir" ]; then
                    echo "Linking $benchmark_name/$dir"
                    cp -rlf "$source_dir/$dir" "$target_dir/" 2>/dev/null || true
                fi
            done
            ;;
        "H2BugSym"|"H2Sym"|"BVBugSym")
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
benchmarks=("BVSym" "OEGrover" "H2BugSym" "H2Sym" "BVBugSym" "GroverSym" "MOGroverSym")

# Process each benchmark
for benchmark in "${benchmarks[@]}"; do
    echo "Processing $benchmark..."
    create_hardlinks_for_benchmark "$benchmark"
done

echo "Hardlink creation completed!"