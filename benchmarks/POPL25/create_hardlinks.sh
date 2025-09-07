#!/bin/bash

# Comprehensive script to create hardlinks for POPL25 benchmarks
# This script can be run manually or called from git hooks

echo "Creating hardlinks for POPL25 benchmarks..."

# Get the script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

# Function to create hardlinks for a specific benchmark
create_hardlinks_for_benchmark() {
    local benchmark_name=$1
    local source_dir="$REPO_ROOT/benchmarks/all/$benchmark_name"
    local target_dir="$REPO_ROOT/benchmarks/POPL25/$benchmark_name"

    # Check if source directory exists
    if [ ! -d "$source_dir" ]; then
        echo "Warning: Source directory $source_dir does not exist"
        return
    fi

    # Create target directory if it doesn't exist
    mkdir -p "$target_dir"

    # Get the list of directories that should be linked
    # This is based on the existing POPL25 structure
    case $benchmark_name in
        "BV")
            # Link specific directories: 95, 96, 97, 98, 99
            for dir in "95" "96" "97" "98" "99"; do
                if [ -d "$source_dir/$dir" ]; then
                    echo "Linking $benchmark_name/$dir"
                    cp -rlf "$source_dir/$dir" "$target_dir/" 2>/dev/null || true
                fi
            done
            ;;
        "Grover")
            # Link specific directories: 12, 14, 16, 18, 20
            for dir in "12" "14" "16" "18" "20"; do
                if [ -d "$source_dir/$dir" ]; then
                    echo "Linking $benchmark_name/$dir"
                    cp -rlf "$source_dir/$dir" "$target_dir/" 2>/dev/null || true
                fi
            done
            ;;
        "MOGrover")
            # Link specific directories: 06, 07, 08, 09, 10
            for dir in "06" "07" "08" "09" "10"; do
                if [ -d "$source_dir/$dir" ]; then
                    echo "Linking $benchmark_name/$dir"
                    cp -rlf "$source_dir/$dir" "$target_dir/" 2>/dev/null || true
                fi
            done
            ;;
        "MCToffoli")
            # Link specific directories: 08, 10, 12, 14, 16
            for dir in "08" "10" "12" "14" "16"; do
                if [ -d "$source_dir/$dir" ]; then
                    echo "Linking $benchmark_name/$dir"
                    cp -rlf "$source_dir/$dir" "$target_dir/" 2>/dev/null || true
                fi
            done
            ;;
        "H2")
            # Link specific directories: 012, 013, 064, 128, 256
            for dir in "012" "013" "064" "128" "256"; do
                if [ -d "$source_dir/$dir" ]; then
                    echo "Linking $benchmark_name/$dir"
                    cp -rlf "$source_dir/$dir" "$target_dir/" 2>/dev/null || true
                fi
            done
            ;;
        "HXH")
            # Link specific directories: 10, 11, 12, 13, 99
            for dir in "10" "11" "12" "13" "99"; do
                if [ -d "$source_dir/$dir" ]; then
                    echo "Linking $benchmark_name/$dir"
                    cp -rlf "$source_dir/$dir" "$target_dir/" 2>/dev/null || true
                fi
            done
            ;;
        "MOBV_reorder")
            # Link specific directories: 09, 10, 11, 12, 13
            for dir in "09" "10" "11" "12" "13"; do
                if [ -d "$source_dir/$dir" ]; then
                    echo "Linking $benchmark_name/$dir"
                    cp -rlf "$source_dir/$dir" "$target_dir/" 2>/dev/null || true
                fi
            done
            ;;
        "GHZzero")
            # Link specific directories: 064, 128, 256, 384, 512
            for dir in "064" "128" "256" "384" "512"; do
                if [ -d "$source_dir/$dir" ]; then
                    echo "Linking $benchmark_name/$dir"
                    cp -rlf "$source_dir/$dir" "$target_dir/" 2>/dev/null || true
                fi
            done
            ;;
        "GHZall")
            # Link specific directories: 008, 016, 032, 064, 128
            for dir in "008" "016" "032" "064" "128"; do
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
        *)
            # For any other benchmarks, try to link all directories
            echo "Linking all directories from $benchmark_name"
            for item in "$source_dir"/*; do
                if [ -d "$item" ]; then
                    local dir_name=$(basename "$item")
                    cp -rlf "$item" "$target_dir/"
                fi
            done
            ;;
    esac
}

# List of benchmark directories to process
benchmarks=("BV" "Grover" "MOGrover" "MCToffoli" "H2" "HXH" "MOBV_reorder" "GHZzero" "GHZall" "OEGrover")

# Process each benchmark
for benchmark in "${benchmarks[@]}"; do
    echo "Processing $benchmark..."
    create_hardlinks_for_benchmark "$benchmark"
done

echo "Hardlink creation completed!"