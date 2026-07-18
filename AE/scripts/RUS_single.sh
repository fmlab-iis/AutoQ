#!/bin/bash

# Configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AUTOQ_BIN="${AUTOQ_BIN:-${SCRIPT_DIR}/../../build/cli/autoq}"
BENCHMARK_BASE="${SCRIPT_DIR}/../../benchmarks/OOPSLA26/RUS"
FIGURES=("Figure7" "Figure8" "Figure9" "Figure10a" "Figure10b" "Figure10c")

echo "Starting Table 1 benchmarks execution..."
echo "========================================="

for FIG in "${FIGURES[@]}"; do
    PRE="${BENCHMARK_BASE}/${FIG}/pre_.lsta"
    POST="${BENCHMARK_BASE}/${FIG}/post_.lsta"
    CIRCUIT="${BENCHMARK_BASE}/${FIG}/circuit_.qasm"
    
    if [[ -f "$PRE" && -f "$POST" ]]; then
        # Run the command and extract the last meaningful line
        # echo "$AUTOQ_BIN" ver "$PRE" "$CIRCUIT" "$POST"
        # Convert FigureX to 𝑉X format
        if [[ "$FIG" =~ ^Figure([0-9]+[a-z]?)$ ]]; then
            TARGET_FIG="𝑉${BASH_REMATCH[1]}"
        else
            TARGET_FIG="𝑉${FIG}"
        fi

        # Figures with a post_corrected.lsta are the deliberately-buggy
        # variants: label the buggy run "_bug" and the fixed run "_fix".
        POST_CORRECTED="${BENCHMARK_BASE}/${FIG}/post_corrected.lsta"
        if [[ -f "$POST_CORRECTED" ]]; then
            BASE_LABEL="${TARGET_FIG}_bug"
        else
            BASE_LABEL="${TARGET_FIG}"
        fi

        RESULT=$("$AUTOQ_BIN" ver "$PRE" "$CIRCUIT" "$POST" 2>/dev/null | tail -n 1)
        printf "%-18s => %s\n" "${BASE_LABEL}" "${RESULT}"
        if [[ -f "$POST_CORRECTED" ]]; then
            RESULT=$("$AUTOQ_BIN" ver "$PRE" "$CIRCUIT" "$POST_CORRECTED" 2>/dev/null | tail -n 1)
            printf "%-18s => %s\n" "${TARGET_FIG}_fix" "${RESULT}"
        fi
    else
        echo "${FIG} => Error: Missing hls files"
    fi
done

echo "Benchmarks execution completed."
