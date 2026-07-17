#!/bin/bash

# Configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AUTOQ_BIN="${AUTOQ_BIN:-${SCRIPT_DIR}/../../build/cli/autoq}"
BENCHMARK_BASE="${SCRIPT_DIR}/../../benchmarks/TACAS25/RUS"
FIGURES=("Figure7" "Figure8" "Figure9" "Figure10a" "Figure10b" "Figure10c")

OUTPUT_FILE="table1.csv"

# Write CSV header
echo "program,qubits,gates,result,time,memory" > "$OUTPUT_FILE"

echo "Starting benchmarks execution and generating CSV..."
echo "==================================================="

for FIG in "${FIGURES[@]}"; do
    PRE="${BENCHMARK_BASE}/${FIG}/pre_.lsta"
    POST="${BENCHMARK_BASE}/${FIG}/post_.lsta"
    CIRCUIT="${BENCHMARK_BASE}/${FIG}/circuit_.qasm"

    if [[ -f "$PRE" && -f "$POST" ]]; then
        # Run the command and extract the last meaningful line
        # Convert FigureX to 𝑉X format
        if [[ "$FIG" =~ ^Figure([0-9]+)([a-z]?)$ ]]; then
            FIG_NUM="${BASH_REMATCH[1]}"
            FIG_SUFFIX="${BASH_REMATCH[2]}"
            TARGET_FIG="𝑉${FIG_NUM}${FIG_SUFFIX}"
        else
            TARGET_FIG="𝑉${FIG}"
        fi
        
        OUTPUT=$("$AUTOQ_BIN" ver "$PRE" "$CIRCUIT" "$POST" 2>/dev/null | tail -n 1)
        
        # Parse the output using sed
        # Format: "The quantum program has [2] qubits and [30] gates. The verification process [OK] in [0.0s] with [27MB] memory usage."
        PARSED=$(echo "$OUTPUT" | sed -n 's/.*has \[\([0-9]*\)\] qubits and \[\([0-9]*\)\] gates.*process \[\([^]]*\)\] in \[\([^]]*\)\] with \[\([^]]*\)\] memory.*/\1,\2,\3,\4,\5/p')
        
        if [ -n "$PARSED" ]; then
            IFS=',' read -r qubits gates result time memory <<< "$PARSED"
            
            # Write to CSV
            echo "${TARGET_FIG},${qubits},${gates},${result},${time},${memory}" >> "$OUTPUT_FILE"
            echo "Processed: ${TARGET_FIG}"
        else
            echo "Error parsing output for ${FIG}: $OUTPUT"
            echo "${TARGET_FIG},,,,," >> "$OUTPUT_FILE"
        fi
        
            # Check for corrected version
        POST_CORRECTED="${BENCHMARK_BASE}/${FIG}/post_corrected.lsta"
        if [[ -f "$POST_CORRECTED" ]]; then
            OUTPUT=$("$AUTOQ_BIN" ver "$PRE" "$CIRCUIT" "$POST_CORRECTED" 2>/dev/null | tail -n 1)
            TARGET_FIG_CORRECTED="𝑉${FIG_NUM}${FIG_SUFFIX}_corrected"
            
            # Parse the output using sed
            PARSED=$(echo "$OUTPUT" | sed -n 's/.*has \[\([0-9]*\)\] qubits and \[\([0-9]*\)\] gates.*process \[\([^]]*\)\] in \[\([^]]*\)\] with \[\([^]]*\)\] memory.*/\1,\2,\3,\4,\5/p')
            
            if [ -n "$PARSED" ]; then
                IFS=',' read -r qubits gates result time memory <<< "$PARSED"
                
                # Write to CSV
                echo "${TARGET_FIG_CORRECTED},${qubits},${gates},${result},${time},${memory}" >> "$OUTPUT_FILE"
                echo "Processed: ${TARGET_FIG_CORRECTED}"
            else
                echo "Error parsing output for ${FIG}_corrected: $OUTPUT"
                echo "${TARGET_FIG_CORRECTED},,,,," >> "$OUTPUT_FILE"
            fi
        fi
    else
        echo "${FIG} => Error: Missing hls files"
        echo "𝑉${FIG},,,,," >> "$OUTPUT_FILE"
    fi
done

echo "CSV generation completed. Output saved to $OUTPUT_FILE"
echo "======================================================"
cat "$OUTPUT_FILE"