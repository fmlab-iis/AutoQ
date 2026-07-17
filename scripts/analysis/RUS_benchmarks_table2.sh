#!/bin/bash

# Configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AUTOQ_BIN="${AUTOQ_BIN:-${SCRIPT_DIR}/../../build/cli/autoq}"
BENCHMARK_BASE="${SCRIPT_DIR}/../../benchmarks/TACAS25/RUS"

OUTPUT_FILE="table2.csv"

# Write CSV header
echo "program,qubits,gates,result,time,memory" > "$OUTPUT_FILE"

echo "Starting ex benchmarks execution and generating CSV..."
echo "======================================================"

# Find all ex directories (including _old directories) and sort them
# Extract numeric parts for proper sorting: Figure7_ex7, Figure7_ex8, Figure8_ex7, etc.
declare -A dir_order
declare -a dir_names

while IFS= read -r -d '' EX_DIR; do
    EX_DIR=$(basename "$EX_DIR")
    
    # Skip nested directories (color1Ok, cut, etc.)
    if [[ "$EX_DIR" == *"color"* ]] || [[ "$EX_DIR" == *"cut"* ]] || [[ "$EX_DIR" == *"tag"* ]]; then
        continue
    fi
    
    # Extract main figure number and ex number for sorting
    # Pattern: Figure<num>_ex<num> or Figure<num>_ex<num>_old
    if [[ "$EX_DIR" =~ ^Figure([0-9]+)_ex([0-9]+[a-z]?)(_old)?$ ]]; then
        main_num="${BASH_REMATCH[1]}"
        ex_num="${BASH_REMATCH[2]}"
        is_old="${BASH_REMATCH[3]}"
        
        # Convert ex_num to sortable format (handle alphanumeric like 10a, 10b, 10c)
        # For numeric-only, pad with zeros
        if [[ "$ex_num" =~ ^[0-9]+$ ]]; then
            ex_sort=$(printf "%03d" "$ex_num")
        else
            # For alphanumeric like 10a, 10b, 10c
            num_part="${ex_num%%[a-z]*}"
            alpha_part="${ex_num##*[0-9]}"
            ex_sort=$(printf "%03d%s" "$num_part" "${alpha_part:- }")
        fi
        
        # Create sort key: main_num.ex_sort.is_old (old directories come after non-old)
        sort_key=$(printf "%03d.%s.%s" "$main_num" "$ex_sort" "${is_old:+1}")
        dir_order["$sort_key"]="$EX_DIR"
        dir_names+=("$sort_key")
    else
        # Fallback for unexpected patterns
        dir_order["$EX_DIR"]="$EX_DIR"
        dir_names+=("$EX_DIR")
    fi
done < <(find "${BENCHMARK_BASE}" -maxdepth 1 -type d -name "*ex*" -print0)

# Sort directory names by sort key
IFS=$'\n' sorted_keys=($(sort <<<"${dir_names[*]}"))
unset IFS

# Process directories in sorted order
for sort_key in "${sorted_keys[@]}"; do
    EX_DIR="${dir_order[$sort_key]}"
    
    DIR_PATH="${BENCHMARK_BASE}/${EX_DIR}"
    
    # Find pre file (usually pre.lsta)
    PRE_FILE="${DIR_PATH}/pre.lsta"
    
    # Find post file (pattern: post*.lsta)
    # There should be exactly one post*.lsta file in each directory
    POST_FILES=($(find "${DIR_PATH}" -maxdepth 1 -name "post*.lsta" -type f))
    if [ ${#POST_FILES[@]} -eq 0 ]; then
        echo "${EX_DIR} => Error: No post*.lsta file found"
        # Convert name for CSV
        if [[ "$EX_DIR" =~ ^Figure([0-9]+[a-z]?)_ex(.+)$ ]]; then
            FIG_NUM="${BASH_REMATCH[1]}"
            EX_PART="${BASH_REMATCH[2]}"
            TARGET_NAME="𝑉${FIG_NUM} ◦ 𝑉${EX_PART}"
        else
            TARGET_NAME="𝑉${EX_DIR}"
        fi
        echo "${TARGET_NAME},,,,," >> "$OUTPUT_FILE"
        continue
    fi
    POST_FILE="${POST_FILES[0]}"
    
    # Find circuit file - ONLY use circuit_lsta_*.qasm, report error if not found
    CIRCUIT_FILES=($(find "${DIR_PATH}" -maxdepth 1 -name "circuit_lsta_*.qasm" -type f))
    if [ ${#CIRCUIT_FILES[@]} -eq 0 ]; then
        echo "${EX_DIR} => Error: No circuit_lsta_*.qasm file found"
        # Convert name for CSV
        if [[ "$EX_DIR" =~ ^Figure([0-9]+[a-z]?)_ex(.+)$ ]]; then
            FIG_NUM="${BASH_REMATCH[1]}"
            EX_PART="${BASH_REMATCH[2]}"
            TARGET_NAME="𝑉${FIG_NUM} ◦ 𝑉${EX_PART}"
        else
            TARGET_NAME="𝑉${EX_DIR}"
        fi
        echo "${TARGET_NAME},,,,," >> "$OUTPUT_FILE"
        continue
    fi
    CIRCUIT_FILE="${CIRCUIT_FILES[0]}"
    
    if [[ -f "$PRE_FILE" && -f "$POST_FILE" && -f "$CIRCUIT_FILE" ]]; then
        # Run the command and extract the last meaningful line
        OUTPUT=$("$AUTOQ_BIN" ver "$PRE_FILE" "$CIRCUIT_FILE" "$POST_FILE" 2>/dev/null | tail -n 1)
        
        # Parse the output using sed
        # Format: "The quantum program has [2] qubits and [61] gates. The verification process [OK] in [0.0s] with [27MB] memory usage."
        PARSED=$(echo "$OUTPUT" | sed -n 's/.*has \[\([0-9]*\)\] qubits and \[\([0-9]*\)\] gates.*process \[\([^]]*\)\] in \[\([^]]*\)\] with \[\([^]]*\)\] memory.*/\1,\2,\3,\4,\5/p')
        
        if [ -n "$PARSED" ]; then
            IFS=',' read -r qubits gates result time memory <<< "$PARSED"
            
            # Convert ex directory name to 𝑉X ◦ 𝑉Y format
            if [[ "$EX_DIR" =~ ^Figure([0-9]+[a-z]?)_ex(.+)$ ]]; then
                FIG_NUM="${BASH_REMATCH[1]}"
                EX_PART="${BASH_REMATCH[2]}"
                TARGET_NAME="𝑉${FIG_NUM} ◦ 𝑉${EX_PART}"
            else
                TARGET_NAME="𝑉${EX_DIR}"
            fi
            
            echo "${TARGET_NAME},${qubits},${gates},${result},${time},${memory}" >> "$OUTPUT_FILE"
            echo "Processed: ${TARGET_NAME}"
        else
            echo "Error parsing output for ${EX_DIR}: $OUTPUT"
            # Still convert name even for errors
            if [[ "$EX_DIR" =~ ^Figure([0-9]+[a-z]?)_ex(.+)$ ]]; then
                FIG_NUM="${BASH_REMATCH[1]}"
                EX_PART="${BASH_REMATCH[2]}"
                TARGET_NAME="𝑉${FIG_NUM} ◦ 𝑉${EX_PART}"
            else
                TARGET_NAME="𝑉${EX_DIR}"
            fi
            echo "${TARGET_NAME},,,,," >> "$OUTPUT_FILE"
        fi
    else
        echo "${EX_DIR} => Error: Missing required files"
        # Still convert name even for errors
        if [[ "$EX_DIR" =~ ^Figure([0-9]+[a-z]?)_ex(.+)$ ]]; then
            FIG_NUM="${BASH_REMATCH[1]}"
            EX_PART="${BASH_REMATCH[2]}"
            TARGET_NAME="𝑉${FIG_NUM} ◦ 𝑉${EX_PART}"
        else
            TARGET_NAME="𝑉${EX_DIR}"
        fi
        echo "${TARGET_NAME},,,,," >> "$OUTPUT_FILE"
    fi
done

echo "CSV generation completed. Output saved to $OUTPUT_FILE"
echo "======================================================"
cat "$OUTPUT_FILE"