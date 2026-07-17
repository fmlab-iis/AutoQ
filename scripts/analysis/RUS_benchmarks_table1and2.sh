#!/bin/bash

# Configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUTPUT_FILE="${SCRIPT_DIR}/../../table3.csv"

echo "Starting combined CSV generation..."
echo "==================================="

# First, run table1.sh to generate table1.csv
if [ -f "${SCRIPT_DIR}/RUS_benchmarks_table1.sh" ]; then
    echo "Generating table1.csv..."
    bash "${SCRIPT_DIR}/RUS_benchmarks_table1.sh" > /dev/null 2>&1
else
    echo "Error: RUS_benchmarks_table1.sh not found"
    exit 1
fi

# Then, run table2.sh to generate table2.csv
if [ -f "${SCRIPT_DIR}/RUS_benchmarks_table2.sh" ]; then
    echo "Generating table2.csv..."
    bash "${SCRIPT_DIR}/RUS_benchmarks_table2.sh" > /dev/null 2>&1
else
    echo "Error: RUS_benchmarks_table2.sh not found"
    exit 1
fi

# Check if both CSV files exist
TABLE1="${SCRIPT_DIR}/../../table1.csv"
TABLE2="${SCRIPT_DIR}/../../table2.csv"

if [ ! -f "$TABLE1" ]; then
    echo "Error: table1.csv not generated"
    exit 1
fi

if [ ! -f "$TABLE2" ]; then
    echo "Error: table2.csv not generated"
    exit 1
fi

# Create combined CSV
echo "Creating combined CSV..."
echo "program,qubits,gates,result,time,memory" > "$OUTPUT_FILE"

# Add all rows from table1.csv (skip header)
tail -n +2 "$TABLE1" >> "$OUTPUT_FILE"

# Add all rows from table2.csv (skip header)
tail -n +2 "$TABLE2" >> "$OUTPUT_FILE"

echo "Combined CSV generation completed. Output saved to $OUTPUT_FILE"
echo "==============================================================="

# Display the combined CSV
cat "$OUTPUT_FILE"

# Optional: Clean up intermediate files if desired
# echo "Cleaning up intermediate files..."
# rm -f table1.csv table2.csv