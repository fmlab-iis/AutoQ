#!/bin/bash
# =============================================================================
# AutoQ — Formal Verification of Quantum Programs
# Artifact evaluation entry point
#
# Usage:  bash run.sh
# Build:  make            (then re-run this script)
# Docker: see README_DOCKER.md
# =============================================================================

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AUTOQ_BIN="${SCRIPT_DIR}/build/cli/autoq"

BOLD='\033[1m'; GREEN='\033[0;32m'; RED='\033[0;31m'; NC='\033[0m'

echo -e "${BOLD}============================================================${NC}"
echo -e "${BOLD}  Verifying repeat-until-success protocols within automata${NC}"
echo -e "${BOLD}============================================================${NC}"
echo ""

if [ ! -f "$AUTOQ_BIN" ]; then
    echo -e "${RED}[!] Binary not found. Please run: make${NC}"
    exit 1
fi
echo -e "${GREEN}[✓] $AUTOQ_BIN${NC}"
echo ""

echo "Select an option:"
echo "  1) Individual RUS circuits  — Figure 7–10, Table 1"
echo "  2) Composed RUS circuits    — V_i → CX → V_j, Table 2"
echo "  3) Both                     — run 1 then 2"
echo "  q) Quit"
echo ""
read -rp "Choice [1-3/q]: " CHOICE
echo ""

export AUTOQ_BIN

case "$CHOICE" in
    1)
        bash "${SCRIPT_DIR}/scripts/RUS_single.sh"
        ;;
    2)
        bash "${SCRIPT_DIR}/scripts/RUS_composed.sh"
        ;;
    3)
        bash "${SCRIPT_DIR}/scripts/RUS_single.sh"
        echo ""
        bash "${SCRIPT_DIR}/scripts/RUS_composed.sh"
        ;;
    q|Q)
        exit 0 ;;
    *)
        echo -e "${RED}Invalid choice.${NC}"; exit 1 ;;
esac

echo ""

# ── Generate and display formatted tables ──
print_table() {
    local csv_file="$1"
    local title="$2"
    if [ ! -f "$csv_file" ]; then return; fi
    echo -e "${BOLD}${title}${NC}"
    python3 -c "
import csv, unicodedata, sys
def vw(s):
    return sum(2 if unicodedata.east_asian_width(c) in 'WF' else 1 for c in s)
rows=list(csv.reader(open(sys.argv[1])))
if not rows: sys.exit()
n=len(rows[0])
w=[max(vw(r[i]) if i<len(r) else 0 for r in rows) for i in range(n)]
for r in rows:
    parts=[]
    for i in range(n):
        c=r[i] if i<len(r) else ''
        parts.append(c+' '*(w[i]-vw(c)))
    print('  '.join(parts))
" "$csv_file"
    echo ""
}

case "$CHOICE" in
    1)
        echo -e "${BOLD}Generating Table 1...${NC}"
        bash "${SCRIPT_DIR}/scripts/analysis/RUS_benchmarks_table1.sh" > /dev/null 2>&1
        print_table "table1.csv" "Table 1: Individual RUS Circuits"
        ;;
    2)
        echo -e "${BOLD}Generating Table 2...${NC}"
        bash "${SCRIPT_DIR}/scripts/analysis/RUS_benchmarks_table2.sh" > /dev/null 2>&1
        print_table "table2.csv" "Table 2: Composed RUS Circuits"
        ;;
    3)
        echo -e "${BOLD}Generating Tables...${NC}"
        bash "${SCRIPT_DIR}/scripts/analysis/RUS_benchmarks_table1.sh" > /dev/null 2>&1
        bash "${SCRIPT_DIR}/scripts/analysis/RUS_benchmarks_table2.sh" > /dev/null 2>&1
        print_table "table1.csv" "Table 1: Individual RUS Circuits"
        print_table "table2.csv" "Table 2: Composed RUS Circuits"
        ;;
esac

echo -e "${BOLD}Done.${NC}"
