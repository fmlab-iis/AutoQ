#!/bin/bash
# =============================================================================
# AutoQ — Formal Verification of Quantum Programs
# Artifact evaluation entry point
#
# Usage:  bash run.sh    (auto-builds via `make release` if needed)
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
    echo -e "${RED}[!] Binary not found. Running: make release${NC}"
    echo ""
    if ! make -C "$SCRIPT_DIR" release; then
        echo -e "${RED}[!] Build failed.${NC}"
        exit 1
    fi
    echo ""
    if [ ! -f "$AUTOQ_BIN" ]; then
        echo -e "${RED}[!] Build succeeded but binary still not found at $AUTOQ_BIN${NC}"
        exit 1
    fi
fi
echo -e "${GREEN}[✓] $AUTOQ_BIN${NC}"
echo ""

export AUTOQ_BIN

bash "${SCRIPT_DIR}/scripts/RUS_single.sh"
echo ""
bash "${SCRIPT_DIR}/scripts/RUS_composed.sh"

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

echo -e "${BOLD}Generating Tables...${NC}"
bash "${SCRIPT_DIR}/scripts/analysis/RUS_benchmarks_table1.sh" > /dev/null 2>&1
bash "${SCRIPT_DIR}/scripts/analysis/RUS_benchmarks_table2.sh" > /dev/null 2>&1
print_table "table1.csv" "Table 1: Individual RUS Circuits"
print_table "table2.csv" "Table 2: Composed RUS Circuits"

echo -e "${BOLD}Done.${NC}"
