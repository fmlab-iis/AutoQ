#!/bin/bash
oldfile=$1
newfile="${oldfile%.qasm}.qc"
cp $oldfile $newfile

# Ignore lines containing "OPENQASM 2.0;" or "include \"qelib1.inc\""
sed -i '/OPENQASM 2.0;/d' "$newfile"
sed -i '/include "qelib1.inc";/d' "$newfile"

# Replace "qreg q[7];" with ".v 0 1 2 3 4 5 6"
sed -i -E 's/qreg [^\d]*\[([0-9]+)\];/echo -n ".v "; seq -s " " 0 $((\1 - 1)); echo BEGIN/e' "$newfile"

# Replace "x q[5];" with "X 5"
#   H _               -> hgate
#   X _               -> xgate
#   Y _               -> ygate
#   Z _               -> zgate
#   CNOT _ _          -> cxgate
#   CZ _ _            -> czgate
#   S _               -> sgate
#   Sinv _            -> sdggate
#   T _               -> tgate
#   Tinv _            -> tdggate
#   Swap _ _          -> swapgate
#   Rz theta _        -> rzgate $ fromDyadic $ discretize theta
#   Rx theta _        -> hgate * rzgate (fromDyadic $ discretize theta) * hgate
#   Ry theta _        -> rzgate (fromDyadic $ discretize theta) * hgate * rzgate (fromDyadic $ discretize theta) * hgate
#   Uninterp "CCZ" _  -> cczgate
#   Uninterp _ _      -> error "Uninterpreted gates not supported"
sed -i -E 's/h q\[([0-9]+)\];/H \1/g' "$newfile"
sed -i -E 's/x q\[([0-9]+)\];/X \1/g' "$newfile"
sed -i -E 's/y q\[([0-9]+)\];/Y \1/g' "$newfile"
sed -i -E 's/z q\[([0-9]+)\];/Z \1/g' "$newfile"
sed -i -E 's/cx q\[([0-9]+)\][^a-z]+q\[([0-9]+)\];/tof \1 \2/g' "$newfile"
sed -i -E 's/cz q\[([0-9]+)\][^a-z]+q\[([0-9]+)\];/CZ \1 \2/g' "$newfile"
sed -i -E 's/s q\[([0-9]+)\];/S \1/g' "$newfile"
sed -i -E 's/sdg q\[([0-9]+)\];/Sinv \1/g' "$newfile"
sed -i -E 's/t q\[([0-9]+)\];/T \1/g' "$newfile"
sed -i -E 's/tdg q\[([0-9]+)\];/Tinv \1/g' "$newfile"
sed -i -E 's/swap q\[([0-9]+)\][^a-z]+q\[([0-9]+)\];/Swap \1 \2/g' "$newfile"
sed -i -E 's/rz\((.+)\) q\[([0-9]+)\];/Rz \1 \2/g' "$newfile"
sed -i -E 's/rx\((.+)\) q\[([0-9]+)\];/Rx \1 \2/g' "$newfile"
sed -i -E 's/ry\((.+)\) q\[([0-9]+)\];/Ry \1 \2/g' "$newfile"
sed -i -E 's/ccx q\[([0-9]+)\][^a-z]+q\[([0-9]+)\][^a-z]+q\[([0-9]+)\];/tof \1 \2 \3/g' "$newfile"

echo "END" >> $newfile
