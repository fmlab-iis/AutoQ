#!/bin/bash
rm -f output.txt

echo "Running autoq_parametric_ghz"
echo -n "Fig. 20c & " >> output.txt
../../../build/cli/autoq_parametric_ghz >> output.txt
echo >> output.txt

echo "Running autoq_diagonal_hamiltonian"
echo -n "DHS      & " >> output.txt
../../../build/cli/autoq_diagonal_hamiltonian >> output.txt
echo >> output.txt

echo "Running autoq_single_fermionic"
echo -n "Fig. 21a & " >> output.txt
../../../build/cli/autoq_single_fermionic >> output.txt
echo >> output.txt

echo "Running autoq_double_fermionic"
echo -n "Fig. 21b & " >> output.txt
../../../build/cli/autoq_double_fermionic >> output.txt
echo >> output.txt
