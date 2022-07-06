#!/bin/bash
#make release

# Table 2. Results of Bernstein-Vazirani
echo 'Table 2:'
for i in {6..14..2}; do VATA_PATH=/home/alan23273850/libvata/build/cli/vata build/cli/vata 1 $i; done

# Table 3. Results of Grover’s Search
echo -e '\nTable 3:'
for i in {2..8..2}; do VATA_PATH=/home/alan23273850/libvata/build/cli/vata build/cli/vata 2 $i; done

# Table 4. Results of Flawed Bernstein-Vazirani
echo -e '\nTable 4:'
for i in {6..14..2}; do VATA_PATH=/home/alan23273850/libvata/build/cli/vata build/cli/vata 7 $i; done

# Table 5. Results of Flawed Grover's Search
echo -e '\nTable 5:'
for i in {2..8..2}; do VATA_PATH=/home/alan23273850/libvata/build/cli/vata build/cli/vata 8 $i; done

# Table 6. Running Time of Different Gates on the 1st Qubit of a 10-Qubit Circuit
echo -e '\nTable 6:'
echo 'X & Y & Z & H & S & T & Rx & Ry & CNOT & CZ & Toffoli & Fredkin\\ \hline'
for i in {1..12}; do VATA_PATH=/home/alan23273850/libvata/build/cli/vata build/cli/vata 0 $i; done

# Table 7. Running Time on Random Circuits
echo -e '\n\nTable 7:'
echo 'Qubit \# & 10 & 20 & 40 & 80 & 160 & 320\\ \hline'
echo -n 'Random+Top'
VATA_PATH=/home/alan23273850/libvata/build/cli/vata timeout 600 build/cli/vata 3 10
VATA_PATH=/home/alan23273850/libvata/build/cli/vata timeout 600 build/cli/vata 3 20
echo ' & & & & & \\ \hline'
echo -n 'Random'
VATA_PATH=/home/alan23273850/libvata/build/cli/vata timeout 600 build/cli/vata 4 10
VATA_PATH=/home/alan23273850/libvata/build/cli/vata timeout 600 build/cli/vata 4 20
echo ' & & & & & \\ \hline'
echo -n 'Random+Bottom'
declare -a arr=("10" "20" "40" "80" "160" "320")
for i in "${arr[@]}"; do VATA_PATH=/home/alan23273850/libvata/build/cli/vata build/cli/vata 5 $i; done
