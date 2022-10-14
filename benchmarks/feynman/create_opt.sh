#!/bin/bash
rm -r opt
mkdir opt
for file in *.qc; do
    ~/feynman/feynopt $file > ./opt/$file
done