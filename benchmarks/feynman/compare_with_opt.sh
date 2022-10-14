#!/bin/bash
for file in *.qc; do
    echo -n "$file "
    ~/feynman/feynver $file ./opt/$file
done