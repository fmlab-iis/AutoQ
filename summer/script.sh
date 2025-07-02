#!/bin/bash

for i in $(seq 1 11); do
    echo "==========="
    echo "Problem $i:"
    ../build/cli/verify_your_lsta_is_correct q$i.lsta q$i.hsl
done