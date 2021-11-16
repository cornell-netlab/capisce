#!/usr/bin/env bash
set -euo pipefail

# smpl=./data/cvc4_simplified_new.csv
full=./data/cvc4_new.csv

# x=$1
# echo "num,ms,ok" > $smpl
# while [ $x -le $2 ]; do
#     echo
#     echo
#     echo Trying example $x;
#     time ./pbench bench $x -one -s -cvc4 >> $smpl
#     x=$((x + 1))
# done

x=$1
echo "num,ms,ok" > $full
while [ $x -le $3 ]; do
    echo
    echo
    echo Trying example $x;
    time ./pbench bench $x -one -cvc4 >> $full
    x=$((x + 1))
done
