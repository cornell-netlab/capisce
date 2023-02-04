#!/usr/bin/env sh

dir=fabric_cpis
tmp="/tmp/tmp.smt2"
touch $tmp

for f in $(ls $dir)
do
    output="${dir}/${f}"
    tail -n +4 $output > $tmp
    mv $tmp $output
done
