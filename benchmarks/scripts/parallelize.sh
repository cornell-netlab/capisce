#!/usr/bin/env sh

resolution=$1 ## the precision with which to slice the program
slice_id_lo=$2 ## the lowest thread id (inclusive)
slice_id_hi=$3 ## the highest thread id (inclusive)

echo "resolution ${resolution}"
echo "slices [$2, $3]"

runner="icecap hoare examples/bf4_failing/fabric_no_consts_exact_only.p4 -I examples/includes -D"
outfile="fabric_cpis/slice_${resolution}"

for slice_id in $(seq $slice_id_lo $slice_id_hi); do
    echo "icecap hoare examples/bf4_failing/fabric_no_consts_exact_only.p4 -I examples/includes -D --nprocs ${resolution} --pid ${slice_id} > ${outfile}_${slice_id} &"
    (icecap hoare examples/bf4_failing/fabric_no_consts_exact_only.p4 -I examples/includes -D --nprocs ${resolution} --pid ${slice_id} > ${outfile}_${slice_id}; echo "done ${slice_id}") &
done
