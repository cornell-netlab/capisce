#!/usr/bin/env sh

resolution=700

icecap () {
    echo "connecting to ${1}@${2}"
    ssh "${1}@${2}.cs.cornell.edu" -- 'cd inference/benchmarks/; eval $(opam env);' "sh ./scripts/parallelize.sh $resolution $3 $4 &"
}

lo=0

for i in 1 2; do
    hi=$((${lo}+61))
    icecap ehc86 pronto-${i} ${lo} ${hi} &
    lo=$(($hi + 1))
done

# ATLAS
# ecampbell0@atlas-2.cs.cornell.edu
for i in 3 4 5 6 7 8 9 11 16 17 18 19 20 22 23
do
    hi=$((${lo} + 31))
    icecap ecampbell atlas-${i} ${lo} ${hi} &
    lo=$((${hi} + 1))
done

for i in 25 26
do
    hi=$((${lo} + 47))
    icecap ecampbell atlas-${i} ${lo} ${hi} &
    lo=$((${hi} + 1))
done

out=$HOME/p4-inference/benchmarks/fabric_cpis
if [ -d ${out} ]; then
    rm -r ${out}
fi
mkdir ${out}

echo "initially sleep for 5 minutes"
time=$((60 * 1))
sleep ${time}

while true
do
    time=$((${time} + 30))
    sleep 30
    for i in 1 2
    do
        echo "downloading pronto-${i}"
        scp -r ehc86@pronto-${i}.cs.cornell.edu:"inference/benchmarks/fabric_cpis/slice_${resolution}_*" $out
    done
    for i in 3 4 5 6 7 8 11 16 17 18 19 20 22 23 25 26
    do
        echo "downloading atlas-${i}"
        scp -r ecampbell@atlas-${i}.cs.cornell.edu:"inference/benchmarks/fabric_cpis/slice_${resolution}_*" $out
    done

    echo "$out"
    completed=$(ls -1 $out | wc -l)
    lines=$(cat $out/* | wc -l )
    echo "found ${completed} of ${resolution} CPIs"
    if [ $completed -ge $resolution ]; then
        if [ $lines > $resolution ]; then
            echo "so we're done in $time s"
            exit 0
        fi
    fi
    echo "hit enter to check again?"
    read x
done
