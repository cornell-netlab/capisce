#! /usr/bin/bash

test_dir="./examples/bf4_failing"
includes_dir="./examples/includes"
success_dir="./examples/bf4_passing"

# coloration
RED='\033[0;31m'
GRN='\033[0;32m'
NC='\033[0m' # No Color
PASS="${GRN}[PASS]${NC}"
FAIL="${RED}[FAIL]${NC}"


eval $(opam env)
make
mv $success_dir/* $test_dir
if [ $? -eq 0 ]; then
    for f in $test_dir/*.p4; do
        ./capisce infer $f -I $includes_dir >/dev/null 2>&1
        if [ $? -eq 0 ]; then
            echo -e "$PASS ./capisce infer $f -I $includes_dir"
            mv $f $success_dir/
        else
            echo -e "$FAIL ./capisce infer $f -I $includes_dir"
        fi
    done
fi

successes=$(ls -1 ${success_dir} | wc -l)
failures=$(ls -1 ${test_dir} | wc -l)
total=$(($successes + $failures))
passing_percent=$(echo "scale=2; $successes / $total" | bc)
echo "${passing_percent} passing (${successes} / $total)"
