#! /usr/bin/bash

test_dir="./examples/bf4_failing"
includes_dir="./examples/includes"
success_dir="./examples/bf4_passing"
nocomp_dir="./examples/bf4_nocompile"
evoke_dir="./examples/evoke"
dup_dir="./examples/bf4_dups"
log_dir="./examples/logs"

# coloration
RED='\033[0;31m'
GRN='\033[0;32m'
YLW='\033[0;33m'
BLU='\033[0;34m'
NC='\033[0m' # No Color
PASS="${GRN}[PASS]${NC}"
FAIL="${RED}[FAIL]${NC}"
BUNK="${YLW}[BUNK]${NC}"
SKIP="${YLW}[SKIP]${NC}"

# mkdirs if they dont exist
if [ ! -d $success_dir ]; then
    mkdir $success_dir
fi
if [ ! -d $nocomp_dir ]; then
    mkdir $nocomp_dir
fi
if [ ! -d $dup_dir ]; then
    mkdir $dup_dir
fi
if [ ! -d $log_dir ]; then
    mkdir $log_dir
fi

if [ ! -d $test_dir ]; then
    echo "error, couldn't find test directory ${test_dir}" >&2
    exit 1
fi


if [ -z $(which petr4) ]; then
    echo "error petr4 is not installed" >&2
    exit 1
fi

# move everything to the starting directory
if [ ! -z "$(ls $success_dir)" ]; then
    mv $success_dir/* $test_dir
fi
if [ ! -z "$(ls $nocomp_dir)" ]; then
    mv $nocomp_dir/* $test_dir
fi
if [ ! -z "$(ls $evoke_dir)" ]; then
    cp $evoke_dir/* $test_dir
fi


# make capisce
eval $(opam env)
make

# if building succeeded run the tests
if [ $? -eq 0 ]; then
    # iterate through test programs
    for f in $test_dir/*.p4; do
        b=$(basename $f)
        log=${log_dir}/${b}.log
        # check if the program works with the petr4 frontend
        errors=$(petr4 typecheck $f -I $includes_dir > ${log} 2>&1)
        # if it doesn't move it to the directory of non-compiling programs
        if [ ! -z "${errors}" ]; then
            echo -e "$BUNK ${BLU}${b}${NC}"
            echo -e "\tcat ${log}"
            mv $f $nocomp_dir
        else
            # otherwise run icecap
            echo -e -n "[..] ${BLU}${b}${NC}\r"
            ./icecap infer $f -I $includes_dir --skip-check > ${log} 2>&1
            if [ $? -eq 0 ]; then
                echo -e "$PASS ${BLU}${b}${NC}"
                echo -e "\tcat ${log}"
                mv $f $success_dir/
            else
                echo -e "$FAIL ${BLU}${b}${NC}"
                echo -e "\tcat ${log}"
                echo -e "\t./icecap infer ${f} -I ${includes_dir} -D"
            fi
        fi
    done
    for f in $test_dir/*.skip; do
        b=$(basename $f)
        echo -e "$SKIP ${BLU}${b}${NC}"
    done

fi

echo
echo "Programs that have manual duplicates above"
echo

for f in $dup_dir/*.p4; do
    # check if the program works with the petr4 frontend
    errors=$(petr4 typecheck $f -I $includes_dir 2>&1 >/dev/null)
    # if it doesn't move it to the directory of non-compiling programs
    if [ ! -z "${errors}" ]; then
        echo -e "$BUNK petr4 typecheck $f -I $includes_dir"
    else
        # otherwise run icecap
        ./icecap infer $f -I $includes_dir >/dev/null 2>&1
        if [ $? -eq 0 ]; then
            echo -e "$PASS ./icecap infer $f -I $includes_dir"
        else
            echo -e "$FAIL ./icecap infer $f -I $includes_dir"
        fi
    fi
done




# summary stats
successes=$(ls -1 ${success_dir} | wc -l)
failures=$(ls -1 ${test_dir} | wc -l)
total=$(($successes + $failures))
nocomp=$(ls -1 ${nocomp_dir} | wc -l)
dups=$(ls -1 ${dup_dir} | wc -l)
passing_percent=$(echo "scale=2; $successes / $total" | bc)
echo
echo "~~~~Summary~~~~~"
echo "  ${passing_percent} passing ( ${successes} passed of ${total} that compiled )"
echo "  ${nocomp} programs didn't make it past the petr4 frontend"
echo "  ${dups} programs currently fail but have simple manually-corrected versions that succeed"
