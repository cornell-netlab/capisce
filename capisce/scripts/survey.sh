#! /usr/bin/bash

data_dir="./survey_data_oopsla"
log_dir="./log_oopsla"

# rm -r $data_dir
mkdir $data_dir
# rm -r $log_dir
mkdir $log_dir

function run {
    start=$(date +%s%N | cut -b1-13)
    ./capisce exp -name $1 -out $data_dir 2>&1 > "${log_dir}/${1}"
    finish=$(date +%s%N | cut -b1-13)
    echo $1
}

run ecmp;
run netpaxos_acceptor;
run resubmit;
run ndp_router;
run heavy_hitter_1;
run arp;
run "07-multiprotocol";
run mc_nat;
run mc_nat_fixed;
run ts_switching;
run ts_switching_fixed;
run heavy_hitter_2;
run heavy_hitter_2_fixed;
run flowlet;
run flowlet_fixed;
run hula;
run hula_fixed;
run netchain;
run simple_nat;
run fabric;
run fabric_fixed;
run linearroad
run linearroad_fixed;
