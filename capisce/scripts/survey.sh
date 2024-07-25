#! /usr/bin/bash

data_dir="${1}"
log_dir="${2}"
flag="${3}"

# rm -r $data_dir
mkdir -p $data_dir
# rm -r $log_dir
mkdir -p $log_dir

function run {
    start=$(date +%s%N | cut -b1-13)
    ./capisce exp $1 -${flag} -out $data_dir 2>&1 > "${log_dir}/${1}"
    finish=$(date +%s%N | cut -b1-13)
    echo $1
}

run "ecmp";
run "netpaxos-acceptor";
run "resubmit";
run "ndp-router";
run "heavy-hitter-1";
run "arp";
run "07-multiprotocol";
run "mc-nat";
run "mc-nat-fixed";
run "ts-switching";
run "ts-switching-fixed";
run "heavy-hitter-2";
run "heavy-hitter-2-fixed";
run "flowlet";
run "flowlet-fixed";
run "hula";
run "hula-fixed";
run "netchain";
run "simple-nat";
run "fabric";
run "fabric-fixed";
run "linearroad-fixed";
run "linearroad";
