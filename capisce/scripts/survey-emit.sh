#! /usr/bin/bash

p4_dir="${1}"

# rm -r $p4_dir
mkdir -p $p4_dir

function run {
    ./capisce emit $1 -p4 2>&1 > "${p4_dir}/${1}.p4"
    echo "${p4_dir}/${1}.p4"
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
