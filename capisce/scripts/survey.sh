#! /usr/bin/bash

data_dir="./survey_data_oopsla"
log_dir="./log_oopsla"

# rm -r $data_dir
mkdir $data_dir
# rm -r $log_dir
mkdir $log_dir

function conc {
    start=$(date +%s%N | cut -b1-13)
    capisce exp -name $1 -out $data_dir 2>&1 > "${log_dir}/${1}"
    finish=$(date +%s%N | cut -b1-13)
    echo $1
}

conc ecmp &\
conc netpaxos_acceptor &\
conc resubmit &\
conc ndp_router &\
conc heavy_hitter_1 &\
conc arp &\
conc "07-multiprotocol"&\
conc mc_nat &\
conc mc_nat_fixed &\
conc ts_switching &\
conc ts_switching_fixed &\
conc heavy_hitter_2 &\
conc heavy_hitter_2_fixed &\
conc flowlet &\
conc flowlet_fixed &\
conc hula &\
conc hula_fixed &\
conc netchain &\
conc simple_nat &\
conc fabric &\
conc fabric_fixed &\
conc linearroad &\
conc linearroad_fixed
