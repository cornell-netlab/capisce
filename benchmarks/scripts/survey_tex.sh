#! /usr/bin/bash

data_dir="${HOME}/p4-inference/benchmarks/survey_data"
log_dir="${HOME}/p4-inference/benchmarks/log"

rm -r $data_dir
mkdir $data_dir
rm -r $log_dir
mkdir $log_dir

function conc {
    icecap exp -name $1 -out $data_dir 2&>1 > "${log_dir}/${1}";
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
conc heavy_hitter_2 &\
conc heavy_hitter_2_fixed &\
conc flowlet &\
conc flowlet_fixed &\
conc hula &\
conc hula_fixed &\
conc netchain &\
conc simple_nat &\
conc fabric_fixed