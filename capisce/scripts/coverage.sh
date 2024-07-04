#! /bin/bash

./capisce exp -name arp -replay -out survey_data_oopsla
./capisce exp -name heavy_hitter_2 -replay -out survey_data_oopsla
./capisce exp -name heavy_hitter_1 -replay -out survey_data_oopsla
./capisce exp -name flowlet -replay -out survey_data_oopsla
./capisce exp -name 07-multiprotocol -replay -out survey_data_oopsla
./capisce exp -name simple_nat -replay -out survey_data_oopsla

python3 scripts/graphs.py
