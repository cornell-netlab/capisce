FROM ubuntu:16.04

## update repositories
RUN apt update
RUN apt upgrade -y

## install git
RUN apt install git -y

## START INSTALL bf4 DEPENDENCIES
RUN apt install cmake g++ automake libtool libgc-dev bison flex libfl-dev libgmp-dev libboost-dev libboost-iostreams-dev libboost-graph-dev llvm pkg-config -y
RUN apt install python python-scapy python-ipaddr python-ply tcpdump -y

### INSTALL PROTOBUF
RUN apt install autoconf unzip curl -y
RUN git clone https://github.com/protocolbuffers/protobuf.git
WORKDIR ./protobuf
RUN git checkout v3.2.0
RUN ./autogen.sh
RUN ./configure
RUN make
RUN make install
RUN ldconfig

### INSTALL z3
WORKDIR ..
RUN git clone https://github.com/Z3Prover/z3.git
WORKDIR z3
RUN git config --global user.email "BORKED@BORKED.com"
RUN git config --global user.name "BORKED"
RUN git stash
RUN git checkout z3-4.8.7

RUN python scripts/mk_make.py
WORKDIR build
RUN make
RUN make install
WORKDIR ../..

### INSTALL THRIFT
RUN apt install wget -y
RUN apt install libboost-all-dev libevent-dev libssl-dev make pkg-config -y
RUN wget https://dlcdn.apache.org/thrift/0.20.0/thrift-0.20.0.tar.gz -O ./thrift-0.20.0.tar.gz
RUN tar -xvf ./thrift-0.20.0.tar.gz
WORKDIR ./thrift-0.20.0
RUN ./bootstrap.sh
RUN ./configure
RUN make
RUN make install
WORKDIR ..


### INSTALL INJA
RUN wget https://github.com/pantor/inja/releases/download/v2.2.0/inja.hpp -O /usr/include/inja.hpp

### INSTALL JSON LIBRARY
RUN mkdir /usr/include/nlohmann
RUN wget https://github.com/nlohmann/json/releases/download/v3.7.3/json.hpp -O /usr/include/nlohmann/json.hpp

## FINALLY INSTALL BF4
RUN git clone --recursive https://github.com/dragosdmtrsc/bf4.git
WORKDIR bf4
RUN mkdir build
WORKDIR build
RUN cmake -DENABLE_UNIFIED_COMPILATION=OFF -DENABLE_GC=OFF ..
# RUN make
# RUN make install


## Configure templates
# RUN make cptemplate
