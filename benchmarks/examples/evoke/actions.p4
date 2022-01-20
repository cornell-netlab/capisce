#include <core.p4>
#define V1MODEL_VERSION 20200408
#include <v1model.p4>

struct ingress_metadata_t {
    bit<1> drop;
    bit<9> egress_port;
    bit<4> packet_type;
}

header ethernet_t {
    bit<48> dstAddr;
    bit<48> srcAddr;
    bit<16> etherType;
}

header ipv4_t {
    bit<4>  version;
    bit<4>  ihl;
    bit<8>  diffserv;
    bit<16> totalLen;
    bit<16> identification;
    bit<3>  flags;
    bit<13> fragOffset;
    bit<8>  ttl;
    bit<8>  protocol;
    bit<16> hdrChecksum;
    bit<32> srcAddr;
    bit<32> dstAddr;
}

struct metadata {
    @name(".ing_metadata") 
    ingress_metadata_t ing_metadata;
}

struct headers {
    @name(".ethernet") 
    ethernet_t ethernet;
    @name(".ipv4")
    ipv4_t     ipv4;
    ipv4_t     ipv4_2;
}

parser ParserImpl(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name(".parse_ipv4") state parse_ipv4 {
        packet.extract(hdr.ipv4);
    }
    @name(".start") state start {
        packet.extract(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            16w0x800: parse_ipv4;
            default: accept;
        }
    }
}

control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {
    }
}

control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    action drop_() { standard_metadata.egress_spec = 9w511; }
    action validate_2() { hdr.ipv4_2.setValid();  }
    action use_2() {hdr.ipv4_2.ttl = hdr.ipv4_2.ttl - 8w1; }

    table t1 {
          key = { hdr.ethernet.etherType : exact; }
          actions = { validate_2; drop_; }
    }
    table t2 {
          key = { hdr.ethernet.srcAddr : exact; }
          actions = { use_2; drop_; }
    }

    apply {
      t1.apply();
      t2.apply();
      standard_metadata.egress_spec = 9w5;
    }
}

control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.ethernet);
        packet.emit(hdr.ipv4);
    }
}

control verifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}

control computeChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}

V1Switch(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;

