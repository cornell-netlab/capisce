#include <core.p4>
#define V1MODEL_VERSION 20200408
#include <v1model.p4>

struct ghost_t {
    bit<1>  assign;
    bit<1>  alloc;
    bit<1>  deref;
}

header ethernet_t {
    bit<48> dstAddr;
    bit<48> srcAddr;
    bit<16> etherType;
}

header icmp_t {
    bit<16> typeCode;
    bit<16> hdrChecksum;
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

header ipv6_t {
    bit<4>   version;
    bit<8>   trafficClass;
    bit<20>  flowLabel;
    bit<16>  payloadLen;
    bit<8>   nextHdr;
    bit<8>   hopLimit;
    bit<128> srcAddr;
    bit<128> dstAddr;
}

header tcp_t {
    bit<16> srcPort;
    bit<16> dstPort;
    bit<32> seqNo;
    bit<32> ackNo;
    bit<4>  dataOffset;
    bit<4>  res;
    bit<8>  flags;
    bit<16> window;
    bit<16> checksum;
    bit<16> urgentPtr;
}

header udp_t {
    bit<16> srcPort;
    bit<16> dstPort;
    bit<16> length_;
    bit<16> checksum;
}

header vlan_tag_t {
    bit<3>  pcp;
    bit<1>  cfi;
    bit<12> vid;
    bit<16> etherType;
}

struct metadata {
    bit<16> ptr;
    ghost_t spec;
}

struct headers {
    ethernet_t ethernet;
    icmp_t     icmp;
    ipv4_t     ipv4;
    ipv6_t     ipv6;
    tcp_t      tcp;
    udp_t      udp;
    vlan_tag_t vlan_tag;
}

parser ParserImpl(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name(".start") state start {
        packet.extract(hdr.ethernet);
        transition accept;
    }
}

control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    action alloc () {
        meta.spec.alloc = 1w1;
    }
    action unalloc () {
        meta.spec.alloc = 1w0;
    }
    action drop_ () {
        mark_to_drop(standard_metadata);
    }
    action fwd (bit<9> port) {
        standard_metadata.egress_spec = port;
        meta.spec.deref = 1w1;
    }
    action assign_(bit<16> ptr){
        meta.ptr = ptr;
        meta.spec.assign = 1w1;
    }
    table assign {
        key = {
            hdr.ethernet.dstAddr : exact;
        }
        actions = {
           assign_;
           drop_;
        }
    }
    table allocator {
        key = {
            meta.ptr : exact;
        }
        actions = {
          alloc;
          @defaultonly unalloc;
        }
        const default_action = unalloc;
    }
    table deref {
        key = {
            meta.ptr : exact;
        }
        actions = {
            fwd;
            @defaultonly drop_;
        }
        const default_action = drop_;
    }

    apply {
      meta.spec.assign = 1w0;
      meta.spec.alloc = 1w0;
      meta.spec.deref = 1w0;
      // meta.ptr = 16w0;
      assign.apply();
      allocator.apply();
      deref.apply();
      assert(meta.spec.assign == 1w0 || meta.spec.alloc == 1w1);
      assert(meta.spec.deref == 1w0 || meta.spec.alloc == 1w1);
      standard_metadata.egress_spec = 9w511;
    }
}

control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {}
}

control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.ethernet);
    }
}

control verifyChecksum(inout headers hdr, inout metadata meta) {
    apply {}
}

control computeChecksum(inout headers hdr, inout metadata meta) {
    apply {}
}

V1Switch(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;

