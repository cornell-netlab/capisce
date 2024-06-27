#include <core.p4>
#define V1MODEL_VERSION 20180101
#include <v1model.p4>

header hdr_t {
   bit<32> x0;
   bit<32> x1;
   bit<32> x2;
   bit<32> x3;
   bit<32> x4;
   bit<32> x5;
   bit<32> x6;
   bit<32> x7;
   bit<32> x8;
   bit<32> x9;
   bit<32> x10;
}

action nop() {
    NoAction();
}
struct fabric_metadata_t {
}

struct parsed_headers_t {
   hdr_t hdr;
}


control FabricComputeChecksum(inout parsed_headers_t hdr, inout fabric_metadata_t meta) {
    apply {
    }
}

control FabricVerifyChecksum(inout parsed_headers_t hdr, inout fabric_metadata_t meta) {
    apply {
    }
}

parser FabricParser(packet_in packet, out parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
  state start {
    packet.extract(hdr.hdr);
    transition accept;
  }
}

control FabricDeparser(packet_out packet, in parsed_headers_t hdr) {
    apply {
      packet.emit(hdr.hdr);
    }
}

control FabricIngress(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
    action nop_acl (){ }
    action drop() {
       mark_to_drop(standard_metadata);
    }
    table acl {
        key = {
            hdr.hdr.x0  : ternary;
            hdr.hdr.x1  : ternary;
            hdr.hdr.x2  : ternary;
            hdr.hdr.x3  : ternary;
            hdr.hdr.x4  : ternary;
            hdr.hdr.x5  : ternary;
            hdr.hdr.x6  : ternary;
            hdr.hdr.x7  : ternary;
            hdr.hdr.x8  : ternary;
            hdr.hdr.x9  : ternary;
            hdr.hdr.x10 : ternary;
        }
        actions = {
            drop;
            nop_acl;
        }
    }
    apply {
        acl.apply();
    }
}

control FabricEgress(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
   apply {
   }
}

V1Switch(FabricParser(), FabricVerifyChecksum(), FabricIngress(), FabricEgress(), FabricComputeChecksum(), FabricDeparser()) main;
