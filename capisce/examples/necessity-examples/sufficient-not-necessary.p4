#include <core.p4>

#include <v1model.p4>

struct metadata {
   bit<32> x;
   bit<32> y;
}

header ethernet_t {
  bit<48> dst;
  bit<48> src;
  bit<16> typ;
}

header ipv4_t{
  bit<64> other_stuff;
  bit<8> ttl;
  bit<8> proto;
  bit<16> chksum;
  bit<32> src;
  bit<32> dst;
}

struct headers {
  ethernet_t ethernet;
  ipv4_t ipv4;
  
 }

parser ParserImpl(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name(".start") state start {
        packet.extract(hdr.ethernet);
        transition select(hdr.ethernet.typ) {
           2048 : parse_ipv4;
	   default : accept;
        }
    }

    @name(".parse_ipv4") state parse_ipv4 {
        packet.extract(hdr.ipv4);
	transition accept;
    }
}

control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {}
}

control ingress(inout headers hdr,
                inout metadata meta,
		inout standard_metadata_t standard_metadata) {

    action fwd() {
       standard_metadata.egress_spec = 47;
    }
    action setbit(){
      meta.x = (hdr.ethernet.dst == hdr.ethernet.src) ? 32w0 : 32w1;
    }
    @name(".t") table t {
        key = {
	   hdr.ethernet.dst : exact;
        }
        actions = {
            fwd;
	    setbit;
        }
	default_action = fwd();
    }
    apply {
        t.apply();
	if (meta.x == 1) {
	   standard_metadata.egress_spec = 99;
        } else {
          meta.x = 1;
        }
    }
}

control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
    }
}

control verifyChecksum(inout headers hdr, inout metadata meta) {
    apply {}}

control computeChecksum(inout headers hdr, inout metadata meta) {
    apply {}}

V1Switch<headers, metadata>(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;

