#include <core.p4>
#define V1MODEL_VERSION 20200408
#include <v1model.p4>

struct ingress_metadata_t {
}

header h_t {
   bit<16> value;
}

struct metadata {
    ingress_metadata_t ing_metadata;
}

struct headers {
    h_t h0;
    h_t h1;
    h_t h2;
    h_t h3;
    h_t h4;
}

parser ParserImpl(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name(".start") state start {
        packet.extract(hdr.h0);
    }
}

control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    action drop_() {
        mark_to_drop(standard_metadata);
    }
    action validate_h1(bit<16> value) {
        hdr.h1.setValid();
        hdr.h1.value = value;
    }
    action validate_h2(bit<16> value) {
        hdr.h2.setValid();
        hdr.h2.value = value;
    }
    action validate_h3(bit<16> value) {
        hdr.h3.setValid();
        hdr.h3.value = value;
    }
    action use_h1_h2_h3() {
        hdr.h4.setValid();
        hdr.h4.value =
           (hdr.h1.value & (hdr.h2.value | hdr.h3.value)) -
           ((hdr.h1.value | (hdr.h2.value & hdr.h3.value)));
        assert(hdr.h4.value <= (hdr.h1.value & (hdr.h2.value | hdr.h3.value))); // underflow protection

    }
    table t1 {
        key = {
            hdr.h0.value: exact;
        }
        actions = {
           validate_h1;
           drop_;
        }
    }
    table t2 {
        key = {
            hdr.h0.value: exact;
        }
        actions = {
           validate_h2;
           drop_;
        }
    }
    table t3 {
        key = {
            hdr.h0.value: exact;
        }
        actions = {
            validate_h3;
            drop_;
        }
    }
    table t4 {
       key = {
         hdr.h0.value: exact;
       }
       actions = {
         use_h1_h2_h3;
         drop_;
      }
    }
    apply {
      hdr.h1.setInvalid();
      hdr.h2.setInvalid();
      hdr.h3.setInvalid();
      hdr.h4.setInvalid();
      t1.apply();
      t2.apply();
      t3.apply();
      t4.apply();
      standard_metadata.egress_spec = 9w511;
    }
}

control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {}
}

control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
    }
}

control verifyChecksum(inout headers hdr, inout metadata meta) {
    apply {}
}

control computeChecksum(inout headers hdr, inout metadata meta) {
    apply {}
}

V1Switch(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;

