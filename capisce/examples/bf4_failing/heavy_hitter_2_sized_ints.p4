#include <core.p4>
#include <v1model.p4>

struct custom_metadata_t {
    bit<32> nhop_ipv4;
    bit<16> hash_val1;
    bit<16> hash_val2;
    bit<16> count_val1;
    bit<16> count_val2;
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

header tcp_t {
    bit<16> srcPort;
    bit<16> dstPort;
    bit<32> seqNo;
    bit<32> ackNo;
    bit<4>  dataOffset;
    bit<3>  res;
    bit<3>  ecn;
    bit<6>  ctrl;
    bit<16> window;
    bit<16> checksum;
    bit<16> urgentPtr;
}

struct metadata {
    custom_metadata_t custom_metadata;
}

struct headers {

    ethernet_t ethernet;
    ipv4_t     ipv4;
    tcp_t      tcp;
}

parser ParserImpl(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    state parse_ethernet {
        packet.extract(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            16w0x800: parse_ipv4;
            default: accept;
        }
    }
    state parse_ipv4 {
        packet.extract(hdr.ipv4);
        transition select(hdr.ipv4.protocol) {
            8w6: parse_tcp;
            default: accept;
        }
    }
    state parse_tcp {
        packet.extract(hdr.tcp);
        transition accept;
    }
    state start {
        transition parse_ethernet;
    }
}

control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    action rewrite_mac(bit<48> smac) {
        hdr.ethernet.srcAddr = smac;
    }
    action _drop() {
        mark_to_drop();
    }
    table send_frame {
        actions = {
            rewrite_mac;
            _drop;
        }
        key = {
            standard_metadata.egress_port: exact;
        }
        size = 256;
    }
    apply {
        send_frame.apply();
    }
}

control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    register<bit<16>>(32w16) heavy_hitter_counter1;
    register<bit<16>>(32w16) heavy_hitter_counter2;

    action _drop() {
        mark_to_drop();
    }

    action set_dmac(bit<48> dmac) {
        hdr.ethernet.dstAddr = dmac;
    }

    action set_nhop(bit<32> nhop_ipv4, bit<9> port) {
        meta.custom_metadata.nhop_ipv4 = nhop_ipv4;
        standard_metadata.egress_spec = port;
        hdr.ipv4.ttl = hdr.ipv4.ttl + 8w255;
    }
    action set_heavy_hitter_count() {
        // Count the hash 1 for indexing
        hash(meta.custom_metadata.hash_val1, HashAlgorithm.csum16, (bit<16>)16w0, { hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, hdr.ipv4.protocol, hdr.tcp.srcPort, hdr.tcp.dstPort }, (bit<32>)32w16);
        // Read the value in the register with that index
        heavy_hitter_counter1.read(meta.custom_metadata.count_val1, (bit<32>)meta.custom_metadata.hash_val1);
        // Incremet the value with 1
        meta.custom_metadata.count_val1 = meta.custom_metadata.count_val1 + 16w1;
        // Write the value back to the register with that index
        heavy_hitter_counter1.write((bit<32>)meta.custom_metadata.hash_val1, (bit<16>)meta.custom_metadata.count_val1);
        // Count the hash 2 for another indexing, similar to the first hash
        hash(meta.custom_metadata.hash_val2, HashAlgorithm.crc16, (bit<16>)16w0, { hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, hdr.ipv4.protocol, hdr.tcp.srcPort, hdr.tcp.dstPort }, (bit<32>)32w16);
        heavy_hitter_counter2.read(meta.custom_metadata.count_val2, (bit<32>)meta.custom_metadata.hash_val2);
        meta.custom_metadata.count_val2 = meta.custom_metadata.count_val2 + 16w1;
        heavy_hitter_counter2.write((bit<32>)meta.custom_metadata.hash_val2, (bit<16>)meta.custom_metadata.count_val2);
    }

    table drop_heavy_hitter_table {
        actions = {
            _drop;
        }
        size = 1;
    }
    
    table forward {
        actions = {
            set_dmac;
            _drop;
        }
        key = {
            meta.custom_metadata.nhop_ipv4: exact;
        }
        size = 512;
    }
    
    table ipv4_lpm {
        actions = {
            set_nhop; // Set next hop
            _drop;
        }
        key = {
            hdr.ipv4.dstAddr: lpm;
        }
        size = 1024;
    }
    
    table set_heavy_hitter_count_table {
        actions = {
            set_heavy_hitter_count;
        }
        size = 1;
    }

    apply {
        assume(hdr.ipv4.isValid() && hdr.tcp.isValid());
        set_heavy_hitter_count_table.apply();

        if (meta.custom_metadata.count_val1 > 16w100 && meta.custom_metadata.count_val2 > 16w100) {
            drop_heavy_hitter_table.apply();
        }
        else {
            ipv4_lpm.apply();
            forward.apply();
        }
    }
}

control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.ethernet);
        packet.emit(hdr.ipv4);
        packet.emit(hdr.tcp);
    }
}

control verifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
        verify_checksum(true, { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
    }
}

control computeChecksum(inout headers hdr, inout metadata meta) {
    apply {
        update_checksum(true, { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
    }
}

V1Switch(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;

