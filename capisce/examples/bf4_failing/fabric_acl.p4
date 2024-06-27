#include <core.p4>
#define V1MODEL_VERSION 20180101
#include <v1model.p4>

#define GTPU_EXT_PSC_TYPE_DL 4w0
#define GTPU_EXT_PSC_TYPE_UL 4w1
typedef bit<3> fwd_type_t;
typedef bit<32> next_id_t;
typedef bit<20> mpls_label_t;
typedef bit<9> port_num_t;
typedef bit<48> mac_addr_t;
typedef bit<16> mcast_group_id_t;
typedef bit<12> vlan_id_t;
typedef bit<32> ipv4_addr_t;
typedef bit<16> l4_port_t;
typedef bit<4> slice_id_t;
typedef bit<2> tc_t;
typedef bit<6> slice_tc_t;
#define DEFAULT_SLICE_ID 4w0
#define DEFAULT_TC 2w0
typedef bit<2> direction_t;
typedef bit<8> spgw_interface_t;
typedef bit<1> pcc_gate_status_t;
typedef bit<32> sdf_rule_id_t;
typedef bit<32> pcc_rule_id_t;
typedef bit<32> far_id_t;
typedef bit<32> pdr_ctr_id_t;
typedef bit<32> teid_t;
typedef bit<6> qfi_t;
typedef bit<5> qid_t;
#define SPGW_IFACE_UNKNOWN 8w0
#define SPGW_IFACE_ACCESS 8w1
#define SPGW_IFACE_CORE 8w2
#define SPGW_IFACE_FROM_DBUF 8w3
typedef bit<2> port_type_t;
#define PORT_TYPE_UNKNOWN 2w0x0
#define PORT_TYPE_EDGE 2w0x1
#define PORT_TYPE_INFRA 2w0x2
#define PORT_TYPE_INTERNAL 2w0x3
#define ETHERTYPE_QINQ 16w0x88a8
#define ETHERTYPE_QINQ_NON_STD 16w0x9100
#define ETHERTYPE_VLAN 16w0x8100
#define ETHERTYPE_MPLS 16w0x8847
#define ETHERTYPE_MPLS_MULTICAST 16w0x8848
#define ETHERTYPE_IPV4 16w0x800
#define ETHERTYPE_IPV6 16w0x86dd
#define ETHERTYPE_ARP 16w0x806
#define ETHERTYPE_PPPOED 16w0x8863
#define ETHERTYPE_PPPOES 16w0x8864
#define PPPOE_PROTOCOL_IP4 16w0x21
#define PPPOE_PROTOCOL_IP6 16w0x57
#define PPPOE_PROTOCOL_MPLS 16w0x281
#define PROTO_ICMP 8w1
#define PROTO_TCP 8w6
#define PROTO_UDP 8w17
#define PROTO_ICMPV6 8w58
#define IPV4_MIN_IHL 4w5
#define FWD_BRIDGING 3w0
#define FWD_MPLS 3w1
#define FWD_IPV4_UNICAST 3w2
#define FWD_IPV4_MULTICAST 3w3
#define FWD_IPV6_UNICAST 3w4
#define FWD_IPV6_MULTICAST 3w5
#define FWD_UNKNOWN 3w7
#define DEFAULT_VLAN_ID 12w4094
#define DEFAULT_MPLS_TTL 8w64
#define DEFAULT_IPV4_TTL 8w64
#define INT_DSCP 8w0x1
#define INT_HEADER_LEN_WORDS 8w4
#define INT_HEADER_LEN_BYTES 8w16
#define CPU_MIRROR_SESSION_ID 8w250
#define REPORT_MIRROR_SESSION_ID 32w500
#define NPROTO_ETHERNET 4w0
#define NPROTO_TELEMETRY_DROP_HEADER 4w1
#define NPROTO_TELEMETRY_SWITCH_LOCAL_HEADER 4w2
#define HW_ID 6w1
#define REPORT_FIXED_HEADER_LEN 8w12
#define DROP_REPORT_HEADER_LEN 8w12
#define LOCAL_REPORT_HEADER_LEN 8w16
#define ETH_HEADER_LEN 8w14
#define IPV4_MIN_HEAD_LEN 8w20
#define UDP_HEADER_LEN 8w8
action nop() {
    NoAction();
}
struct int_metadata_t {
    bool    source;
    bool    transit;
    bool    sink;
    bit<32> switch_id;
    bit<8>  new_words;
    bit<16> new_bytes;
    bit<32> ig_tstamp;
    bit<32> eg_tstamp;
}

header int_header_t {
    bit<2>  ver;
    bit<2>  rep;
    bit<1>  c;
    bit<1>  e;
    bit<5>  rsvd1;
    bit<5>  ins_cnt;
    bit<8>  max_hop_cnt;
    bit<8>  total_hop_cnt;
    bit<4>  instruction_mask_0003;
    bit<4>  instruction_mask_0407;
    bit<4>  instruction_mask_0811;
    bit<4>  instruction_mask_1215;
    bit<16> rsvd2;
}

header intl4_shim_t {
    bit<8> int_type;
    bit<8> rsvd1;
    bit<8> len_words;
    bit<8> rsvd2;
}

header intl4_tail_t {
    bit<8>  next_proto;
    bit<16> dest_port;
    bit<2>  padding;
    bit<6>  dscp;
}

@controller_header("packet_in") header packet_in_header_t {
    port_num_t ingress_port;
    bit<7>     _pad;
}

@controller_header("packet_out") header packet_out_header_t {
    port_num_t egress_port;
    bit<1>     do_forwarding;
    bit<6>     _pad;
}

header ethernet_t {
    mac_addr_t dst_addr;
    mac_addr_t src_addr;
}

header eth_type_t {
    bit<16> value;
}

header vlan_tag_t {
    bit<16>   eth_type;
    bit<3>    pri;
    bit<1>    cfi;
    vlan_id_t vlan_id;
}

header mpls_t {
    bit<20> label;
    bit<3>  tc;
    bit<1>  bos;
    bit<8>  ttl;
}

header pppoe_t {
    bit<4>  version;
    bit<4>  type_id;
    bit<8>  code;
    bit<16> session_id;
    bit<16> length;
    bit<16> protocol;
}

header ipv4_t {
    bit<4>  version;
    bit<4>  ihl;
    bit<6>  dscp;
    bit<2>  ecn;
    bit<16> total_len;
    bit<16> identification;
    bit<3>  flags;
    bit<13> frag_offset;
    bit<8>  ttl;
    bit<8>  protocol;
    bit<16> hdr_checksum;
    bit<32> src_addr;
    bit<32> dst_addr;
}

header ipv6_t {
    bit<4>   version;
    bit<8>   traffic_class;
    bit<20>  flow_label;
    bit<16>  payload_len;
    bit<8>   next_hdr;
    bit<8>   hop_limit;
    bit<128> src_addr;
    bit<128> dst_addr;
}

header tcp_t {
    bit<16> sport;
    bit<16> dport;
    bit<32> seq_no;
    bit<32> ack_no;
    bit<4>  data_offset;
    bit<3>  res;
    bit<3>  ecn;
    bit<6>  ctrl;
    bit<16> window;
    bit<16> checksum;
    bit<16> urgent_ptr;
}

header udp_t {
    bit<16> sport;
    bit<16> dport;
    bit<16> len;
    bit<16> checksum;
}

header icmp_t {
    bit<8>  icmp_type;
    bit<8>  icmp_code;
    bit<16> checksum;
    bit<16> identifier;
    bit<16> sequence_number;
    bit<64> timestamp;
}

header gtpu_t {
    bit<3>  version;
    bit<1>  pt;
    bit<1>  spare;
    bit<1>  ex_flag;
    bit<1>  seq_flag;
    bit<1>  npdu_flag;
    bit<8>  msgtype;
    bit<16> msglen;
    teid_t  teid;
}

header gtpu_options_t {
    bit<16> seq_num;
    bit<8>  n_pdu_num;
    bit<8>  next_ext;
}

header gtpu_ext_psc_t {
    bit<8> len;
    bit<4> type;
    bit<4> spare0;
    bit<1> ppp;
    bit<1> rqi;
    qfi_t  qfi;
    bit<8> next_ext;
}

struct lookup_metadata_t {
    bool      is_ipv4;
    bit<32>   ipv4_src;
    bit<32>   ipv4_dst;
    bit<8>    ip_proto;
    l4_port_t l4_sport;
    l4_port_t l4_dport;
    bit<8>    icmp_type;
    bit<8>    icmp_code;
}

struct fabric_metadata_t {
    lookup_metadata_t lkp;
    bit<16>           ip_eth_type;
    vlan_id_t         vlan_id;
    bit<3>            vlan_pri;
    bit<1>            vlan_cfi;
    mpls_label_t      mpls_label;
    bit<8>            mpls_ttl;
    bool              skip_forwarding;
    bool              skip_next;
    fwd_type_t        fwd_type;
    next_id_t         next_id;
    bool              is_multicast;
    bool              is_controller_packet_out;
    bit<8>            ip_proto;
    bit<16>           l4_sport;
    bit<16>           l4_dport;
    bit<32>           ipv4_src_addr;
    bit<32>           ipv4_dst_addr;
    slice_id_t        slice_id;
    bit<2>            packet_color;
    tc_t              tc;
    bit<6>            dscp;
    port_type_t       port_type;
}

struct parsed_headers_t {
    ethernet_t          ethernet;
    vlan_tag_t          vlan_tag;
    vlan_tag_t          inner_vlan_tag;
    eth_type_t          eth_type;
    mpls_t              mpls;
    gtpu_t              gtpu;
    gtpu_options_t      gtpu_options;
    gtpu_ext_psc_t      gtpu_ext_psc;
    ipv4_t              inner_ipv4;
    udp_t               inner_udp;
    tcp_t               inner_tcp;
    icmp_t              inner_icmp;
    ipv4_t              ipv4;
    tcp_t               tcp;
    udp_t               udp;
    icmp_t              icmp;
    packet_out_header_t packet_out;
    packet_in_header_t  packet_in;
}


control Acl(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_md, inout standard_metadata_t standard_metadata) {
    direct_counter(CounterType.packets_and_bytes) acl_counter;
    action set_next_id_acl(next_id_t next_id) {
        fabric_md.next_id = next_id;
        acl_counter.count();
    }
    action punt_to_cpu() {
        standard_metadata.egress_spec = 9w510;
        fabric_md.skip_next = true;
        acl_counter.count();
    }
    action set_clone_session_id(bit<32> clone_id) {
        clone3(CloneType.I2E, clone_id, { standard_metadata.ingress_port });
        acl_counter.count();
    }
    action drop() {
        mark_to_drop(standard_metadata);
        fabric_md.skip_next = true;
        acl_counter.count();
    }
    action nop_acl() {
        acl_counter.count();
    }
    table acl {
        key = {
            standard_metadata.ingress_port: ternary @name("ig_port") ;
            hdr.ethernet.dst_addr         : ternary @name("eth_dst") ;
            hdr.ethernet.src_addr         : ternary @name("eth_src") ;
            hdr.vlan_tag.vlan_id          : ternary @name("vlan_id") ;
            hdr.eth_type.value            : ternary @name("eth_type") ;
            fabric_md.lkp.ipv4_src        : ternary @name("ipv4_src") ;
            fabric_md.lkp.ipv4_dst        : ternary @name("ipv4_dst") ;
            fabric_md.lkp.ip_proto        : ternary @name("ip_proto") ;
            hdr.icmp.icmp_type            : ternary @name("icmp_type") ;
            hdr.icmp.icmp_code            : ternary @name("icmp_code") ;
            fabric_md.lkp.l4_sport        : ternary @name("l4_sport") ;
            fabric_md.lkp.l4_dport        : ternary @name("l4_dport") ;
            fabric_md.port_type           : ternary @name("port_type") ;
        }
        actions = {
            set_next_id_acl;
            punt_to_cpu;
            set_clone_session_id;
            drop;
            nop_acl;
        }
        const default_action = nop_acl();
        size = 1024;
        counters = acl_counter;
    }
    apply {
        acl.apply();
    }
}

control FabricComputeChecksum(inout parsed_headers_t hdr, inout fabric_metadata_t meta) {
    apply {
        update_checksum(hdr.ipv4.isValid(), { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.dscp, hdr.ipv4.ecn, hdr.ipv4.total_len, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.frag_offset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.src_addr, hdr.ipv4.dst_addr }, hdr.ipv4.hdr_checksum, HashAlgorithm.csum16);
    }
}

control FabricVerifyChecksum(inout parsed_headers_t hdr, inout fabric_metadata_t meta) {
    apply {
        verify_checksum(hdr.ipv4.isValid(), { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.dscp, hdr.ipv4.ecn, hdr.ipv4.total_len, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.frag_offset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.src_addr, hdr.ipv4.dst_addr }, hdr.ipv4.hdr_checksum, HashAlgorithm.csum16);
    }
}

parser FabricParser(packet_in packet, out parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
    bit<6> last_ipv4_dscp = 6w0;
    state start {
        transition select(standard_metadata.ingress_port) {
            9w510: check_packet_out;
            default: parse_ethernet;
        }
    }
    state check_packet_out {
        // packet_out_header_t tmp = packet.lookahead<packet_out_header_t>();
        // transition select(tmp.do_forwarding) {
        transition select((packet.lookahead<bit<1>>()[0:0])) {
            1w0: parse_packet_out_and_accept;
            default: strip_packet_out;
        }
    }
    state parse_packet_out_and_accept {
        packet.extract(hdr.packet_out);
        transition accept;
    }
    state strip_packet_out {
        // packet.advance(2 * 8);
        transition parse_ethernet;
    }
    state parse_ethernet {
        packet.extract(hdr.ethernet);
        // transition accept;
        fabric_metadata.vlan_id = DEFAULT_VLAN_ID;
        transition select((packet.lookahead<bit<16>>())[15:0]) {
            ETHERTYPE_QINQ: parse_vlan_tag;
            ETHERTYPE_QINQ_NON_STD: parse_vlan_tag;
            ETHERTYPE_VLAN: parse_vlan_tag;
            default: parse_eth_type;
        }
    }
    state parse_vlan_tag {
        packet.extract(hdr.vlan_tag);
        transition select((packet.lookahead<bit<16>>())[15:0]) {
            ETHERTYPE_VLAN: parse_inner_vlan_tag;
            default: parse_eth_type;
        }
    }
    state parse_inner_vlan_tag {
        packet.extract(hdr.inner_vlan_tag);
        transition parse_eth_type;
    }
    state parse_eth_type {
        packet.extract(hdr.eth_type);
        transition select(hdr.eth_type.value) {
            ETHERTYPE_MPLS: parse_mpls;
            ETHERTYPE_IPV4: parse_ipv4;
            default: accept;
        }
    }
    state parse_mpls {
        packet.extract(hdr.mpls);
        fabric_metadata.mpls_label = hdr.mpls.label;
        fabric_metadata.mpls_ttl = hdr.mpls.ttl;
        transition select((packet.lookahead<bit<4>>())[3:0]) {
            4w4: parse_ipv4;
            default: parse_ethernet;
        }
    }
    state parse_ipv4 {
        packet.extract(hdr.ipv4);
        fabric_metadata.ip_proto = hdr.ipv4.protocol;
        fabric_metadata.ip_eth_type = ETHERTYPE_IPV4;
        fabric_metadata.ipv4_src_addr = hdr.ipv4.src_addr;
        fabric_metadata.ipv4_dst_addr = hdr.ipv4.dst_addr;
        last_ipv4_dscp = hdr.ipv4.dscp;
        transition select(hdr.ipv4.protocol) {
            PROTO_TCP: parse_tcp;
            PROTO_UDP: parse_udp;
            PROTO_ICMP: parse_icmp;
            default: accept;
        }
    }
    state parse_tcp {
        packet.extract(hdr.tcp);
        fabric_metadata.l4_sport = hdr.tcp.sport;
        fabric_metadata.l4_dport = hdr.tcp.dport;
        transition accept;
    }
    state parse_udp {
        packet.extract(hdr.udp);
        fabric_metadata.l4_sport = hdr.udp.sport;
        fabric_metadata.l4_dport = hdr.udp.dport;
        // gtpu_t gtpu = packet.lookahead<gtpu_t>();
        // transition select(hdr.udp.dport, gtpu.version, gtpu.msgtype) {
        //     (16w2152, 3w0x1, 8w0xff): parse_gtpu;
        //     default: accept;
        // }
        transition accept;
    }
    state parse_icmp {
        packet.extract(hdr.icmp);
        transition accept;
    }
    state parse_gtpu {
        packet.extract(hdr.gtpu);
        transition select(hdr.gtpu.ex_flag, hdr.gtpu.seq_flag, hdr.gtpu.npdu_flag) {
            (1w0, 1w0, 1w0): parse_inner_ipv4;
            default: parse_gtpu_options;
        }
    }
    state parse_gtpu_options {
        packet.extract(hdr.gtpu_options);
        bit<8> gtpu_ext_len = packet.lookahead<bit<8>>();
        transition select(hdr.gtpu_options.next_ext, gtpu_ext_len) {
            (8w0x85, 8w1): parse_gtpu_ext_psc;
            default: accept;
        }
    }
    state parse_gtpu_ext_psc {
        packet.extract(hdr.gtpu_ext_psc);
        transition select(hdr.gtpu_ext_psc.next_ext) {
            8w0x0: parse_inner_ipv4;
            default: accept;
        }
    }
    state parse_inner_ipv4 {
        packet.extract(hdr.inner_ipv4);
        last_ipv4_dscp = hdr.inner_ipv4.dscp;
        transition select(hdr.inner_ipv4.protocol) {
            PROTO_TCP: parse_inner_tcp;
            PROTO_UDP: parse_inner_udp;
            PROTO_ICMP: parse_inner_icmp;
            default: accept;
        }
    }
    state parse_inner_udp {
        packet.extract(hdr.inner_udp);
        transition accept;
    }
    state parse_inner_tcp {
        packet.extract(hdr.inner_tcp);
        transition accept;
    }
    state parse_inner_icmp {
        packet.extract(hdr.inner_icmp);
        transition accept;
    }
}

control FabricDeparser(packet_out packet, in parsed_headers_t hdr) {
    apply {
        packet.emit(hdr.packet_in);
        packet.emit(hdr.ethernet);
        packet.emit(hdr.vlan_tag);
        packet.emit(hdr.inner_vlan_tag);
        packet.emit(hdr.eth_type);
        packet.emit(hdr.mpls);
        packet.emit(hdr.ipv4);
        packet.emit(hdr.tcp);
        packet.emit(hdr.udp);
        packet.emit(hdr.icmp);
        packet.emit(hdr.gtpu);
        packet.emit(hdr.gtpu_options);
        packet.emit(hdr.gtpu_ext_psc);
        packet.emit(hdr.inner_ipv4);
        packet.emit(hdr.inner_tcp);
        packet.emit(hdr.inner_udp);
        packet.emit(hdr.inner_icmp);
    }
}

control FabricIngress(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
    Acl() acl;
    apply {
          assume(hdr.packet_out.isValid() == false);
          hopen (8w1, hdr.ethernet.isValid() && hdr.eth_type.isValid()); //&& (fabric_metadata.skip_forwarding == true || hdr.icmp.isValid()));
          acl.apply(hdr, fabric_metadata, standard_metadata);
          hclose(8w1, hdr.ethernet.isValid() && hdr.eth_type.isValid());
          standard_metadata.egress_spec = 9w511;
    }
}

control FabricEgress(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
    apply {
        standard_metadata.egress_spec = 9w511;
    }
}

V1Switch(FabricParser(), FabricVerifyChecksum(), FabricIngress(), FabricEgress(), FabricComputeChecksum(), FabricDeparser()) main;
