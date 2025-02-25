/* -*- P4_16 -*- */

#include <core.p4>
#include <v1model.p4>

/*************************************************************************
 ***********************  C O N S T A N T S  *****************************
 *************************************************************************/
      /*  Define the useful global constants for your program */
// const bit<16> ETHERTYPE_IPV4 = 0x0800;
// const bit<16> ETHERTYPE_ARP  = 0x0806;
// const bit<8>  IPPROTO_ICMP   = 0x01;

/*************************************************************************
 ***********************  H E A D E R S  *********************************
 *************************************************************************/
        /*  Define the headers the program will recognize */

/*
 * Standard ethernet header 
 */
typedef bit<48>  mac_addr_t;
typedef bit<32>  ipv4_addr_t;
typedef bit<9>   port_id_t; 

header ethernet_t {
    mac_addr_t dstAddr;
    mac_addr_t srcAddr;
    bit<16>    etherType;
}

header ipv4_t {
    bit<4>       version;
    bit<4>       ihl;
    bit<8>       diffserv;
    bit<16>      totalLen;
    bit<16>      identification;
    bit<3>       flags;
    bit<13>      fragOffset;
    bit<8>       ttl;
    bit<8>       protocol;
    bit<16>      hdrChecksum;
    ipv4_addr_t  srcAddr;
    ipv4_addr_t  dstAddr;
}

// const bit<16> ARP_HTYPE_ETHERNET = 0x0001;
// const bit<16> ARP_PTYPE_IPV4     = 0x0800;
// const bit<8>  ARP_HLEN_ETHERNET   = 6;
// const bit<8>  ARP_PLEN_IPV4      = 4;
// const bit<16> ARP_OPER_REQUEST   = 1;
// const bit<16> ARP_OPER_REPLY     = 2;

header arp_t {
    bit<16> htype;
    bit<16> ptype;
    bit<8>  hlen;
    bit<8>  plen;
    bit<16> oper;
}

header arp_ipv4_t {
    mac_addr_t  sha;
    ipv4_addr_t spa;
    mac_addr_t  tha;
    ipv4_addr_t tpa;
}

// const bit<8> ICMP_ECHO_REQUEST = 8;
// const bit<8> ICMP_ECHO_REPLY   = 0;

header icmp_t {
    bit<8>  type;
    bit<8>  code;
    bit<16> checksum;
}
    
/* Assemble headers in a single struct */
struct my_headers_t {
    ethernet_t   ethernet;
    arp_t        arp;
    arp_ipv4_t   arp_ipv4;
    ipv4_t       ipv4;
    icmp_t       icmp;
}

/*************************************************************************
 ***********************  M E T A D A T A  *******************************
 *************************************************************************/
        /*  Define the global metadata for your program */

struct my_metadata_t {
    ipv4_addr_t dst_ipv4;
    mac_addr_t  mac_da;
    mac_addr_t  mac_sa;
    port_id_t   egress_port;
    mac_addr_t  my_mac;
}

/*************************************************************************
 ***********************  P A R S E R  ***********************************
 *************************************************************************/
parser MyParser(
    packet_in             packet,
    out   my_headers_t    hdr,
    inout my_metadata_t   meta,
    inout standard_metadata_t standard_metadata)
{
    state start {
        packet.extract(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            16w0x0800 : parse_ipv4;
            16w0x0806  : parse_arp;
            default        : accept;
        }
    }

    state parse_arp {
        packet.extract(hdr.arp);
        transition select(hdr.arp.htype, hdr.arp.ptype,
                          hdr.arp.hlen,  hdr.arp.plen) {
            (16w0x0001, 16w0x0800,
             8w6,  8w4) : parse_arp_ipv4;
            default : accept;
        }
    }

    state parse_arp_ipv4 {
        packet.extract(hdr.arp_ipv4);
        meta.dst_ipv4 = hdr.arp_ipv4.tpa;
        transition accept;
    }            

    state parse_ipv4 {
        packet.extract(hdr.ipv4);
        meta.dst_ipv4 = hdr.ipv4.dstAddr;
        transition select(hdr.ipv4.protocol) {
            8w0x01 : parse_icmp;
            default      : accept;
        }
    }

    state parse_icmp {
        packet.extract(hdr.icmp);
        transition accept;
    }    
}

/*************************************************************************
 ************   C H E C K S U M    V E R I F I C A T I O N   *************
 *************************************************************************/
control MyVerifyChecksum(
    inout my_headers_t   hdr,
    inout my_metadata_t  meta)
{
    apply {     }
}

/*************************************************************************
 **************  I N G R E S S   P R O C E S S I N G   *******************
 *************************************************************************/
control MyIngress(
    inout my_headers_t     hdr,
    inout my_metadata_t    meta,
    inout standard_metadata_t  standard_metadata)
{
    action drop() {
        mark_to_drop();
        // exit;
    }
    
    action set_dst_info(mac_addr_t mac_da,
                        mac_addr_t mac_sa,
                        port_id_t  egress_port)
    {
        meta.mac_da      = mac_da;
        meta.mac_sa      = mac_sa;
        meta.egress_port = egress_port;
    }
    
    table ipv4_lpm {
        key     = { meta.dst_ipv4 : lpm; }
        actions = { set_dst_info; drop;  }
        default_action = drop();
    }

    action forward_ipv4() {
        hdr.ethernet.dstAddr = meta.mac_da;
        hdr.ethernet.srcAddr = meta.mac_sa;
        hdr.ipv4.ttl         = hdr.ipv4.ttl - 8w1;
        
        standard_metadata.egress_spec = meta.egress_port;
    }

    action send_arp_reply() {
        hdr.ethernet.dstAddr = hdr.arp_ipv4.sha;
        hdr.ethernet.srcAddr = meta.mac_da;
        
        hdr.arp.oper         = 16w2;
        
        hdr.arp_ipv4.tha     = hdr.arp_ipv4.sha;
        hdr.arp_ipv4.tpa     = hdr.arp_ipv4.spa;
        hdr.arp_ipv4.sha     = meta.mac_da;
        hdr.arp_ipv4.spa     = meta.dst_ipv4;

        standard_metadata.egress_spec = standard_metadata.ingress_port;
    }

    action send_icmp_reply() {
        mac_addr_t   tmp_mac;
        ipv4_addr_t  tmp_ip;

        tmp_mac              = hdr.ethernet.dstAddr;
        hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
        hdr.ethernet.srcAddr = tmp_mac;

        tmp_ip               = hdr.ipv4.dstAddr;
        hdr.ipv4.dstAddr     = hdr.ipv4.srcAddr;
        hdr.ipv4.srcAddr     = tmp_ip;

        hdr.icmp.type        = 8w0;
        hdr.icmp.checksum    = 16w0; // For now

        standard_metadata.egress_spec = standard_metadata.ingress_port;
    }

    table forward {
        key = {
            hdr.arp.isValid()      : exact;
            hdr.arp.oper           : ternary;
            hdr.arp_ipv4.isValid() : exact;
            hdr.ipv4.isValid()     : exact;
            hdr.icmp.isValid()     : exact;
            hdr.icmp.type          : ternary;
        }
        actions = {
            forward_ipv4;
            send_arp_reply;
            send_icmp_reply;
            drop;
        }
        const default_action = drop();
        const entries = {
            ( true, 16w1, true, false, false, _  ) :
                                                         send_arp_reply();
            ( false, _,               false, true, false, _  ) :
                                                         forward_ipv4();
            ( false, _,               false, true, true, 8w8 ) :
                                                         send_icmp_reply();
        }
    }
    
    apply {
        meta.my_mac = 48w0x000102030405;
        ipv4_lpm.apply();
        forward.apply();
    }
}

/*************************************************************************
 ****************  E G R E S S   P R O C E S S I N G   *******************
 *************************************************************************/
control MyEgress(
    inout my_headers_t        hdr,
    inout my_metadata_t       meta,
    inout standard_metadata_t standard_metadata) {
    apply {    }
}

/*************************************************************************
 *************   C H E C K S U M    C O M P U T A T I O N   **************
 *************************************************************************/
control MyComputeChecksum(
    inout my_headers_t  hdr,
    inout my_metadata_t meta)
{
    apply {   }
}

/*************************************************************************
 ***********************  D E P A R S E R  *******************************
 *************************************************************************/
control MyDeparser(
    packet_out      packet,
    in my_headers_t hdr)
{
    apply {
        packet.emit(hdr.ethernet);
        /* ARP Case */
        packet.emit(hdr.arp);
        packet.emit(hdr.arp_ipv4);
        /* IPv4 case */
        packet.emit(hdr.ipv4);
        packet.emit(hdr.icmp);
    }
}

V1Switch(
    MyParser(),
    MyVerifyChecksum(),
    MyIngress(),
    MyEgress(),
    MyComputeChecksum(),
    MyDeparser()
) main;
