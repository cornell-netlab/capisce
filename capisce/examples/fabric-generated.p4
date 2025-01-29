 parse_result:=(_ bv0 1);
 exited:=(_ bv0 1);
 hdr.eth_type.isValid:=(_ bv0 1);
 hdr.ethernet.isValid:=(_ bv0 1);
 hdr.gtpu.isValid:=(_ bv0 1);
 hdr.gtpu_ext_psc.isValid:=(_ bv0 1);
 hdr.gtpu_options.isValid:=(_ bv0 1);
 hdr.icmp.isValid:=(_ bv0 1);
 hdr.inner_icmp.isValid:=(_ bv0 1);
 hdr.inner_ipv4.isValid:=(_ bv0 1);
 hdr.inner_tcp.isValid:=(_ bv0 1);
 hdr.inner_udp.isValid:=(_ bv0 1);
 hdr.inner_vlan_tag.isValid:=(_ bv0 1);
 hdr.ipv4.isValid:=(_ bv0 1);
 hdr.mpls.isValid:=(_ bv0 1);
 hdr.packet_out.isValid:=(_ bv0 1);
 hdr.tcp.isValid:=(_ bv0 1);
 hdr.udp.isValid:=(_ bv0 1);
 hdr.vlan_tag.isValid:=(_ bv0 1);
 fabric_metadata.is_controller_packet_out:=(_ bv0 1);
 hdr.packet_out.isValid:=(_ bv0 1);
 last_ipv4_dscp:=(_ bv0 6);
{
   assume (not(= (_ bv510 9) standard_metadata.ingress_port));
   fabric_metadata.vlan_id:=(_ bv4094 12);
   hdr.ethernet.isValid:=(_ bv1 1);
  {
     assume (not(= (_ bv34984 16) look_eth));
    {
       assume (not(= (_ bv37120 16) look_eth));
      {
         assume (not(= (_ bv33024 16) look_eth));
         hdr.eth_type.isValid:=(_ bv1 1);
        {
           assume (not(= (_ bv34887 16) hdr.eth_type.value));
          {
             assume (not(= (_ bv2048 16) hdr.eth_type.value));
             parse_result:=(_ bv1 1)
          } [] {
             assume (= (_ bv2048 16) hdr.eth_type.value);
             hdr.ipv4.isValid:=(_ bv1 1);
             fabric_metadata.ip_proto:=hdr.ipv4.protocol;
             fabric_metadata.ip_eth_type:=(_ bv2048 16);
             fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
             fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
             last_ipv4_dscp:=hdr.ipv4.dscp;
            {
               assume (not(= (_ bv6 8) hdr.ipv4.protocol));
              {
                 assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                {
                   assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                   parse_result:=(_ bv1 1)
                } [] {
                   assume (= (_ bv1 8) hdr.ipv4.protocol);
                   hdr.icmp.isValid:=(_ bv1 1);
                   parse_result:=(_ bv1 1)
                }
              } [] {
                 assume (= (_ bv17 8) hdr.ipv4.protocol);
                 hdr.udp.isValid:=(_ bv1 1);
                 fabric_metadata.l4_sport:=hdr.udp.srcPort;
                 fabric_metadata.l4_dport:=hdr.udp.dstPort;
                {
                   assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                   parse_result:=(_ bv1 1)
                } [] {
                   assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                   hdr.gtpu.isValid:=(_ bv1 1);
                  {
                     assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                     hdr.gtpu_options.isValid:=(_ bv1 1);
                    {
                       assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                       hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                      {
                         assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                         hdr.inner_ipv4.isValid:=(_ bv1 1);
                         last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                        {
                           assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                          {
                             assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                            {
                               assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                               hdr.inner_icmp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                             hdr.inner_udp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                           hdr.inner_tcp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      }
                    }
                  } [] {
                     assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                     hdr.inner_ipv4.isValid:=(_ bv1 1);
                     last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                    {
                       assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                      {
                         assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                        {
                           assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                           hdr.inner_icmp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                         hdr.inner_udp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    } [] {
                       assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                       hdr.inner_tcp.isValid:=(_ bv1 1);
                       parse_result:=(_ bv1 1)
                    }
                  }
                }
              }
            } [] {
               assume (= (_ bv6 8) hdr.ipv4.protocol);
               hdr.tcp.isValid:=(_ bv1 1);
               fabric_metadata.l4_sport:=hdr.tcp.srcPort;
               fabric_metadata.l4_dport:=hdr.tcp.dstPort;
               parse_result:=(_ bv1 1)
            }
          }
        } [] {
           assume (= (_ bv34887 16) hdr.eth_type.value);
           hdr.mpls.isValid:=(_ bv1 1);
           fabric_metadata.mpls_label:=hdr.mpls.label;
           fabric_metadata.mpls_ttl:=hdr.mpls.ttl;
          {
             assume (not(= (_ bv4 4) look_mpls));
             fabric_metadata.vlan_id:=(_ bv4094 12);
             hdr.ethernet.isValid:=(_ bv1 1);
            {
               assume (not(= (_ bv34984 16) look_eth));
              {
                 assume (not(= (_ bv37120 16) look_eth));
                {
                   assume (not(= (_ bv33024 16) look_eth));
                   hdr.eth_type.isValid:=(_ bv1 1);
                  {
                     assume (not(= (_ bv34887 16) hdr.eth_type.value));
                    {
                       assume (not(= (_ bv2048 16) hdr.eth_type.value));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (= (_ bv2048 16) hdr.eth_type.value);
                       hdr.ipv4.isValid:=(_ bv1 1);
                       fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                       fabric_metadata.ip_eth_type:=(_ bv2048 16);
                       fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                       fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                       last_ipv4_dscp:=hdr.ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.ipv4.protocol);
                             hdr.icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.ipv4.protocol);
                           hdr.udp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.udp.srcPort;
                           fabric_metadata.l4_dport:=hdr.udp.dstPort;
                          {
                             assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                             hdr.gtpu.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                               hdr.gtpu_options.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                 hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                {
                                   assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                  {
                                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                         parse_result:=(_ bv1 1)
                                      } [] {
                                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_icmp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_udp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_tcp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                }
                              }
                            } [] {
                               assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                               hdr.inner_ipv4.isValid:=(_ bv1 1);
                               last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                              {
                                 assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_icmp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_udp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_tcp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            }
                          }
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.ipv4.protocol);
                         hdr.tcp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                         fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                         parse_result:=(_ bv1 1)
                      }
                    }
                  } [] {
                     assume (= (_ bv34887 16) hdr.eth_type.value);
                     parse_result:=(_ bv0 1)
                  }
                } [] {
                   assume (= (_ bv33024 16) look_eth);
                   hdr.vlan_tag.isValid:=(_ bv1 1);
                   hdr.vlan_tag.eth_type:=look_eth;
                  {
                     assume (not(= (_ bv33024 16) look_vlan));
                     hdr.eth_type.isValid:=(_ bv1 1);
                    {
                       assume (not(= (_ bv34887 16) hdr.eth_type.value));
                      {
                         assume (not(= (_ bv2048 16) hdr.eth_type.value));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv2048 16) hdr.eth_type.value);
                         hdr.ipv4.isValid:=(_ bv1 1);
                         fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                         fabric_metadata.ip_eth_type:=(_ bv2048 16);
                         fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                         fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                         last_ipv4_dscp:=hdr.ipv4.dscp;
                        {
                           assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                            {
                               assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv1 8) hdr.ipv4.protocol);
                               hdr.icmp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv17 8) hdr.ipv4.protocol);
                             hdr.udp.isValid:=(_ bv1 1);
                             fabric_metadata.l4_sport:=hdr.udp.srcPort;
                             fabric_metadata.l4_dport:=hdr.udp.dstPort;
                            {
                               assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                               hdr.gtpu.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                                 hdr.gtpu_options.isValid:=(_ bv1 1);
                                {
                                   assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                   hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                  {
                                     assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                     hdr.inner_ipv4.isValid:=(_ bv1 1);
                                     last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                    {
                                       assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                        {
                                           assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                           parse_result:=(_ bv1 1)
                                        } [] {
                                           assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                           hdr.inner_icmp.isValid:=(_ bv1 1);
                                           parse_result:=(_ bv1 1)
                                        }
                                      } [] {
                                         assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_udp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_tcp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  }
                                }
                              } [] {
                                 assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          }
                        } [] {
                           assume (= (_ bv6 8) hdr.ipv4.protocol);
                           hdr.tcp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                           fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                           parse_result:=(_ bv1 1)
                        }
                      }
                    } [] {
                       assume (= (_ bv34887 16) hdr.eth_type.value);
                       parse_result:=(_ bv0 1)
                    }
                  } [] {
                     assume (= (_ bv33024 16) look_vlan);
                     hdr.inner_vlan_tag.isValid:=(_ bv1 1);
                     hdr.inner_vlan_tag.eth_type:=look_vlan;
                     hdr.eth_type.isValid:=(_ bv1 1);
                    {
                       assume (not(= (_ bv34887 16) hdr.eth_type.value));
                      {
                         assume (not(= (_ bv2048 16) hdr.eth_type.value));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv2048 16) hdr.eth_type.value);
                         hdr.ipv4.isValid:=(_ bv1 1);
                         fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                         fabric_metadata.ip_eth_type:=(_ bv2048 16);
                         fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                         fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                         last_ipv4_dscp:=hdr.ipv4.dscp;
                        {
                           assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                            {
                               assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv1 8) hdr.ipv4.protocol);
                               hdr.icmp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv17 8) hdr.ipv4.protocol);
                             hdr.udp.isValid:=(_ bv1 1);
                             fabric_metadata.l4_sport:=hdr.udp.srcPort;
                             fabric_metadata.l4_dport:=hdr.udp.dstPort;
                            {
                               assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                               hdr.gtpu.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                                 hdr.gtpu_options.isValid:=(_ bv1 1);
                                {
                                   assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                   hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                  {
                                     assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                     hdr.inner_ipv4.isValid:=(_ bv1 1);
                                     last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                    {
                                       assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                        {
                                           assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                           parse_result:=(_ bv1 1)
                                        } [] {
                                           assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                           hdr.inner_icmp.isValid:=(_ bv1 1);
                                           parse_result:=(_ bv1 1)
                                        }
                                      } [] {
                                         assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_udp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_tcp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  }
                                }
                              } [] {
                                 assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          }
                        } [] {
                           assume (= (_ bv6 8) hdr.ipv4.protocol);
                           hdr.tcp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                           fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                           parse_result:=(_ bv1 1)
                        }
                      }
                    } [] {
                       assume (= (_ bv34887 16) hdr.eth_type.value);
                       parse_result:=(_ bv0 1)
                    }
                  }
                }
              } [] {
                 assume (= (_ bv37120 16) look_eth);
                 hdr.vlan_tag.isValid:=(_ bv1 1);
                 hdr.vlan_tag.eth_type:=look_eth;
                {
                   assume (not(= (_ bv33024 16) look_vlan));
                   hdr.eth_type.isValid:=(_ bv1 1);
                  {
                     assume (not(= (_ bv34887 16) hdr.eth_type.value));
                    {
                       assume (not(= (_ bv2048 16) hdr.eth_type.value));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (= (_ bv2048 16) hdr.eth_type.value);
                       hdr.ipv4.isValid:=(_ bv1 1);
                       fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                       fabric_metadata.ip_eth_type:=(_ bv2048 16);
                       fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                       fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                       last_ipv4_dscp:=hdr.ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.ipv4.protocol);
                             hdr.icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.ipv4.protocol);
                           hdr.udp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.udp.srcPort;
                           fabric_metadata.l4_dport:=hdr.udp.dstPort;
                          {
                             assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                             hdr.gtpu.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                               hdr.gtpu_options.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                 hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                {
                                   assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                  {
                                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                         parse_result:=(_ bv1 1)
                                      } [] {
                                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_icmp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_udp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_tcp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                }
                              }
                            } [] {
                               assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                               hdr.inner_ipv4.isValid:=(_ bv1 1);
                               last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                              {
                                 assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_icmp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_udp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_tcp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            }
                          }
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.ipv4.protocol);
                         hdr.tcp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                         fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                         parse_result:=(_ bv1 1)
                      }
                    }
                  } [] {
                     assume (= (_ bv34887 16) hdr.eth_type.value);
                     parse_result:=(_ bv0 1)
                  }
                } [] {
                   assume (= (_ bv33024 16) look_vlan);
                   hdr.inner_vlan_tag.isValid:=(_ bv1 1);
                   hdr.inner_vlan_tag.eth_type:=look_vlan;
                   hdr.eth_type.isValid:=(_ bv1 1);
                  {
                     assume (not(= (_ bv34887 16) hdr.eth_type.value));
                    {
                       assume (not(= (_ bv2048 16) hdr.eth_type.value));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (= (_ bv2048 16) hdr.eth_type.value);
                       hdr.ipv4.isValid:=(_ bv1 1);
                       fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                       fabric_metadata.ip_eth_type:=(_ bv2048 16);
                       fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                       fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                       last_ipv4_dscp:=hdr.ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.ipv4.protocol);
                             hdr.icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.ipv4.protocol);
                           hdr.udp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.udp.srcPort;
                           fabric_metadata.l4_dport:=hdr.udp.dstPort;
                          {
                             assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                             hdr.gtpu.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                               hdr.gtpu_options.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                 hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                {
                                   assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                  {
                                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                         parse_result:=(_ bv1 1)
                                      } [] {
                                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_icmp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_udp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_tcp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                }
                              }
                            } [] {
                               assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                               hdr.inner_ipv4.isValid:=(_ bv1 1);
                               last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                              {
                                 assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_icmp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_udp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_tcp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            }
                          }
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.ipv4.protocol);
                         hdr.tcp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                         fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                         parse_result:=(_ bv1 1)
                      }
                    }
                  } [] {
                     assume (= (_ bv34887 16) hdr.eth_type.value);
                     parse_result:=(_ bv0 1)
                  }
                }
              }
            } [] {
               assume (= (_ bv34984 16) look_eth);
               hdr.vlan_tag.isValid:=(_ bv1 1);
               hdr.vlan_tag.eth_type:=look_eth;
              {
                 assume (not(= (_ bv33024 16) look_vlan));
                 hdr.eth_type.isValid:=(_ bv1 1);
                {
                   assume (not(= (_ bv34887 16) hdr.eth_type.value));
                  {
                     assume (not(= (_ bv2048 16) hdr.eth_type.value));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (= (_ bv2048 16) hdr.eth_type.value);
                     hdr.ipv4.isValid:=(_ bv1 1);
                     fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                     fabric_metadata.ip_eth_type:=(_ bv2048 16);
                     fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                     fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                     last_ipv4_dscp:=hdr.ipv4.dscp;
                    {
                       assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                      {
                         assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv1 8) hdr.ipv4.protocol);
                           hdr.icmp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv17 8) hdr.ipv4.protocol);
                         hdr.udp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.udp.srcPort;
                         fabric_metadata.l4_dport:=hdr.udp.dstPort;
                        {
                           assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                           hdr.gtpu.isValid:=(_ bv1 1);
                          {
                             assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                             hdr.gtpu_options.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                               hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                              {
                                 assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          } [] {
                             assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                             hdr.inner_ipv4.isValid:=(_ bv1 1);
                             last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                            {
                               assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                              {
                                 assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_icmp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_udp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                               hdr.inner_tcp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          }
                        }
                      }
                    } [] {
                       assume (= (_ bv6 8) hdr.ipv4.protocol);
                       hdr.tcp.isValid:=(_ bv1 1);
                       fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                       fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                       parse_result:=(_ bv1 1)
                    }
                  }
                } [] {
                   assume (= (_ bv34887 16) hdr.eth_type.value);
                   parse_result:=(_ bv0 1)
                }
              } [] {
                 assume (= (_ bv33024 16) look_vlan);
                 hdr.inner_vlan_tag.isValid:=(_ bv1 1);
                 hdr.inner_vlan_tag.eth_type:=look_vlan;
                 hdr.eth_type.isValid:=(_ bv1 1);
                {
                   assume (not(= (_ bv34887 16) hdr.eth_type.value));
                  {
                     assume (not(= (_ bv2048 16) hdr.eth_type.value));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (= (_ bv2048 16) hdr.eth_type.value);
                     hdr.ipv4.isValid:=(_ bv1 1);
                     fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                     fabric_metadata.ip_eth_type:=(_ bv2048 16);
                     fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                     fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                     last_ipv4_dscp:=hdr.ipv4.dscp;
                    {
                       assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                      {
                         assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv1 8) hdr.ipv4.protocol);
                           hdr.icmp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv17 8) hdr.ipv4.protocol);
                         hdr.udp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.udp.srcPort;
                         fabric_metadata.l4_dport:=hdr.udp.dstPort;
                        {
                           assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                           hdr.gtpu.isValid:=(_ bv1 1);
                          {
                             assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                             hdr.gtpu_options.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                               hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                              {
                                 assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          } [] {
                             assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                             hdr.inner_ipv4.isValid:=(_ bv1 1);
                             last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                            {
                               assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                              {
                                 assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_icmp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_udp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                               hdr.inner_tcp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          }
                        }
                      }
                    } [] {
                       assume (= (_ bv6 8) hdr.ipv4.protocol);
                       hdr.tcp.isValid:=(_ bv1 1);
                       fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                       fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                       parse_result:=(_ bv1 1)
                    }
                  }
                } [] {
                   assume (= (_ bv34887 16) hdr.eth_type.value);
                   parse_result:=(_ bv0 1)
                }
              }
            }
          } [] {
             assume (= (_ bv4 4) look_mpls);
             hdr.ipv4.isValid:=(_ bv1 1);
             fabric_metadata.ip_proto:=hdr.ipv4.protocol;
             fabric_metadata.ip_eth_type:=(_ bv2048 16);
             fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
             fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
             last_ipv4_dscp:=hdr.ipv4.dscp;
            {
               assume (not(= (_ bv6 8) hdr.ipv4.protocol));
              {
                 assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                {
                   assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                   parse_result:=(_ bv1 1)
                } [] {
                   assume (= (_ bv1 8) hdr.ipv4.protocol);
                   hdr.icmp.isValid:=(_ bv1 1);
                   parse_result:=(_ bv1 1)
                }
              } [] {
                 assume (= (_ bv17 8) hdr.ipv4.protocol);
                 hdr.udp.isValid:=(_ bv1 1);
                 fabric_metadata.l4_sport:=hdr.udp.srcPort;
                 fabric_metadata.l4_dport:=hdr.udp.dstPort;
                {
                   assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                   parse_result:=(_ bv1 1)
                } [] {
                   assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                   hdr.gtpu.isValid:=(_ bv1 1);
                  {
                     assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                     hdr.gtpu_options.isValid:=(_ bv1 1);
                    {
                       assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                       hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                      {
                         assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                         hdr.inner_ipv4.isValid:=(_ bv1 1);
                         last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                        {
                           assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                          {
                             assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                            {
                               assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                               hdr.inner_icmp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                             hdr.inner_udp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                           hdr.inner_tcp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      }
                    }
                  } [] {
                     assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                     hdr.inner_ipv4.isValid:=(_ bv1 1);
                     last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                    {
                       assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                      {
                         assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                        {
                           assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                           hdr.inner_icmp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                         hdr.inner_udp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    } [] {
                       assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                       hdr.inner_tcp.isValid:=(_ bv1 1);
                       parse_result:=(_ bv1 1)
                    }
                  }
                }
              }
            } [] {
               assume (= (_ bv6 8) hdr.ipv4.protocol);
               hdr.tcp.isValid:=(_ bv1 1);
               fabric_metadata.l4_sport:=hdr.tcp.srcPort;
               fabric_metadata.l4_dport:=hdr.tcp.dstPort;
               parse_result:=(_ bv1 1)
            }
          }
        }
      } [] {
         assume (= (_ bv33024 16) look_eth);
         hdr.vlan_tag.isValid:=(_ bv1 1);
         hdr.vlan_tag.eth_type:=look_eth;
        {
           assume (not(= (_ bv33024 16) look_vlan));
           hdr.eth_type.isValid:=(_ bv1 1);
          {
             assume (not(= (_ bv34887 16) hdr.eth_type.value));
            {
               assume (not(= (_ bv2048 16) hdr.eth_type.value));
               parse_result:=(_ bv1 1)
            } [] {
               assume (= (_ bv2048 16) hdr.eth_type.value);
               hdr.ipv4.isValid:=(_ bv1 1);
               fabric_metadata.ip_proto:=hdr.ipv4.protocol;
               fabric_metadata.ip_eth_type:=(_ bv2048 16);
               fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
               fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
               last_ipv4_dscp:=hdr.ipv4.dscp;
              {
                 assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                {
                   assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                  {
                     assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (= (_ bv1 8) hdr.ipv4.protocol);
                     hdr.icmp.isValid:=(_ bv1 1);
                     parse_result:=(_ bv1 1)
                  }
                } [] {
                   assume (= (_ bv17 8) hdr.ipv4.protocol);
                   hdr.udp.isValid:=(_ bv1 1);
                   fabric_metadata.l4_sport:=hdr.udp.srcPort;
                   fabric_metadata.l4_dport:=hdr.udp.dstPort;
                  {
                     assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                     hdr.gtpu.isValid:=(_ bv1 1);
                    {
                       assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                       hdr.gtpu_options.isValid:=(_ bv1 1);
                      {
                         assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                         hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                        {
                           assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                           hdr.inner_ipv4.isValid:=(_ bv1 1);
                           last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                          {
                             assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                            {
                               assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                              {
                                 assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_icmp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                               hdr.inner_udp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                             hdr.inner_tcp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        }
                      }
                    } [] {
                       assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                       hdr.inner_ipv4.isValid:=(_ bv1 1);
                       last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                             hdr.inner_icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                           hdr.inner_udp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                         hdr.inner_tcp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    }
                  }
                }
              } [] {
                 assume (= (_ bv6 8) hdr.ipv4.protocol);
                 hdr.tcp.isValid:=(_ bv1 1);
                 fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                 fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                 parse_result:=(_ bv1 1)
              }
            }
          } [] {
             assume (= (_ bv34887 16) hdr.eth_type.value);
             hdr.mpls.isValid:=(_ bv1 1);
             fabric_metadata.mpls_label:=hdr.mpls.label;
             fabric_metadata.mpls_ttl:=hdr.mpls.ttl;
            {
               assume (not(= (_ bv4 4) look_mpls));
               fabric_metadata.vlan_id:=(_ bv4094 12);
               hdr.ethernet.isValid:=(_ bv1 1);
              {
                 assume (not(= (_ bv34984 16) look_eth));
                {
                   assume (not(= (_ bv37120 16) look_eth));
                  {
                     assume (not(= (_ bv33024 16) look_eth));
                     hdr.eth_type.isValid:=(_ bv1 1);
                    {
                       assume (not(= (_ bv34887 16) hdr.eth_type.value));
                      {
                         assume (not(= (_ bv2048 16) hdr.eth_type.value));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv2048 16) hdr.eth_type.value);
                         hdr.ipv4.isValid:=(_ bv1 1);
                         fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                         fabric_metadata.ip_eth_type:=(_ bv2048 16);
                         fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                         fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                         last_ipv4_dscp:=hdr.ipv4.dscp;
                        {
                           assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                            {
                               assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv1 8) hdr.ipv4.protocol);
                               hdr.icmp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv17 8) hdr.ipv4.protocol);
                             hdr.udp.isValid:=(_ bv1 1);
                             fabric_metadata.l4_sport:=hdr.udp.srcPort;
                             fabric_metadata.l4_dport:=hdr.udp.dstPort;
                            {
                               assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                               hdr.gtpu.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                                 hdr.gtpu_options.isValid:=(_ bv1 1);
                                {
                                   assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                   hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                  {
                                     assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                     hdr.inner_ipv4.isValid:=(_ bv1 1);
                                     last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                    {
                                       assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                        {
                                           assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                           parse_result:=(_ bv1 1)
                                        } [] {
                                           assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                           hdr.inner_icmp.isValid:=(_ bv1 1);
                                           parse_result:=(_ bv1 1)
                                        }
                                      } [] {
                                         assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_udp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_tcp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  }
                                }
                              } [] {
                                 assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          }
                        } [] {
                           assume (= (_ bv6 8) hdr.ipv4.protocol);
                           hdr.tcp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                           fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                           parse_result:=(_ bv1 1)
                        }
                      }
                    } [] {
                       assume (= (_ bv34887 16) hdr.eth_type.value);
                       parse_result:=(_ bv0 1)
                    }
                  } [] {
                     assume (= (_ bv33024 16) look_eth);
                     hdr.vlan_tag.isValid:=(_ bv1 1);
                     hdr.vlan_tag.eth_type:=look_eth;
                    {
                       assume (not(= (_ bv33024 16) look_vlan));
                       hdr.eth_type.isValid:=(_ bv1 1);
                      {
                         assume (not(= (_ bv34887 16) hdr.eth_type.value));
                        {
                           assume (not(= (_ bv2048 16) hdr.eth_type.value));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv2048 16) hdr.eth_type.value);
                           hdr.ipv4.isValid:=(_ bv1 1);
                           fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                           fabric_metadata.ip_eth_type:=(_ bv2048 16);
                           fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                           fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                           last_ipv4_dscp:=hdr.ipv4.dscp;
                          {
                             assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                            {
                               assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                              {
                                 assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv1 8) hdr.ipv4.protocol);
                                 hdr.icmp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv17 8) hdr.ipv4.protocol);
                               hdr.udp.isValid:=(_ bv1 1);
                               fabric_metadata.l4_sport:=hdr.udp.srcPort;
                               fabric_metadata.l4_dport:=hdr.udp.dstPort;
                              {
                                 assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                                 hdr.gtpu.isValid:=(_ bv1 1);
                                {
                                   assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                                   hdr.gtpu_options.isValid:=(_ bv1 1);
                                  {
                                     assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                     hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                    {
                                       assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                       hdr.inner_ipv4.isValid:=(_ bv1 1);
                                       last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                      {
                                         assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                        {
                                           assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                          {
                                             assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                             parse_result:=(_ bv1 1)
                                          } [] {
                                             assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                             hdr.inner_icmp.isValid:=(_ bv1 1);
                                             parse_result:=(_ bv1 1)
                                          }
                                        } [] {
                                           assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                           hdr.inner_udp.isValid:=(_ bv1 1);
                                           parse_result:=(_ bv1 1)
                                        }
                                      } [] {
                                         assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_tcp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    }
                                  }
                                } [] {
                                   assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                  {
                                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                         parse_result:=(_ bv1 1)
                                      } [] {
                                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_icmp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_udp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_tcp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                }
                              }
                            }
                          } [] {
                             assume (= (_ bv6 8) hdr.ipv4.protocol);
                             hdr.tcp.isValid:=(_ bv1 1);
                             fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                             fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                             parse_result:=(_ bv1 1)
                          }
                        }
                      } [] {
                         assume (= (_ bv34887 16) hdr.eth_type.value);
                         parse_result:=(_ bv0 1)
                      }
                    } [] {
                       assume (= (_ bv33024 16) look_vlan);
                       hdr.inner_vlan_tag.isValid:=(_ bv1 1);
                       hdr.inner_vlan_tag.eth_type:=look_vlan;
                       hdr.eth_type.isValid:=(_ bv1 1);
                      {
                         assume (not(= (_ bv34887 16) hdr.eth_type.value));
                        {
                           assume (not(= (_ bv2048 16) hdr.eth_type.value));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv2048 16) hdr.eth_type.value);
                           hdr.ipv4.isValid:=(_ bv1 1);
                           fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                           fabric_metadata.ip_eth_type:=(_ bv2048 16);
                           fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                           fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                           last_ipv4_dscp:=hdr.ipv4.dscp;
                          {
                             assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                            {
                               assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                              {
                                 assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv1 8) hdr.ipv4.protocol);
                                 hdr.icmp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv17 8) hdr.ipv4.protocol);
                               hdr.udp.isValid:=(_ bv1 1);
                               fabric_metadata.l4_sport:=hdr.udp.srcPort;
                               fabric_metadata.l4_dport:=hdr.udp.dstPort;
                              {
                                 assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                                 hdr.gtpu.isValid:=(_ bv1 1);
                                {
                                   assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                                   hdr.gtpu_options.isValid:=(_ bv1 1);
                                  {
                                     assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                     hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                    {
                                       assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                       hdr.inner_ipv4.isValid:=(_ bv1 1);
                                       last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                      {
                                         assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                        {
                                           assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                          {
                                             assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                             parse_result:=(_ bv1 1)
                                          } [] {
                                             assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                             hdr.inner_icmp.isValid:=(_ bv1 1);
                                             parse_result:=(_ bv1 1)
                                          }
                                        } [] {
                                           assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                           hdr.inner_udp.isValid:=(_ bv1 1);
                                           parse_result:=(_ bv1 1)
                                        }
                                      } [] {
                                         assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_tcp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    }
                                  }
                                } [] {
                                   assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                  {
                                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                         parse_result:=(_ bv1 1)
                                      } [] {
                                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_icmp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_udp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_tcp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                }
                              }
                            }
                          } [] {
                             assume (= (_ bv6 8) hdr.ipv4.protocol);
                             hdr.tcp.isValid:=(_ bv1 1);
                             fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                             fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                             parse_result:=(_ bv1 1)
                          }
                        }
                      } [] {
                         assume (= (_ bv34887 16) hdr.eth_type.value);
                         parse_result:=(_ bv0 1)
                      }
                    }
                  }
                } [] {
                   assume (= (_ bv37120 16) look_eth);
                   hdr.vlan_tag.isValid:=(_ bv1 1);
                   hdr.vlan_tag.eth_type:=look_eth;
                  {
                     assume (not(= (_ bv33024 16) look_vlan));
                     hdr.eth_type.isValid:=(_ bv1 1);
                    {
                       assume (not(= (_ bv34887 16) hdr.eth_type.value));
                      {
                         assume (not(= (_ bv2048 16) hdr.eth_type.value));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv2048 16) hdr.eth_type.value);
                         hdr.ipv4.isValid:=(_ bv1 1);
                         fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                         fabric_metadata.ip_eth_type:=(_ bv2048 16);
                         fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                         fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                         last_ipv4_dscp:=hdr.ipv4.dscp;
                        {
                           assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                            {
                               assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv1 8) hdr.ipv4.protocol);
                               hdr.icmp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv17 8) hdr.ipv4.protocol);
                             hdr.udp.isValid:=(_ bv1 1);
                             fabric_metadata.l4_sport:=hdr.udp.srcPort;
                             fabric_metadata.l4_dport:=hdr.udp.dstPort;
                            {
                               assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                               hdr.gtpu.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                                 hdr.gtpu_options.isValid:=(_ bv1 1);
                                {
                                   assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                   hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                  {
                                     assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                     hdr.inner_ipv4.isValid:=(_ bv1 1);
                                     last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                    {
                                       assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                        {
                                           assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                           parse_result:=(_ bv1 1)
                                        } [] {
                                           assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                           hdr.inner_icmp.isValid:=(_ bv1 1);
                                           parse_result:=(_ bv1 1)
                                        }
                                      } [] {
                                         assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_udp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_tcp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  }
                                }
                              } [] {
                                 assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          }
                        } [] {
                           assume (= (_ bv6 8) hdr.ipv4.protocol);
                           hdr.tcp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                           fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                           parse_result:=(_ bv1 1)
                        }
                      }
                    } [] {
                       assume (= (_ bv34887 16) hdr.eth_type.value);
                       parse_result:=(_ bv0 1)
                    }
                  } [] {
                     assume (= (_ bv33024 16) look_vlan);
                     hdr.inner_vlan_tag.isValid:=(_ bv1 1);
                     hdr.inner_vlan_tag.eth_type:=look_vlan;
                     hdr.eth_type.isValid:=(_ bv1 1);
                    {
                       assume (not(= (_ bv34887 16) hdr.eth_type.value));
                      {
                         assume (not(= (_ bv2048 16) hdr.eth_type.value));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv2048 16) hdr.eth_type.value);
                         hdr.ipv4.isValid:=(_ bv1 1);
                         fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                         fabric_metadata.ip_eth_type:=(_ bv2048 16);
                         fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                         fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                         last_ipv4_dscp:=hdr.ipv4.dscp;
                        {
                           assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                            {
                               assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv1 8) hdr.ipv4.protocol);
                               hdr.icmp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv17 8) hdr.ipv4.protocol);
                             hdr.udp.isValid:=(_ bv1 1);
                             fabric_metadata.l4_sport:=hdr.udp.srcPort;
                             fabric_metadata.l4_dport:=hdr.udp.dstPort;
                            {
                               assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                               hdr.gtpu.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                                 hdr.gtpu_options.isValid:=(_ bv1 1);
                                {
                                   assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                   hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                  {
                                     assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                     hdr.inner_ipv4.isValid:=(_ bv1 1);
                                     last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                    {
                                       assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                        {
                                           assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                           parse_result:=(_ bv1 1)
                                        } [] {
                                           assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                           hdr.inner_icmp.isValid:=(_ bv1 1);
                                           parse_result:=(_ bv1 1)
                                        }
                                      } [] {
                                         assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_udp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_tcp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  }
                                }
                              } [] {
                                 assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          }
                        } [] {
                           assume (= (_ bv6 8) hdr.ipv4.protocol);
                           hdr.tcp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                           fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                           parse_result:=(_ bv1 1)
                        }
                      }
                    } [] {
                       assume (= (_ bv34887 16) hdr.eth_type.value);
                       parse_result:=(_ bv0 1)
                    }
                  }
                }
              } [] {
                 assume (= (_ bv34984 16) look_eth);
                 hdr.vlan_tag.isValid:=(_ bv1 1);
                 hdr.vlan_tag.eth_type:=look_eth;
                {
                   assume (not(= (_ bv33024 16) look_vlan));
                   hdr.eth_type.isValid:=(_ bv1 1);
                  {
                     assume (not(= (_ bv34887 16) hdr.eth_type.value));
                    {
                       assume (not(= (_ bv2048 16) hdr.eth_type.value));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (= (_ bv2048 16) hdr.eth_type.value);
                       hdr.ipv4.isValid:=(_ bv1 1);
                       fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                       fabric_metadata.ip_eth_type:=(_ bv2048 16);
                       fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                       fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                       last_ipv4_dscp:=hdr.ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.ipv4.protocol);
                             hdr.icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.ipv4.protocol);
                           hdr.udp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.udp.srcPort;
                           fabric_metadata.l4_dport:=hdr.udp.dstPort;
                          {
                             assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                             hdr.gtpu.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                               hdr.gtpu_options.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                 hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                {
                                   assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                  {
                                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                         parse_result:=(_ bv1 1)
                                      } [] {
                                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_icmp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_udp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_tcp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                }
                              }
                            } [] {
                               assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                               hdr.inner_ipv4.isValid:=(_ bv1 1);
                               last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                              {
                                 assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_icmp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_udp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_tcp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            }
                          }
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.ipv4.protocol);
                         hdr.tcp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                         fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                         parse_result:=(_ bv1 1)
                      }
                    }
                  } [] {
                     assume (= (_ bv34887 16) hdr.eth_type.value);
                     parse_result:=(_ bv0 1)
                  }
                } [] {
                   assume (= (_ bv33024 16) look_vlan);
                   hdr.inner_vlan_tag.isValid:=(_ bv1 1);
                   hdr.inner_vlan_tag.eth_type:=look_vlan;
                   hdr.eth_type.isValid:=(_ bv1 1);
                  {
                     assume (not(= (_ bv34887 16) hdr.eth_type.value));
                    {
                       assume (not(= (_ bv2048 16) hdr.eth_type.value));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (= (_ bv2048 16) hdr.eth_type.value);
                       hdr.ipv4.isValid:=(_ bv1 1);
                       fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                       fabric_metadata.ip_eth_type:=(_ bv2048 16);
                       fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                       fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                       last_ipv4_dscp:=hdr.ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.ipv4.protocol);
                             hdr.icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.ipv4.protocol);
                           hdr.udp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.udp.srcPort;
                           fabric_metadata.l4_dport:=hdr.udp.dstPort;
                          {
                             assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                             hdr.gtpu.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                               hdr.gtpu_options.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                 hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                {
                                   assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                  {
                                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                         parse_result:=(_ bv1 1)
                                      } [] {
                                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_icmp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_udp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_tcp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                }
                              }
                            } [] {
                               assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                               hdr.inner_ipv4.isValid:=(_ bv1 1);
                               last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                              {
                                 assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_icmp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_udp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_tcp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            }
                          }
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.ipv4.protocol);
                         hdr.tcp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                         fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                         parse_result:=(_ bv1 1)
                      }
                    }
                  } [] {
                     assume (= (_ bv34887 16) hdr.eth_type.value);
                     parse_result:=(_ bv0 1)
                  }
                }
              }
            } [] {
               assume (= (_ bv4 4) look_mpls);
               hdr.ipv4.isValid:=(_ bv1 1);
               fabric_metadata.ip_proto:=hdr.ipv4.protocol;
               fabric_metadata.ip_eth_type:=(_ bv2048 16);
               fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
               fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
               last_ipv4_dscp:=hdr.ipv4.dscp;
              {
                 assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                {
                   assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                  {
                     assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (= (_ bv1 8) hdr.ipv4.protocol);
                     hdr.icmp.isValid:=(_ bv1 1);
                     parse_result:=(_ bv1 1)
                  }
                } [] {
                   assume (= (_ bv17 8) hdr.ipv4.protocol);
                   hdr.udp.isValid:=(_ bv1 1);
                   fabric_metadata.l4_sport:=hdr.udp.srcPort;
                   fabric_metadata.l4_dport:=hdr.udp.dstPort;
                  {
                     assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                     hdr.gtpu.isValid:=(_ bv1 1);
                    {
                       assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                       hdr.gtpu_options.isValid:=(_ bv1 1);
                      {
                         assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                         hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                        {
                           assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                           hdr.inner_ipv4.isValid:=(_ bv1 1);
                           last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                          {
                             assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                            {
                               assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                              {
                                 assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_icmp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                               hdr.inner_udp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                             hdr.inner_tcp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        }
                      }
                    } [] {
                       assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                       hdr.inner_ipv4.isValid:=(_ bv1 1);
                       last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                             hdr.inner_icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                           hdr.inner_udp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                         hdr.inner_tcp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    }
                  }
                }
              } [] {
                 assume (= (_ bv6 8) hdr.ipv4.protocol);
                 hdr.tcp.isValid:=(_ bv1 1);
                 fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                 fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                 parse_result:=(_ bv1 1)
              }
            }
          }
        } [] {
           assume (= (_ bv33024 16) look_vlan);
           hdr.inner_vlan_tag.isValid:=(_ bv1 1);
           hdr.inner_vlan_tag.eth_type:=look_vlan;
           hdr.eth_type.isValid:=(_ bv1 1);
          {
             assume (not(= (_ bv34887 16) hdr.eth_type.value));
            {
               assume (not(= (_ bv2048 16) hdr.eth_type.value));
               parse_result:=(_ bv1 1)
            } [] {
               assume (= (_ bv2048 16) hdr.eth_type.value);
               hdr.ipv4.isValid:=(_ bv1 1);
               fabric_metadata.ip_proto:=hdr.ipv4.protocol;
               fabric_metadata.ip_eth_type:=(_ bv2048 16);
               fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
               fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
               last_ipv4_dscp:=hdr.ipv4.dscp;
              {
                 assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                {
                   assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                  {
                     assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (= (_ bv1 8) hdr.ipv4.protocol);
                     hdr.icmp.isValid:=(_ bv1 1);
                     parse_result:=(_ bv1 1)
                  }
                } [] {
                   assume (= (_ bv17 8) hdr.ipv4.protocol);
                   hdr.udp.isValid:=(_ bv1 1);
                   fabric_metadata.l4_sport:=hdr.udp.srcPort;
                   fabric_metadata.l4_dport:=hdr.udp.dstPort;
                  {
                     assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                     hdr.gtpu.isValid:=(_ bv1 1);
                    {
                       assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                       hdr.gtpu_options.isValid:=(_ bv1 1);
                      {
                         assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                         hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                        {
                           assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                           hdr.inner_ipv4.isValid:=(_ bv1 1);
                           last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                          {
                             assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                            {
                               assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                              {
                                 assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_icmp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                               hdr.inner_udp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                             hdr.inner_tcp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        }
                      }
                    } [] {
                       assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                       hdr.inner_ipv4.isValid:=(_ bv1 1);
                       last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                             hdr.inner_icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                           hdr.inner_udp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                         hdr.inner_tcp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    }
                  }
                }
              } [] {
                 assume (= (_ bv6 8) hdr.ipv4.protocol);
                 hdr.tcp.isValid:=(_ bv1 1);
                 fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                 fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                 parse_result:=(_ bv1 1)
              }
            }
          } [] {
             assume (= (_ bv34887 16) hdr.eth_type.value);
             hdr.mpls.isValid:=(_ bv1 1);
             fabric_metadata.mpls_label:=hdr.mpls.label;
             fabric_metadata.mpls_ttl:=hdr.mpls.ttl;
            {
               assume (not(= (_ bv4 4) look_mpls));
               fabric_metadata.vlan_id:=(_ bv4094 12);
               hdr.ethernet.isValid:=(_ bv1 1);
              {
                 assume (not(= (_ bv34984 16) look_eth));
                {
                   assume (not(= (_ bv37120 16) look_eth));
                  {
                     assume (not(= (_ bv33024 16) look_eth));
                     hdr.eth_type.isValid:=(_ bv1 1);
                    {
                       assume (not(= (_ bv34887 16) hdr.eth_type.value));
                      {
                         assume (not(= (_ bv2048 16) hdr.eth_type.value));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv2048 16) hdr.eth_type.value);
                         hdr.ipv4.isValid:=(_ bv1 1);
                         fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                         fabric_metadata.ip_eth_type:=(_ bv2048 16);
                         fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                         fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                         last_ipv4_dscp:=hdr.ipv4.dscp;
                        {
                           assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                            {
                               assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv1 8) hdr.ipv4.protocol);
                               hdr.icmp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv17 8) hdr.ipv4.protocol);
                             hdr.udp.isValid:=(_ bv1 1);
                             fabric_metadata.l4_sport:=hdr.udp.srcPort;
                             fabric_metadata.l4_dport:=hdr.udp.dstPort;
                            {
                               assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                               hdr.gtpu.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                                 hdr.gtpu_options.isValid:=(_ bv1 1);
                                {
                                   assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                   hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                  {
                                     assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                     hdr.inner_ipv4.isValid:=(_ bv1 1);
                                     last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                    {
                                       assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                        {
                                           assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                           parse_result:=(_ bv1 1)
                                        } [] {
                                           assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                           hdr.inner_icmp.isValid:=(_ bv1 1);
                                           parse_result:=(_ bv1 1)
                                        }
                                      } [] {
                                         assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_udp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_tcp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  }
                                }
                              } [] {
                                 assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          }
                        } [] {
                           assume (= (_ bv6 8) hdr.ipv4.protocol);
                           hdr.tcp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                           fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                           parse_result:=(_ bv1 1)
                        }
                      }
                    } [] {
                       assume (= (_ bv34887 16) hdr.eth_type.value);
                       parse_result:=(_ bv0 1)
                    }
                  } [] {
                     assume (= (_ bv33024 16) look_eth);
                     hdr.vlan_tag.isValid:=(_ bv1 1);
                     hdr.vlan_tag.eth_type:=look_eth;
                    {
                       assume (not(= (_ bv33024 16) look_vlan));
                       hdr.eth_type.isValid:=(_ bv1 1);
                      {
                         assume (not(= (_ bv34887 16) hdr.eth_type.value));
                        {
                           assume (not(= (_ bv2048 16) hdr.eth_type.value));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv2048 16) hdr.eth_type.value);
                           hdr.ipv4.isValid:=(_ bv1 1);
                           fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                           fabric_metadata.ip_eth_type:=(_ bv2048 16);
                           fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                           fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                           last_ipv4_dscp:=hdr.ipv4.dscp;
                          {
                             assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                            {
                               assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                              {
                                 assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv1 8) hdr.ipv4.protocol);
                                 hdr.icmp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv17 8) hdr.ipv4.protocol);
                               hdr.udp.isValid:=(_ bv1 1);
                               fabric_metadata.l4_sport:=hdr.udp.srcPort;
                               fabric_metadata.l4_dport:=hdr.udp.dstPort;
                              {
                                 assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                                 hdr.gtpu.isValid:=(_ bv1 1);
                                {
                                   assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                                   hdr.gtpu_options.isValid:=(_ bv1 1);
                                  {
                                     assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                     hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                    {
                                       assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                       hdr.inner_ipv4.isValid:=(_ bv1 1);
                                       last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                      {
                                         assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                        {
                                           assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                          {
                                             assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                             parse_result:=(_ bv1 1)
                                          } [] {
                                             assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                             hdr.inner_icmp.isValid:=(_ bv1 1);
                                             parse_result:=(_ bv1 1)
                                          }
                                        } [] {
                                           assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                           hdr.inner_udp.isValid:=(_ bv1 1);
                                           parse_result:=(_ bv1 1)
                                        }
                                      } [] {
                                         assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_tcp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    }
                                  }
                                } [] {
                                   assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                  {
                                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                         parse_result:=(_ bv1 1)
                                      } [] {
                                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_icmp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_udp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_tcp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                }
                              }
                            }
                          } [] {
                             assume (= (_ bv6 8) hdr.ipv4.protocol);
                             hdr.tcp.isValid:=(_ bv1 1);
                             fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                             fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                             parse_result:=(_ bv1 1)
                          }
                        }
                      } [] {
                         assume (= (_ bv34887 16) hdr.eth_type.value);
                         parse_result:=(_ bv0 1)
                      }
                    } [] {
                       assume (= (_ bv33024 16) look_vlan);
                       hdr.inner_vlan_tag.isValid:=(_ bv1 1);
                       hdr.inner_vlan_tag.eth_type:=look_vlan;
                       hdr.eth_type.isValid:=(_ bv1 1);
                      {
                         assume (not(= (_ bv34887 16) hdr.eth_type.value));
                        {
                           assume (not(= (_ bv2048 16) hdr.eth_type.value));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv2048 16) hdr.eth_type.value);
                           hdr.ipv4.isValid:=(_ bv1 1);
                           fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                           fabric_metadata.ip_eth_type:=(_ bv2048 16);
                           fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                           fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                           last_ipv4_dscp:=hdr.ipv4.dscp;
                          {
                             assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                            {
                               assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                              {
                                 assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv1 8) hdr.ipv4.protocol);
                                 hdr.icmp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv17 8) hdr.ipv4.protocol);
                               hdr.udp.isValid:=(_ bv1 1);
                               fabric_metadata.l4_sport:=hdr.udp.srcPort;
                               fabric_metadata.l4_dport:=hdr.udp.dstPort;
                              {
                                 assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                                 hdr.gtpu.isValid:=(_ bv1 1);
                                {
                                   assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                                   hdr.gtpu_options.isValid:=(_ bv1 1);
                                  {
                                     assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                     hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                    {
                                       assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                       hdr.inner_ipv4.isValid:=(_ bv1 1);
                                       last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                      {
                                         assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                        {
                                           assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                          {
                                             assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                             parse_result:=(_ bv1 1)
                                          } [] {
                                             assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                             hdr.inner_icmp.isValid:=(_ bv1 1);
                                             parse_result:=(_ bv1 1)
                                          }
                                        } [] {
                                           assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                           hdr.inner_udp.isValid:=(_ bv1 1);
                                           parse_result:=(_ bv1 1)
                                        }
                                      } [] {
                                         assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_tcp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    }
                                  }
                                } [] {
                                   assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                  {
                                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                         parse_result:=(_ bv1 1)
                                      } [] {
                                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_icmp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_udp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_tcp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                }
                              }
                            }
                          } [] {
                             assume (= (_ bv6 8) hdr.ipv4.protocol);
                             hdr.tcp.isValid:=(_ bv1 1);
                             fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                             fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                             parse_result:=(_ bv1 1)
                          }
                        }
                      } [] {
                         assume (= (_ bv34887 16) hdr.eth_type.value);
                         parse_result:=(_ bv0 1)
                      }
                    }
                  }
                } [] {
                   assume (= (_ bv37120 16) look_eth);
                   hdr.vlan_tag.isValid:=(_ bv1 1);
                   hdr.vlan_tag.eth_type:=look_eth;
                  {
                     assume (not(= (_ bv33024 16) look_vlan));
                     hdr.eth_type.isValid:=(_ bv1 1);
                    {
                       assume (not(= (_ bv34887 16) hdr.eth_type.value));
                      {
                         assume (not(= (_ bv2048 16) hdr.eth_type.value));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv2048 16) hdr.eth_type.value);
                         hdr.ipv4.isValid:=(_ bv1 1);
                         fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                         fabric_metadata.ip_eth_type:=(_ bv2048 16);
                         fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                         fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                         last_ipv4_dscp:=hdr.ipv4.dscp;
                        {
                           assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                            {
                               assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv1 8) hdr.ipv4.protocol);
                               hdr.icmp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv17 8) hdr.ipv4.protocol);
                             hdr.udp.isValid:=(_ bv1 1);
                             fabric_metadata.l4_sport:=hdr.udp.srcPort;
                             fabric_metadata.l4_dport:=hdr.udp.dstPort;
                            {
                               assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                               hdr.gtpu.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                                 hdr.gtpu_options.isValid:=(_ bv1 1);
                                {
                                   assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                   hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                  {
                                     assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                     hdr.inner_ipv4.isValid:=(_ bv1 1);
                                     last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                    {
                                       assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                        {
                                           assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                           parse_result:=(_ bv1 1)
                                        } [] {
                                           assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                           hdr.inner_icmp.isValid:=(_ bv1 1);
                                           parse_result:=(_ bv1 1)
                                        }
                                      } [] {
                                         assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_udp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_tcp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  }
                                }
                              } [] {
                                 assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          }
                        } [] {
                           assume (= (_ bv6 8) hdr.ipv4.protocol);
                           hdr.tcp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                           fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                           parse_result:=(_ bv1 1)
                        }
                      }
                    } [] {
                       assume (= (_ bv34887 16) hdr.eth_type.value);
                       parse_result:=(_ bv0 1)
                    }
                  } [] {
                     assume (= (_ bv33024 16) look_vlan);
                     hdr.inner_vlan_tag.isValid:=(_ bv1 1);
                     hdr.inner_vlan_tag.eth_type:=look_vlan;
                     hdr.eth_type.isValid:=(_ bv1 1);
                    {
                       assume (not(= (_ bv34887 16) hdr.eth_type.value));
                      {
                         assume (not(= (_ bv2048 16) hdr.eth_type.value));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv2048 16) hdr.eth_type.value);
                         hdr.ipv4.isValid:=(_ bv1 1);
                         fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                         fabric_metadata.ip_eth_type:=(_ bv2048 16);
                         fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                         fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                         last_ipv4_dscp:=hdr.ipv4.dscp;
                        {
                           assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                            {
                               assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv1 8) hdr.ipv4.protocol);
                               hdr.icmp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv17 8) hdr.ipv4.protocol);
                             hdr.udp.isValid:=(_ bv1 1);
                             fabric_metadata.l4_sport:=hdr.udp.srcPort;
                             fabric_metadata.l4_dport:=hdr.udp.dstPort;
                            {
                               assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                               hdr.gtpu.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                                 hdr.gtpu_options.isValid:=(_ bv1 1);
                                {
                                   assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                   hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                  {
                                     assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                     hdr.inner_ipv4.isValid:=(_ bv1 1);
                                     last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                    {
                                       assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                        {
                                           assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                           parse_result:=(_ bv1 1)
                                        } [] {
                                           assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                           hdr.inner_icmp.isValid:=(_ bv1 1);
                                           parse_result:=(_ bv1 1)
                                        }
                                      } [] {
                                         assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_udp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_tcp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  }
                                }
                              } [] {
                                 assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          }
                        } [] {
                           assume (= (_ bv6 8) hdr.ipv4.protocol);
                           hdr.tcp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                           fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                           parse_result:=(_ bv1 1)
                        }
                      }
                    } [] {
                       assume (= (_ bv34887 16) hdr.eth_type.value);
                       parse_result:=(_ bv0 1)
                    }
                  }
                }
              } [] {
                 assume (= (_ bv34984 16) look_eth);
                 hdr.vlan_tag.isValid:=(_ bv1 1);
                 hdr.vlan_tag.eth_type:=look_eth;
                {
                   assume (not(= (_ bv33024 16) look_vlan));
                   hdr.eth_type.isValid:=(_ bv1 1);
                  {
                     assume (not(= (_ bv34887 16) hdr.eth_type.value));
                    {
                       assume (not(= (_ bv2048 16) hdr.eth_type.value));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (= (_ bv2048 16) hdr.eth_type.value);
                       hdr.ipv4.isValid:=(_ bv1 1);
                       fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                       fabric_metadata.ip_eth_type:=(_ bv2048 16);
                       fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                       fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                       last_ipv4_dscp:=hdr.ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.ipv4.protocol);
                             hdr.icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.ipv4.protocol);
                           hdr.udp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.udp.srcPort;
                           fabric_metadata.l4_dport:=hdr.udp.dstPort;
                          {
                             assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                             hdr.gtpu.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                               hdr.gtpu_options.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                 hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                {
                                   assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                  {
                                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                         parse_result:=(_ bv1 1)
                                      } [] {
                                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_icmp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_udp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_tcp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                }
                              }
                            } [] {
                               assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                               hdr.inner_ipv4.isValid:=(_ bv1 1);
                               last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                              {
                                 assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_icmp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_udp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_tcp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            }
                          }
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.ipv4.protocol);
                         hdr.tcp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                         fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                         parse_result:=(_ bv1 1)
                      }
                    }
                  } [] {
                     assume (= (_ bv34887 16) hdr.eth_type.value);
                     parse_result:=(_ bv0 1)
                  }
                } [] {
                   assume (= (_ bv33024 16) look_vlan);
                   hdr.inner_vlan_tag.isValid:=(_ bv1 1);
                   hdr.inner_vlan_tag.eth_type:=look_vlan;
                   hdr.eth_type.isValid:=(_ bv1 1);
                  {
                     assume (not(= (_ bv34887 16) hdr.eth_type.value));
                    {
                       assume (not(= (_ bv2048 16) hdr.eth_type.value));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (= (_ bv2048 16) hdr.eth_type.value);
                       hdr.ipv4.isValid:=(_ bv1 1);
                       fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                       fabric_metadata.ip_eth_type:=(_ bv2048 16);
                       fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                       fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                       last_ipv4_dscp:=hdr.ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.ipv4.protocol);
                             hdr.icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.ipv4.protocol);
                           hdr.udp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.udp.srcPort;
                           fabric_metadata.l4_dport:=hdr.udp.dstPort;
                          {
                             assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                             hdr.gtpu.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                               hdr.gtpu_options.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                 hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                {
                                   assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                  {
                                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                         parse_result:=(_ bv1 1)
                                      } [] {
                                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_icmp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_udp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_tcp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                }
                              }
                            } [] {
                               assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                               hdr.inner_ipv4.isValid:=(_ bv1 1);
                               last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                              {
                                 assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_icmp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_udp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_tcp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            }
                          }
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.ipv4.protocol);
                         hdr.tcp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                         fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                         parse_result:=(_ bv1 1)
                      }
                    }
                  } [] {
                     assume (= (_ bv34887 16) hdr.eth_type.value);
                     parse_result:=(_ bv0 1)
                  }
                }
              }
            } [] {
               assume (= (_ bv4 4) look_mpls);
               hdr.ipv4.isValid:=(_ bv1 1);
               fabric_metadata.ip_proto:=hdr.ipv4.protocol;
               fabric_metadata.ip_eth_type:=(_ bv2048 16);
               fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
               fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
               last_ipv4_dscp:=hdr.ipv4.dscp;
              {
                 assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                {
                   assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                  {
                     assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (= (_ bv1 8) hdr.ipv4.protocol);
                     hdr.icmp.isValid:=(_ bv1 1);
                     parse_result:=(_ bv1 1)
                  }
                } [] {
                   assume (= (_ bv17 8) hdr.ipv4.protocol);
                   hdr.udp.isValid:=(_ bv1 1);
                   fabric_metadata.l4_sport:=hdr.udp.srcPort;
                   fabric_metadata.l4_dport:=hdr.udp.dstPort;
                  {
                     assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                     hdr.gtpu.isValid:=(_ bv1 1);
                    {
                       assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                       hdr.gtpu_options.isValid:=(_ bv1 1);
                      {
                         assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                         hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                        {
                           assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                           hdr.inner_ipv4.isValid:=(_ bv1 1);
                           last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                          {
                             assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                            {
                               assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                              {
                                 assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_icmp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                               hdr.inner_udp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                             hdr.inner_tcp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        }
                      }
                    } [] {
                       assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                       hdr.inner_ipv4.isValid:=(_ bv1 1);
                       last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                             hdr.inner_icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                           hdr.inner_udp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                         hdr.inner_tcp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    }
                  }
                }
              } [] {
                 assume (= (_ bv6 8) hdr.ipv4.protocol);
                 hdr.tcp.isValid:=(_ bv1 1);
                 fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                 fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                 parse_result:=(_ bv1 1)
              }
            }
          }
        }
      }
    } [] {
       assume (= (_ bv37120 16) look_eth);
       hdr.vlan_tag.isValid:=(_ bv1 1);
       hdr.vlan_tag.eth_type:=look_eth;
      {
         assume (not(= (_ bv33024 16) look_vlan));
         hdr.eth_type.isValid:=(_ bv1 1);
        {
           assume (not(= (_ bv34887 16) hdr.eth_type.value));
          {
             assume (not(= (_ bv2048 16) hdr.eth_type.value));
             parse_result:=(_ bv1 1)
          } [] {
             assume (= (_ bv2048 16) hdr.eth_type.value);
             hdr.ipv4.isValid:=(_ bv1 1);
             fabric_metadata.ip_proto:=hdr.ipv4.protocol;
             fabric_metadata.ip_eth_type:=(_ bv2048 16);
             fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
             fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
             last_ipv4_dscp:=hdr.ipv4.dscp;
            {
               assume (not(= (_ bv6 8) hdr.ipv4.protocol));
              {
                 assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                {
                   assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                   parse_result:=(_ bv1 1)
                } [] {
                   assume (= (_ bv1 8) hdr.ipv4.protocol);
                   hdr.icmp.isValid:=(_ bv1 1);
                   parse_result:=(_ bv1 1)
                }
              } [] {
                 assume (= (_ bv17 8) hdr.ipv4.protocol);
                 hdr.udp.isValid:=(_ bv1 1);
                 fabric_metadata.l4_sport:=hdr.udp.srcPort;
                 fabric_metadata.l4_dport:=hdr.udp.dstPort;
                {
                   assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                   parse_result:=(_ bv1 1)
                } [] {
                   assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                   hdr.gtpu.isValid:=(_ bv1 1);
                  {
                     assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                     hdr.gtpu_options.isValid:=(_ bv1 1);
                    {
                       assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                       hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                      {
                         assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                         hdr.inner_ipv4.isValid:=(_ bv1 1);
                         last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                        {
                           assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                          {
                             assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                            {
                               assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                               hdr.inner_icmp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                             hdr.inner_udp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                           hdr.inner_tcp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      }
                    }
                  } [] {
                     assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                     hdr.inner_ipv4.isValid:=(_ bv1 1);
                     last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                    {
                       assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                      {
                         assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                        {
                           assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                           hdr.inner_icmp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                         hdr.inner_udp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    } [] {
                       assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                       hdr.inner_tcp.isValid:=(_ bv1 1);
                       parse_result:=(_ bv1 1)
                    }
                  }
                }
              }
            } [] {
               assume (= (_ bv6 8) hdr.ipv4.protocol);
               hdr.tcp.isValid:=(_ bv1 1);
               fabric_metadata.l4_sport:=hdr.tcp.srcPort;
               fabric_metadata.l4_dport:=hdr.tcp.dstPort;
               parse_result:=(_ bv1 1)
            }
          }
        } [] {
           assume (= (_ bv34887 16) hdr.eth_type.value);
           hdr.mpls.isValid:=(_ bv1 1);
           fabric_metadata.mpls_label:=hdr.mpls.label;
           fabric_metadata.mpls_ttl:=hdr.mpls.ttl;
          {
             assume (not(= (_ bv4 4) look_mpls));
             fabric_metadata.vlan_id:=(_ bv4094 12);
             hdr.ethernet.isValid:=(_ bv1 1);
            {
               assume (not(= (_ bv34984 16) look_eth));
              {
                 assume (not(= (_ bv37120 16) look_eth));
                {
                   assume (not(= (_ bv33024 16) look_eth));
                   hdr.eth_type.isValid:=(_ bv1 1);
                  {
                     assume (not(= (_ bv34887 16) hdr.eth_type.value));
                    {
                       assume (not(= (_ bv2048 16) hdr.eth_type.value));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (= (_ bv2048 16) hdr.eth_type.value);
                       hdr.ipv4.isValid:=(_ bv1 1);
                       fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                       fabric_metadata.ip_eth_type:=(_ bv2048 16);
                       fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                       fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                       last_ipv4_dscp:=hdr.ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.ipv4.protocol);
                             hdr.icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.ipv4.protocol);
                           hdr.udp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.udp.srcPort;
                           fabric_metadata.l4_dport:=hdr.udp.dstPort;
                          {
                             assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                             hdr.gtpu.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                               hdr.gtpu_options.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                 hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                {
                                   assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                  {
                                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                         parse_result:=(_ bv1 1)
                                      } [] {
                                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_icmp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_udp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_tcp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                }
                              }
                            } [] {
                               assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                               hdr.inner_ipv4.isValid:=(_ bv1 1);
                               last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                              {
                                 assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_icmp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_udp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_tcp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            }
                          }
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.ipv4.protocol);
                         hdr.tcp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                         fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                         parse_result:=(_ bv1 1)
                      }
                    }
                  } [] {
                     assume (= (_ bv34887 16) hdr.eth_type.value);
                     parse_result:=(_ bv0 1)
                  }
                } [] {
                   assume (= (_ bv33024 16) look_eth);
                   hdr.vlan_tag.isValid:=(_ bv1 1);
                   hdr.vlan_tag.eth_type:=look_eth;
                  {
                     assume (not(= (_ bv33024 16) look_vlan));
                     hdr.eth_type.isValid:=(_ bv1 1);
                    {
                       assume (not(= (_ bv34887 16) hdr.eth_type.value));
                      {
                         assume (not(= (_ bv2048 16) hdr.eth_type.value));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv2048 16) hdr.eth_type.value);
                         hdr.ipv4.isValid:=(_ bv1 1);
                         fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                         fabric_metadata.ip_eth_type:=(_ bv2048 16);
                         fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                         fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                         last_ipv4_dscp:=hdr.ipv4.dscp;
                        {
                           assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                            {
                               assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv1 8) hdr.ipv4.protocol);
                               hdr.icmp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv17 8) hdr.ipv4.protocol);
                             hdr.udp.isValid:=(_ bv1 1);
                             fabric_metadata.l4_sport:=hdr.udp.srcPort;
                             fabric_metadata.l4_dport:=hdr.udp.dstPort;
                            {
                               assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                               hdr.gtpu.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                                 hdr.gtpu_options.isValid:=(_ bv1 1);
                                {
                                   assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                   hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                  {
                                     assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                     hdr.inner_ipv4.isValid:=(_ bv1 1);
                                     last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                    {
                                       assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                        {
                                           assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                           parse_result:=(_ bv1 1)
                                        } [] {
                                           assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                           hdr.inner_icmp.isValid:=(_ bv1 1);
                                           parse_result:=(_ bv1 1)
                                        }
                                      } [] {
                                         assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_udp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_tcp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  }
                                }
                              } [] {
                                 assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          }
                        } [] {
                           assume (= (_ bv6 8) hdr.ipv4.protocol);
                           hdr.tcp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                           fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                           parse_result:=(_ bv1 1)
                        }
                      }
                    } [] {
                       assume (= (_ bv34887 16) hdr.eth_type.value);
                       parse_result:=(_ bv0 1)
                    }
                  } [] {
                     assume (= (_ bv33024 16) look_vlan);
                     hdr.inner_vlan_tag.isValid:=(_ bv1 1);
                     hdr.inner_vlan_tag.eth_type:=look_vlan;
                     hdr.eth_type.isValid:=(_ bv1 1);
                    {
                       assume (not(= (_ bv34887 16) hdr.eth_type.value));
                      {
                         assume (not(= (_ bv2048 16) hdr.eth_type.value));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv2048 16) hdr.eth_type.value);
                         hdr.ipv4.isValid:=(_ bv1 1);
                         fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                         fabric_metadata.ip_eth_type:=(_ bv2048 16);
                         fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                         fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                         last_ipv4_dscp:=hdr.ipv4.dscp;
                        {
                           assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                            {
                               assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv1 8) hdr.ipv4.protocol);
                               hdr.icmp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv17 8) hdr.ipv4.protocol);
                             hdr.udp.isValid:=(_ bv1 1);
                             fabric_metadata.l4_sport:=hdr.udp.srcPort;
                             fabric_metadata.l4_dport:=hdr.udp.dstPort;
                            {
                               assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                               hdr.gtpu.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                                 hdr.gtpu_options.isValid:=(_ bv1 1);
                                {
                                   assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                   hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                  {
                                     assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                     hdr.inner_ipv4.isValid:=(_ bv1 1);
                                     last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                    {
                                       assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                        {
                                           assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                           parse_result:=(_ bv1 1)
                                        } [] {
                                           assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                           hdr.inner_icmp.isValid:=(_ bv1 1);
                                           parse_result:=(_ bv1 1)
                                        }
                                      } [] {
                                         assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_udp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_tcp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  }
                                }
                              } [] {
                                 assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          }
                        } [] {
                           assume (= (_ bv6 8) hdr.ipv4.protocol);
                           hdr.tcp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                           fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                           parse_result:=(_ bv1 1)
                        }
                      }
                    } [] {
                       assume (= (_ bv34887 16) hdr.eth_type.value);
                       parse_result:=(_ bv0 1)
                    }
                  }
                }
              } [] {
                 assume (= (_ bv37120 16) look_eth);
                 hdr.vlan_tag.isValid:=(_ bv1 1);
                 hdr.vlan_tag.eth_type:=look_eth;
                {
                   assume (not(= (_ bv33024 16) look_vlan));
                   hdr.eth_type.isValid:=(_ bv1 1);
                  {
                     assume (not(= (_ bv34887 16) hdr.eth_type.value));
                    {
                       assume (not(= (_ bv2048 16) hdr.eth_type.value));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (= (_ bv2048 16) hdr.eth_type.value);
                       hdr.ipv4.isValid:=(_ bv1 1);
                       fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                       fabric_metadata.ip_eth_type:=(_ bv2048 16);
                       fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                       fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                       last_ipv4_dscp:=hdr.ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.ipv4.protocol);
                             hdr.icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.ipv4.protocol);
                           hdr.udp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.udp.srcPort;
                           fabric_metadata.l4_dport:=hdr.udp.dstPort;
                          {
                             assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                             hdr.gtpu.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                               hdr.gtpu_options.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                 hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                {
                                   assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                  {
                                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                         parse_result:=(_ bv1 1)
                                      } [] {
                                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_icmp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_udp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_tcp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                }
                              }
                            } [] {
                               assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                               hdr.inner_ipv4.isValid:=(_ bv1 1);
                               last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                              {
                                 assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_icmp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_udp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_tcp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            }
                          }
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.ipv4.protocol);
                         hdr.tcp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                         fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                         parse_result:=(_ bv1 1)
                      }
                    }
                  } [] {
                     assume (= (_ bv34887 16) hdr.eth_type.value);
                     parse_result:=(_ bv0 1)
                  }
                } [] {
                   assume (= (_ bv33024 16) look_vlan);
                   hdr.inner_vlan_tag.isValid:=(_ bv1 1);
                   hdr.inner_vlan_tag.eth_type:=look_vlan;
                   hdr.eth_type.isValid:=(_ bv1 1);
                  {
                     assume (not(= (_ bv34887 16) hdr.eth_type.value));
                    {
                       assume (not(= (_ bv2048 16) hdr.eth_type.value));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (= (_ bv2048 16) hdr.eth_type.value);
                       hdr.ipv4.isValid:=(_ bv1 1);
                       fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                       fabric_metadata.ip_eth_type:=(_ bv2048 16);
                       fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                       fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                       last_ipv4_dscp:=hdr.ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.ipv4.protocol);
                             hdr.icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.ipv4.protocol);
                           hdr.udp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.udp.srcPort;
                           fabric_metadata.l4_dport:=hdr.udp.dstPort;
                          {
                             assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                             hdr.gtpu.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                               hdr.gtpu_options.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                 hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                {
                                   assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                  {
                                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                         parse_result:=(_ bv1 1)
                                      } [] {
                                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_icmp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_udp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_tcp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                }
                              }
                            } [] {
                               assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                               hdr.inner_ipv4.isValid:=(_ bv1 1);
                               last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                              {
                                 assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_icmp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_udp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_tcp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            }
                          }
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.ipv4.protocol);
                         hdr.tcp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                         fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                         parse_result:=(_ bv1 1)
                      }
                    }
                  } [] {
                     assume (= (_ bv34887 16) hdr.eth_type.value);
                     parse_result:=(_ bv0 1)
                  }
                }
              }
            } [] {
               assume (= (_ bv34984 16) look_eth);
               hdr.vlan_tag.isValid:=(_ bv1 1);
               hdr.vlan_tag.eth_type:=look_eth;
              {
                 assume (not(= (_ bv33024 16) look_vlan));
                 hdr.eth_type.isValid:=(_ bv1 1);
                {
                   assume (not(= (_ bv34887 16) hdr.eth_type.value));
                  {
                     assume (not(= (_ bv2048 16) hdr.eth_type.value));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (= (_ bv2048 16) hdr.eth_type.value);
                     hdr.ipv4.isValid:=(_ bv1 1);
                     fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                     fabric_metadata.ip_eth_type:=(_ bv2048 16);
                     fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                     fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                     last_ipv4_dscp:=hdr.ipv4.dscp;
                    {
                       assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                      {
                         assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv1 8) hdr.ipv4.protocol);
                           hdr.icmp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv17 8) hdr.ipv4.protocol);
                         hdr.udp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.udp.srcPort;
                         fabric_metadata.l4_dport:=hdr.udp.dstPort;
                        {
                           assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                           hdr.gtpu.isValid:=(_ bv1 1);
                          {
                             assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                             hdr.gtpu_options.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                               hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                              {
                                 assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          } [] {
                             assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                             hdr.inner_ipv4.isValid:=(_ bv1 1);
                             last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                            {
                               assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                              {
                                 assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_icmp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_udp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                               hdr.inner_tcp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          }
                        }
                      }
                    } [] {
                       assume (= (_ bv6 8) hdr.ipv4.protocol);
                       hdr.tcp.isValid:=(_ bv1 1);
                       fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                       fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                       parse_result:=(_ bv1 1)
                    }
                  }
                } [] {
                   assume (= (_ bv34887 16) hdr.eth_type.value);
                   parse_result:=(_ bv0 1)
                }
              } [] {
                 assume (= (_ bv33024 16) look_vlan);
                 hdr.inner_vlan_tag.isValid:=(_ bv1 1);
                 hdr.inner_vlan_tag.eth_type:=look_vlan;
                 hdr.eth_type.isValid:=(_ bv1 1);
                {
                   assume (not(= (_ bv34887 16) hdr.eth_type.value));
                  {
                     assume (not(= (_ bv2048 16) hdr.eth_type.value));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (= (_ bv2048 16) hdr.eth_type.value);
                     hdr.ipv4.isValid:=(_ bv1 1);
                     fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                     fabric_metadata.ip_eth_type:=(_ bv2048 16);
                     fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                     fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                     last_ipv4_dscp:=hdr.ipv4.dscp;
                    {
                       assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                      {
                         assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv1 8) hdr.ipv4.protocol);
                           hdr.icmp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv17 8) hdr.ipv4.protocol);
                         hdr.udp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.udp.srcPort;
                         fabric_metadata.l4_dport:=hdr.udp.dstPort;
                        {
                           assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                           hdr.gtpu.isValid:=(_ bv1 1);
                          {
                             assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                             hdr.gtpu_options.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                               hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                              {
                                 assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          } [] {
                             assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                             hdr.inner_ipv4.isValid:=(_ bv1 1);
                             last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                            {
                               assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                              {
                                 assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_icmp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_udp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                               hdr.inner_tcp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          }
                        }
                      }
                    } [] {
                       assume (= (_ bv6 8) hdr.ipv4.protocol);
                       hdr.tcp.isValid:=(_ bv1 1);
                       fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                       fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                       parse_result:=(_ bv1 1)
                    }
                  }
                } [] {
                   assume (= (_ bv34887 16) hdr.eth_type.value);
                   parse_result:=(_ bv0 1)
                }
              }
            }
          } [] {
             assume (= (_ bv4 4) look_mpls);
             hdr.ipv4.isValid:=(_ bv1 1);
             fabric_metadata.ip_proto:=hdr.ipv4.protocol;
             fabric_metadata.ip_eth_type:=(_ bv2048 16);
             fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
             fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
             last_ipv4_dscp:=hdr.ipv4.dscp;
            {
               assume (not(= (_ bv6 8) hdr.ipv4.protocol));
              {
                 assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                {
                   assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                   parse_result:=(_ bv1 1)
                } [] {
                   assume (= (_ bv1 8) hdr.ipv4.protocol);
                   hdr.icmp.isValid:=(_ bv1 1);
                   parse_result:=(_ bv1 1)
                }
              } [] {
                 assume (= (_ bv17 8) hdr.ipv4.protocol);
                 hdr.udp.isValid:=(_ bv1 1);
                 fabric_metadata.l4_sport:=hdr.udp.srcPort;
                 fabric_metadata.l4_dport:=hdr.udp.dstPort;
                {
                   assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                   parse_result:=(_ bv1 1)
                } [] {
                   assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                   hdr.gtpu.isValid:=(_ bv1 1);
                  {
                     assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                     hdr.gtpu_options.isValid:=(_ bv1 1);
                    {
                       assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                       hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                      {
                         assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                         hdr.inner_ipv4.isValid:=(_ bv1 1);
                         last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                        {
                           assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                          {
                             assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                            {
                               assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                               hdr.inner_icmp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                             hdr.inner_udp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                           hdr.inner_tcp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      }
                    }
                  } [] {
                     assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                     hdr.inner_ipv4.isValid:=(_ bv1 1);
                     last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                    {
                       assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                      {
                         assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                        {
                           assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                           hdr.inner_icmp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                         hdr.inner_udp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    } [] {
                       assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                       hdr.inner_tcp.isValid:=(_ bv1 1);
                       parse_result:=(_ bv1 1)
                    }
                  }
                }
              }
            } [] {
               assume (= (_ bv6 8) hdr.ipv4.protocol);
               hdr.tcp.isValid:=(_ bv1 1);
               fabric_metadata.l4_sport:=hdr.tcp.srcPort;
               fabric_metadata.l4_dport:=hdr.tcp.dstPort;
               parse_result:=(_ bv1 1)
            }
          }
        }
      } [] {
         assume (= (_ bv33024 16) look_vlan);
         hdr.inner_vlan_tag.isValid:=(_ bv1 1);
         hdr.inner_vlan_tag.eth_type:=look_vlan;
         hdr.eth_type.isValid:=(_ bv1 1);
        {
           assume (not(= (_ bv34887 16) hdr.eth_type.value));
          {
             assume (not(= (_ bv2048 16) hdr.eth_type.value));
             parse_result:=(_ bv1 1)
          } [] {
             assume (= (_ bv2048 16) hdr.eth_type.value);
             hdr.ipv4.isValid:=(_ bv1 1);
             fabric_metadata.ip_proto:=hdr.ipv4.protocol;
             fabric_metadata.ip_eth_type:=(_ bv2048 16);
             fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
             fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
             last_ipv4_dscp:=hdr.ipv4.dscp;
            {
               assume (not(= (_ bv6 8) hdr.ipv4.protocol));
              {
                 assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                {
                   assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                   parse_result:=(_ bv1 1)
                } [] {
                   assume (= (_ bv1 8) hdr.ipv4.protocol);
                   hdr.icmp.isValid:=(_ bv1 1);
                   parse_result:=(_ bv1 1)
                }
              } [] {
                 assume (= (_ bv17 8) hdr.ipv4.protocol);
                 hdr.udp.isValid:=(_ bv1 1);
                 fabric_metadata.l4_sport:=hdr.udp.srcPort;
                 fabric_metadata.l4_dport:=hdr.udp.dstPort;
                {
                   assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                   parse_result:=(_ bv1 1)
                } [] {
                   assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                   hdr.gtpu.isValid:=(_ bv1 1);
                  {
                     assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                     hdr.gtpu_options.isValid:=(_ bv1 1);
                    {
                       assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                       hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                      {
                         assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                         hdr.inner_ipv4.isValid:=(_ bv1 1);
                         last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                        {
                           assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                          {
                             assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                            {
                               assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                               hdr.inner_icmp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                             hdr.inner_udp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                           hdr.inner_tcp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      }
                    }
                  } [] {
                     assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                     hdr.inner_ipv4.isValid:=(_ bv1 1);
                     last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                    {
                       assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                      {
                         assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                        {
                           assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                           hdr.inner_icmp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                         hdr.inner_udp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    } [] {
                       assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                       hdr.inner_tcp.isValid:=(_ bv1 1);
                       parse_result:=(_ bv1 1)
                    }
                  }
                }
              }
            } [] {
               assume (= (_ bv6 8) hdr.ipv4.protocol);
               hdr.tcp.isValid:=(_ bv1 1);
               fabric_metadata.l4_sport:=hdr.tcp.srcPort;
               fabric_metadata.l4_dport:=hdr.tcp.dstPort;
               parse_result:=(_ bv1 1)
            }
          }
        } [] {
           assume (= (_ bv34887 16) hdr.eth_type.value);
           hdr.mpls.isValid:=(_ bv1 1);
           fabric_metadata.mpls_label:=hdr.mpls.label;
           fabric_metadata.mpls_ttl:=hdr.mpls.ttl;
          {
             assume (not(= (_ bv4 4) look_mpls));
             fabric_metadata.vlan_id:=(_ bv4094 12);
             hdr.ethernet.isValid:=(_ bv1 1);
            {
               assume (not(= (_ bv34984 16) look_eth));
              {
                 assume (not(= (_ bv37120 16) look_eth));
                {
                   assume (not(= (_ bv33024 16) look_eth));
                   hdr.eth_type.isValid:=(_ bv1 1);
                  {
                     assume (not(= (_ bv34887 16) hdr.eth_type.value));
                    {
                       assume (not(= (_ bv2048 16) hdr.eth_type.value));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (= (_ bv2048 16) hdr.eth_type.value);
                       hdr.ipv4.isValid:=(_ bv1 1);
                       fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                       fabric_metadata.ip_eth_type:=(_ bv2048 16);
                       fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                       fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                       last_ipv4_dscp:=hdr.ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.ipv4.protocol);
                             hdr.icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.ipv4.protocol);
                           hdr.udp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.udp.srcPort;
                           fabric_metadata.l4_dport:=hdr.udp.dstPort;
                          {
                             assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                             hdr.gtpu.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                               hdr.gtpu_options.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                 hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                {
                                   assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                  {
                                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                         parse_result:=(_ bv1 1)
                                      } [] {
                                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_icmp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_udp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_tcp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                }
                              }
                            } [] {
                               assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                               hdr.inner_ipv4.isValid:=(_ bv1 1);
                               last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                              {
                                 assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_icmp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_udp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_tcp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            }
                          }
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.ipv4.protocol);
                         hdr.tcp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                         fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                         parse_result:=(_ bv1 1)
                      }
                    }
                  } [] {
                     assume (= (_ bv34887 16) hdr.eth_type.value);
                     parse_result:=(_ bv0 1)
                  }
                } [] {
                   assume (= (_ bv33024 16) look_eth);
                   hdr.vlan_tag.isValid:=(_ bv1 1);
                   hdr.vlan_tag.eth_type:=look_eth;
                  {
                     assume (not(= (_ bv33024 16) look_vlan));
                     hdr.eth_type.isValid:=(_ bv1 1);
                    {
                       assume (not(= (_ bv34887 16) hdr.eth_type.value));
                      {
                         assume (not(= (_ bv2048 16) hdr.eth_type.value));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv2048 16) hdr.eth_type.value);
                         hdr.ipv4.isValid:=(_ bv1 1);
                         fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                         fabric_metadata.ip_eth_type:=(_ bv2048 16);
                         fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                         fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                         last_ipv4_dscp:=hdr.ipv4.dscp;
                        {
                           assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                            {
                               assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv1 8) hdr.ipv4.protocol);
                               hdr.icmp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv17 8) hdr.ipv4.protocol);
                             hdr.udp.isValid:=(_ bv1 1);
                             fabric_metadata.l4_sport:=hdr.udp.srcPort;
                             fabric_metadata.l4_dport:=hdr.udp.dstPort;
                            {
                               assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                               hdr.gtpu.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                                 hdr.gtpu_options.isValid:=(_ bv1 1);
                                {
                                   assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                   hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                  {
                                     assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                     hdr.inner_ipv4.isValid:=(_ bv1 1);
                                     last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                    {
                                       assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                        {
                                           assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                           parse_result:=(_ bv1 1)
                                        } [] {
                                           assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                           hdr.inner_icmp.isValid:=(_ bv1 1);
                                           parse_result:=(_ bv1 1)
                                        }
                                      } [] {
                                         assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_udp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_tcp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  }
                                }
                              } [] {
                                 assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          }
                        } [] {
                           assume (= (_ bv6 8) hdr.ipv4.protocol);
                           hdr.tcp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                           fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                           parse_result:=(_ bv1 1)
                        }
                      }
                    } [] {
                       assume (= (_ bv34887 16) hdr.eth_type.value);
                       parse_result:=(_ bv0 1)
                    }
                  } [] {
                     assume (= (_ bv33024 16) look_vlan);
                     hdr.inner_vlan_tag.isValid:=(_ bv1 1);
                     hdr.inner_vlan_tag.eth_type:=look_vlan;
                     hdr.eth_type.isValid:=(_ bv1 1);
                    {
                       assume (not(= (_ bv34887 16) hdr.eth_type.value));
                      {
                         assume (not(= (_ bv2048 16) hdr.eth_type.value));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv2048 16) hdr.eth_type.value);
                         hdr.ipv4.isValid:=(_ bv1 1);
                         fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                         fabric_metadata.ip_eth_type:=(_ bv2048 16);
                         fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                         fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                         last_ipv4_dscp:=hdr.ipv4.dscp;
                        {
                           assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                            {
                               assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv1 8) hdr.ipv4.protocol);
                               hdr.icmp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv17 8) hdr.ipv4.protocol);
                             hdr.udp.isValid:=(_ bv1 1);
                             fabric_metadata.l4_sport:=hdr.udp.srcPort;
                             fabric_metadata.l4_dport:=hdr.udp.dstPort;
                            {
                               assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                               hdr.gtpu.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                                 hdr.gtpu_options.isValid:=(_ bv1 1);
                                {
                                   assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                   hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                  {
                                     assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                     hdr.inner_ipv4.isValid:=(_ bv1 1);
                                     last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                    {
                                       assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                        {
                                           assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                           parse_result:=(_ bv1 1)
                                        } [] {
                                           assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                           hdr.inner_icmp.isValid:=(_ bv1 1);
                                           parse_result:=(_ bv1 1)
                                        }
                                      } [] {
                                         assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_udp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_tcp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  }
                                }
                              } [] {
                                 assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          }
                        } [] {
                           assume (= (_ bv6 8) hdr.ipv4.protocol);
                           hdr.tcp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                           fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                           parse_result:=(_ bv1 1)
                        }
                      }
                    } [] {
                       assume (= (_ bv34887 16) hdr.eth_type.value);
                       parse_result:=(_ bv0 1)
                    }
                  }
                }
              } [] {
                 assume (= (_ bv37120 16) look_eth);
                 hdr.vlan_tag.isValid:=(_ bv1 1);
                 hdr.vlan_tag.eth_type:=look_eth;
                {
                   assume (not(= (_ bv33024 16) look_vlan));
                   hdr.eth_type.isValid:=(_ bv1 1);
                  {
                     assume (not(= (_ bv34887 16) hdr.eth_type.value));
                    {
                       assume (not(= (_ bv2048 16) hdr.eth_type.value));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (= (_ bv2048 16) hdr.eth_type.value);
                       hdr.ipv4.isValid:=(_ bv1 1);
                       fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                       fabric_metadata.ip_eth_type:=(_ bv2048 16);
                       fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                       fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                       last_ipv4_dscp:=hdr.ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.ipv4.protocol);
                             hdr.icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.ipv4.protocol);
                           hdr.udp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.udp.srcPort;
                           fabric_metadata.l4_dport:=hdr.udp.dstPort;
                          {
                             assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                             hdr.gtpu.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                               hdr.gtpu_options.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                 hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                {
                                   assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                  {
                                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                         parse_result:=(_ bv1 1)
                                      } [] {
                                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_icmp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_udp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_tcp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                }
                              }
                            } [] {
                               assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                               hdr.inner_ipv4.isValid:=(_ bv1 1);
                               last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                              {
                                 assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_icmp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_udp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_tcp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            }
                          }
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.ipv4.protocol);
                         hdr.tcp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                         fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                         parse_result:=(_ bv1 1)
                      }
                    }
                  } [] {
                     assume (= (_ bv34887 16) hdr.eth_type.value);
                     parse_result:=(_ bv0 1)
                  }
                } [] {
                   assume (= (_ bv33024 16) look_vlan);
                   hdr.inner_vlan_tag.isValid:=(_ bv1 1);
                   hdr.inner_vlan_tag.eth_type:=look_vlan;
                   hdr.eth_type.isValid:=(_ bv1 1);
                  {
                     assume (not(= (_ bv34887 16) hdr.eth_type.value));
                    {
                       assume (not(= (_ bv2048 16) hdr.eth_type.value));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (= (_ bv2048 16) hdr.eth_type.value);
                       hdr.ipv4.isValid:=(_ bv1 1);
                       fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                       fabric_metadata.ip_eth_type:=(_ bv2048 16);
                       fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                       fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                       last_ipv4_dscp:=hdr.ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.ipv4.protocol);
                             hdr.icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.ipv4.protocol);
                           hdr.udp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.udp.srcPort;
                           fabric_metadata.l4_dport:=hdr.udp.dstPort;
                          {
                             assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                             hdr.gtpu.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                               hdr.gtpu_options.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                 hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                {
                                   assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                  {
                                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                         parse_result:=(_ bv1 1)
                                      } [] {
                                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_icmp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_udp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_tcp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                }
                              }
                            } [] {
                               assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                               hdr.inner_ipv4.isValid:=(_ bv1 1);
                               last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                              {
                                 assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_icmp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_udp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_tcp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            }
                          }
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.ipv4.protocol);
                         hdr.tcp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                         fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                         parse_result:=(_ bv1 1)
                      }
                    }
                  } [] {
                     assume (= (_ bv34887 16) hdr.eth_type.value);
                     parse_result:=(_ bv0 1)
                  }
                }
              }
            } [] {
               assume (= (_ bv34984 16) look_eth);
               hdr.vlan_tag.isValid:=(_ bv1 1);
               hdr.vlan_tag.eth_type:=look_eth;
              {
                 assume (not(= (_ bv33024 16) look_vlan));
                 hdr.eth_type.isValid:=(_ bv1 1);
                {
                   assume (not(= (_ bv34887 16) hdr.eth_type.value));
                  {
                     assume (not(= (_ bv2048 16) hdr.eth_type.value));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (= (_ bv2048 16) hdr.eth_type.value);
                     hdr.ipv4.isValid:=(_ bv1 1);
                     fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                     fabric_metadata.ip_eth_type:=(_ bv2048 16);
                     fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                     fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                     last_ipv4_dscp:=hdr.ipv4.dscp;
                    {
                       assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                      {
                         assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv1 8) hdr.ipv4.protocol);
                           hdr.icmp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv17 8) hdr.ipv4.protocol);
                         hdr.udp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.udp.srcPort;
                         fabric_metadata.l4_dport:=hdr.udp.dstPort;
                        {
                           assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                           hdr.gtpu.isValid:=(_ bv1 1);
                          {
                             assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                             hdr.gtpu_options.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                               hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                              {
                                 assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          } [] {
                             assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                             hdr.inner_ipv4.isValid:=(_ bv1 1);
                             last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                            {
                               assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                              {
                                 assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_icmp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_udp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                               hdr.inner_tcp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          }
                        }
                      }
                    } [] {
                       assume (= (_ bv6 8) hdr.ipv4.protocol);
                       hdr.tcp.isValid:=(_ bv1 1);
                       fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                       fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                       parse_result:=(_ bv1 1)
                    }
                  }
                } [] {
                   assume (= (_ bv34887 16) hdr.eth_type.value);
                   parse_result:=(_ bv0 1)
                }
              } [] {
                 assume (= (_ bv33024 16) look_vlan);
                 hdr.inner_vlan_tag.isValid:=(_ bv1 1);
                 hdr.inner_vlan_tag.eth_type:=look_vlan;
                 hdr.eth_type.isValid:=(_ bv1 1);
                {
                   assume (not(= (_ bv34887 16) hdr.eth_type.value));
                  {
                     assume (not(= (_ bv2048 16) hdr.eth_type.value));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (= (_ bv2048 16) hdr.eth_type.value);
                     hdr.ipv4.isValid:=(_ bv1 1);
                     fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                     fabric_metadata.ip_eth_type:=(_ bv2048 16);
                     fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                     fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                     last_ipv4_dscp:=hdr.ipv4.dscp;
                    {
                       assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                      {
                         assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv1 8) hdr.ipv4.protocol);
                           hdr.icmp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv17 8) hdr.ipv4.protocol);
                         hdr.udp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.udp.srcPort;
                         fabric_metadata.l4_dport:=hdr.udp.dstPort;
                        {
                           assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                           hdr.gtpu.isValid:=(_ bv1 1);
                          {
                             assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                             hdr.gtpu_options.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                               hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                              {
                                 assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          } [] {
                             assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                             hdr.inner_ipv4.isValid:=(_ bv1 1);
                             last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                            {
                               assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                              {
                                 assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_icmp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_udp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                               hdr.inner_tcp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          }
                        }
                      }
                    } [] {
                       assume (= (_ bv6 8) hdr.ipv4.protocol);
                       hdr.tcp.isValid:=(_ bv1 1);
                       fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                       fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                       parse_result:=(_ bv1 1)
                    }
                  }
                } [] {
                   assume (= (_ bv34887 16) hdr.eth_type.value);
                   parse_result:=(_ bv0 1)
                }
              }
            }
          } [] {
             assume (= (_ bv4 4) look_mpls);
             hdr.ipv4.isValid:=(_ bv1 1);
             fabric_metadata.ip_proto:=hdr.ipv4.protocol;
             fabric_metadata.ip_eth_type:=(_ bv2048 16);
             fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
             fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
             last_ipv4_dscp:=hdr.ipv4.dscp;
            {
               assume (not(= (_ bv6 8) hdr.ipv4.protocol));
              {
                 assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                {
                   assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                   parse_result:=(_ bv1 1)
                } [] {
                   assume (= (_ bv1 8) hdr.ipv4.protocol);
                   hdr.icmp.isValid:=(_ bv1 1);
                   parse_result:=(_ bv1 1)
                }
              } [] {
                 assume (= (_ bv17 8) hdr.ipv4.protocol);
                 hdr.udp.isValid:=(_ bv1 1);
                 fabric_metadata.l4_sport:=hdr.udp.srcPort;
                 fabric_metadata.l4_dport:=hdr.udp.dstPort;
                {
                   assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                   parse_result:=(_ bv1 1)
                } [] {
                   assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                   hdr.gtpu.isValid:=(_ bv1 1);
                  {
                     assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                     hdr.gtpu_options.isValid:=(_ bv1 1);
                    {
                       assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                       hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                      {
                         assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                         hdr.inner_ipv4.isValid:=(_ bv1 1);
                         last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                        {
                           assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                          {
                             assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                            {
                               assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                               hdr.inner_icmp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                             hdr.inner_udp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                           hdr.inner_tcp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      }
                    }
                  } [] {
                     assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                     hdr.inner_ipv4.isValid:=(_ bv1 1);
                     last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                    {
                       assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                      {
                         assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                        {
                           assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                           hdr.inner_icmp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                         hdr.inner_udp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    } [] {
                       assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                       hdr.inner_tcp.isValid:=(_ bv1 1);
                       parse_result:=(_ bv1 1)
                    }
                  }
                }
              }
            } [] {
               assume (= (_ bv6 8) hdr.ipv4.protocol);
               hdr.tcp.isValid:=(_ bv1 1);
               fabric_metadata.l4_sport:=hdr.tcp.srcPort;
               fabric_metadata.l4_dport:=hdr.tcp.dstPort;
               parse_result:=(_ bv1 1)
            }
          }
        }
      }
    }
  } [] {
     assume (= (_ bv34984 16) look_eth);
     hdr.vlan_tag.isValid:=(_ bv1 1);
     hdr.vlan_tag.eth_type:=look_eth;
    {
       assume (not(= (_ bv33024 16) look_vlan));
       hdr.eth_type.isValid:=(_ bv1 1);
      {
         assume (not(= (_ bv34887 16) hdr.eth_type.value));
        {
           assume (not(= (_ bv2048 16) hdr.eth_type.value));
           parse_result:=(_ bv1 1)
        } [] {
           assume (= (_ bv2048 16) hdr.eth_type.value);
           hdr.ipv4.isValid:=(_ bv1 1);
           fabric_metadata.ip_proto:=hdr.ipv4.protocol;
           fabric_metadata.ip_eth_type:=(_ bv2048 16);
           fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
           fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
           last_ipv4_dscp:=hdr.ipv4.dscp;
          {
             assume (not(= (_ bv6 8) hdr.ipv4.protocol));
            {
               assume (not(= (_ bv17 8) hdr.ipv4.protocol));
              {
                 assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                 parse_result:=(_ bv1 1)
              } [] {
                 assume (= (_ bv1 8) hdr.ipv4.protocol);
                 hdr.icmp.isValid:=(_ bv1 1);
                 parse_result:=(_ bv1 1)
              }
            } [] {
               assume (= (_ bv17 8) hdr.ipv4.protocol);
               hdr.udp.isValid:=(_ bv1 1);
               fabric_metadata.l4_sport:=hdr.udp.srcPort;
               fabric_metadata.l4_dport:=hdr.udp.dstPort;
              {
                 assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                 parse_result:=(_ bv1 1)
              } [] {
                 assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                 hdr.gtpu.isValid:=(_ bv1 1);
                {
                   assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                   hdr.gtpu_options.isValid:=(_ bv1 1);
                  {
                     assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                     hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                    {
                       assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                       hdr.inner_ipv4.isValid:=(_ bv1 1);
                       last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                             hdr.inner_icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                           hdr.inner_udp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                         hdr.inner_tcp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    }
                  }
                } [] {
                   assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                  {
                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                    {
                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                      {
                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                         hdr.inner_icmp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    } [] {
                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                       hdr.inner_udp.isValid:=(_ bv1 1);
                       parse_result:=(_ bv1 1)
                    }
                  } [] {
                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                     hdr.inner_tcp.isValid:=(_ bv1 1);
                     parse_result:=(_ bv1 1)
                  }
                }
              }
            }
          } [] {
             assume (= (_ bv6 8) hdr.ipv4.protocol);
             hdr.tcp.isValid:=(_ bv1 1);
             fabric_metadata.l4_sport:=hdr.tcp.srcPort;
             fabric_metadata.l4_dport:=hdr.tcp.dstPort;
             parse_result:=(_ bv1 1)
          }
        }
      } [] {
         assume (= (_ bv34887 16) hdr.eth_type.value);
         hdr.mpls.isValid:=(_ bv1 1);
         fabric_metadata.mpls_label:=hdr.mpls.label;
         fabric_metadata.mpls_ttl:=hdr.mpls.ttl;
        {
           assume (not(= (_ bv4 4) look_mpls));
           fabric_metadata.vlan_id:=(_ bv4094 12);
           hdr.ethernet.isValid:=(_ bv1 1);
          {
             assume (not(= (_ bv34984 16) look_eth));
            {
               assume (not(= (_ bv37120 16) look_eth));
              {
                 assume (not(= (_ bv33024 16) look_eth));
                 hdr.eth_type.isValid:=(_ bv1 1);
                {
                   assume (not(= (_ bv34887 16) hdr.eth_type.value));
                  {
                     assume (not(= (_ bv2048 16) hdr.eth_type.value));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (= (_ bv2048 16) hdr.eth_type.value);
                     hdr.ipv4.isValid:=(_ bv1 1);
                     fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                     fabric_metadata.ip_eth_type:=(_ bv2048 16);
                     fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                     fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                     last_ipv4_dscp:=hdr.ipv4.dscp;
                    {
                       assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                      {
                         assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv1 8) hdr.ipv4.protocol);
                           hdr.icmp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv17 8) hdr.ipv4.protocol);
                         hdr.udp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.udp.srcPort;
                         fabric_metadata.l4_dport:=hdr.udp.dstPort;
                        {
                           assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                           hdr.gtpu.isValid:=(_ bv1 1);
                          {
                             assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                             hdr.gtpu_options.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                               hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                              {
                                 assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          } [] {
                             assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                             hdr.inner_ipv4.isValid:=(_ bv1 1);
                             last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                            {
                               assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                              {
                                 assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_icmp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_udp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                               hdr.inner_tcp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          }
                        }
                      }
                    } [] {
                       assume (= (_ bv6 8) hdr.ipv4.protocol);
                       hdr.tcp.isValid:=(_ bv1 1);
                       fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                       fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                       parse_result:=(_ bv1 1)
                    }
                  }
                } [] {
                   assume (= (_ bv34887 16) hdr.eth_type.value);
                   parse_result:=(_ bv0 1)
                }
              } [] {
                 assume (= (_ bv33024 16) look_eth);
                 hdr.vlan_tag.isValid:=(_ bv1 1);
                 hdr.vlan_tag.eth_type:=look_eth;
                {
                   assume (not(= (_ bv33024 16) look_vlan));
                   hdr.eth_type.isValid:=(_ bv1 1);
                  {
                     assume (not(= (_ bv34887 16) hdr.eth_type.value));
                    {
                       assume (not(= (_ bv2048 16) hdr.eth_type.value));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (= (_ bv2048 16) hdr.eth_type.value);
                       hdr.ipv4.isValid:=(_ bv1 1);
                       fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                       fabric_metadata.ip_eth_type:=(_ bv2048 16);
                       fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                       fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                       last_ipv4_dscp:=hdr.ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.ipv4.protocol);
                             hdr.icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.ipv4.protocol);
                           hdr.udp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.udp.srcPort;
                           fabric_metadata.l4_dport:=hdr.udp.dstPort;
                          {
                             assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                             hdr.gtpu.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                               hdr.gtpu_options.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                 hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                {
                                   assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                  {
                                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                         parse_result:=(_ bv1 1)
                                      } [] {
                                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_icmp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_udp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_tcp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                }
                              }
                            } [] {
                               assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                               hdr.inner_ipv4.isValid:=(_ bv1 1);
                               last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                              {
                                 assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_icmp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_udp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_tcp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            }
                          }
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.ipv4.protocol);
                         hdr.tcp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                         fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                         parse_result:=(_ bv1 1)
                      }
                    }
                  } [] {
                     assume (= (_ bv34887 16) hdr.eth_type.value);
                     parse_result:=(_ bv0 1)
                  }
                } [] {
                   assume (= (_ bv33024 16) look_vlan);
                   hdr.inner_vlan_tag.isValid:=(_ bv1 1);
                   hdr.inner_vlan_tag.eth_type:=look_vlan;
                   hdr.eth_type.isValid:=(_ bv1 1);
                  {
                     assume (not(= (_ bv34887 16) hdr.eth_type.value));
                    {
                       assume (not(= (_ bv2048 16) hdr.eth_type.value));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (= (_ bv2048 16) hdr.eth_type.value);
                       hdr.ipv4.isValid:=(_ bv1 1);
                       fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                       fabric_metadata.ip_eth_type:=(_ bv2048 16);
                       fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                       fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                       last_ipv4_dscp:=hdr.ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.ipv4.protocol);
                             hdr.icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.ipv4.protocol);
                           hdr.udp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.udp.srcPort;
                           fabric_metadata.l4_dport:=hdr.udp.dstPort;
                          {
                             assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                             hdr.gtpu.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                               hdr.gtpu_options.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                 hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                {
                                   assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                  {
                                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                         parse_result:=(_ bv1 1)
                                      } [] {
                                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_icmp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_udp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_tcp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                }
                              }
                            } [] {
                               assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                               hdr.inner_ipv4.isValid:=(_ bv1 1);
                               last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                              {
                                 assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_icmp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_udp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_tcp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            }
                          }
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.ipv4.protocol);
                         hdr.tcp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                         fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                         parse_result:=(_ bv1 1)
                      }
                    }
                  } [] {
                     assume (= (_ bv34887 16) hdr.eth_type.value);
                     parse_result:=(_ bv0 1)
                  }
                }
              }
            } [] {
               assume (= (_ bv37120 16) look_eth);
               hdr.vlan_tag.isValid:=(_ bv1 1);
               hdr.vlan_tag.eth_type:=look_eth;
              {
                 assume (not(= (_ bv33024 16) look_vlan));
                 hdr.eth_type.isValid:=(_ bv1 1);
                {
                   assume (not(= (_ bv34887 16) hdr.eth_type.value));
                  {
                     assume (not(= (_ bv2048 16) hdr.eth_type.value));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (= (_ bv2048 16) hdr.eth_type.value);
                     hdr.ipv4.isValid:=(_ bv1 1);
                     fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                     fabric_metadata.ip_eth_type:=(_ bv2048 16);
                     fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                     fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                     last_ipv4_dscp:=hdr.ipv4.dscp;
                    {
                       assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                      {
                         assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv1 8) hdr.ipv4.protocol);
                           hdr.icmp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv17 8) hdr.ipv4.protocol);
                         hdr.udp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.udp.srcPort;
                         fabric_metadata.l4_dport:=hdr.udp.dstPort;
                        {
                           assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                           hdr.gtpu.isValid:=(_ bv1 1);
                          {
                             assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                             hdr.gtpu_options.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                               hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                              {
                                 assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          } [] {
                             assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                             hdr.inner_ipv4.isValid:=(_ bv1 1);
                             last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                            {
                               assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                              {
                                 assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_icmp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_udp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                               hdr.inner_tcp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          }
                        }
                      }
                    } [] {
                       assume (= (_ bv6 8) hdr.ipv4.protocol);
                       hdr.tcp.isValid:=(_ bv1 1);
                       fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                       fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                       parse_result:=(_ bv1 1)
                    }
                  }
                } [] {
                   assume (= (_ bv34887 16) hdr.eth_type.value);
                   parse_result:=(_ bv0 1)
                }
              } [] {
                 assume (= (_ bv33024 16) look_vlan);
                 hdr.inner_vlan_tag.isValid:=(_ bv1 1);
                 hdr.inner_vlan_tag.eth_type:=look_vlan;
                 hdr.eth_type.isValid:=(_ bv1 1);
                {
                   assume (not(= (_ bv34887 16) hdr.eth_type.value));
                  {
                     assume (not(= (_ bv2048 16) hdr.eth_type.value));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (= (_ bv2048 16) hdr.eth_type.value);
                     hdr.ipv4.isValid:=(_ bv1 1);
                     fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                     fabric_metadata.ip_eth_type:=(_ bv2048 16);
                     fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                     fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                     last_ipv4_dscp:=hdr.ipv4.dscp;
                    {
                       assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                      {
                         assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv1 8) hdr.ipv4.protocol);
                           hdr.icmp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv17 8) hdr.ipv4.protocol);
                         hdr.udp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.udp.srcPort;
                         fabric_metadata.l4_dport:=hdr.udp.dstPort;
                        {
                           assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                           hdr.gtpu.isValid:=(_ bv1 1);
                          {
                             assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                             hdr.gtpu_options.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                               hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                              {
                                 assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          } [] {
                             assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                             hdr.inner_ipv4.isValid:=(_ bv1 1);
                             last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                            {
                               assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                              {
                                 assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_icmp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_udp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                               hdr.inner_tcp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          }
                        }
                      }
                    } [] {
                       assume (= (_ bv6 8) hdr.ipv4.protocol);
                       hdr.tcp.isValid:=(_ bv1 1);
                       fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                       fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                       parse_result:=(_ bv1 1)
                    }
                  }
                } [] {
                   assume (= (_ bv34887 16) hdr.eth_type.value);
                   parse_result:=(_ bv0 1)
                }
              }
            }
          } [] {
             assume (= (_ bv34984 16) look_eth);
             hdr.vlan_tag.isValid:=(_ bv1 1);
             hdr.vlan_tag.eth_type:=look_eth;
            {
               assume (not(= (_ bv33024 16) look_vlan));
               hdr.eth_type.isValid:=(_ bv1 1);
              {
                 assume (not(= (_ bv34887 16) hdr.eth_type.value));
                {
                   assume (not(= (_ bv2048 16) hdr.eth_type.value));
                   parse_result:=(_ bv1 1)
                } [] {
                   assume (= (_ bv2048 16) hdr.eth_type.value);
                   hdr.ipv4.isValid:=(_ bv1 1);
                   fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                   fabric_metadata.ip_eth_type:=(_ bv2048 16);
                   fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                   fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                   last_ipv4_dscp:=hdr.ipv4.dscp;
                  {
                     assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                    {
                       assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                      {
                         assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv1 8) hdr.ipv4.protocol);
                         hdr.icmp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    } [] {
                       assume (= (_ bv17 8) hdr.ipv4.protocol);
                       hdr.udp.isValid:=(_ bv1 1);
                       fabric_metadata.l4_sport:=hdr.udp.srcPort;
                       fabric_metadata.l4_dport:=hdr.udp.dstPort;
                      {
                         assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                         hdr.gtpu.isValid:=(_ bv1 1);
                        {
                           assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                           hdr.gtpu_options.isValid:=(_ bv1 1);
                          {
                             assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                             hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                            {
                               assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                               hdr.inner_ipv4.isValid:=(_ bv1 1);
                               last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                              {
                                 assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_icmp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_udp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_tcp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            }
                          }
                        } [] {
                           assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                           hdr.inner_ipv4.isValid:=(_ bv1 1);
                           last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                          {
                             assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                            {
                               assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                              {
                                 assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_icmp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                               hdr.inner_udp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                             hdr.inner_tcp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        }
                      }
                    }
                  } [] {
                     assume (= (_ bv6 8) hdr.ipv4.protocol);
                     hdr.tcp.isValid:=(_ bv1 1);
                     fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                     fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                     parse_result:=(_ bv1 1)
                  }
                }
              } [] {
                 assume (= (_ bv34887 16) hdr.eth_type.value);
                 parse_result:=(_ bv0 1)
              }
            } [] {
               assume (= (_ bv33024 16) look_vlan);
               hdr.inner_vlan_tag.isValid:=(_ bv1 1);
               hdr.inner_vlan_tag.eth_type:=look_vlan;
               hdr.eth_type.isValid:=(_ bv1 1);
              {
                 assume (not(= (_ bv34887 16) hdr.eth_type.value));
                {
                   assume (not(= (_ bv2048 16) hdr.eth_type.value));
                   parse_result:=(_ bv1 1)
                } [] {
                   assume (= (_ bv2048 16) hdr.eth_type.value);
                   hdr.ipv4.isValid:=(_ bv1 1);
                   fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                   fabric_metadata.ip_eth_type:=(_ bv2048 16);
                   fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                   fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                   last_ipv4_dscp:=hdr.ipv4.dscp;
                  {
                     assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                    {
                       assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                      {
                         assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv1 8) hdr.ipv4.protocol);
                         hdr.icmp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    } [] {
                       assume (= (_ bv17 8) hdr.ipv4.protocol);
                       hdr.udp.isValid:=(_ bv1 1);
                       fabric_metadata.l4_sport:=hdr.udp.srcPort;
                       fabric_metadata.l4_dport:=hdr.udp.dstPort;
                      {
                         assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                         hdr.gtpu.isValid:=(_ bv1 1);
                        {
                           assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                           hdr.gtpu_options.isValid:=(_ bv1 1);
                          {
                             assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                             hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                            {
                               assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                               hdr.inner_ipv4.isValid:=(_ bv1 1);
                               last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                              {
                                 assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_icmp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_udp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_tcp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            }
                          }
                        } [] {
                           assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                           hdr.inner_ipv4.isValid:=(_ bv1 1);
                           last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                          {
                             assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                            {
                               assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                              {
                                 assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_icmp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                               hdr.inner_udp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                             hdr.inner_tcp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        }
                      }
                    }
                  } [] {
                     assume (= (_ bv6 8) hdr.ipv4.protocol);
                     hdr.tcp.isValid:=(_ bv1 1);
                     fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                     fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                     parse_result:=(_ bv1 1)
                  }
                }
              } [] {
                 assume (= (_ bv34887 16) hdr.eth_type.value);
                 parse_result:=(_ bv0 1)
              }
            }
          }
        } [] {
           assume (= (_ bv4 4) look_mpls);
           hdr.ipv4.isValid:=(_ bv1 1);
           fabric_metadata.ip_proto:=hdr.ipv4.protocol;
           fabric_metadata.ip_eth_type:=(_ bv2048 16);
           fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
           fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
           last_ipv4_dscp:=hdr.ipv4.dscp;
          {
             assume (not(= (_ bv6 8) hdr.ipv4.protocol));
            {
               assume (not(= (_ bv17 8) hdr.ipv4.protocol));
              {
                 assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                 parse_result:=(_ bv1 1)
              } [] {
                 assume (= (_ bv1 8) hdr.ipv4.protocol);
                 hdr.icmp.isValid:=(_ bv1 1);
                 parse_result:=(_ bv1 1)
              }
            } [] {
               assume (= (_ bv17 8) hdr.ipv4.protocol);
               hdr.udp.isValid:=(_ bv1 1);
               fabric_metadata.l4_sport:=hdr.udp.srcPort;
               fabric_metadata.l4_dport:=hdr.udp.dstPort;
              {
                 assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                 parse_result:=(_ bv1 1)
              } [] {
                 assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                 hdr.gtpu.isValid:=(_ bv1 1);
                {
                   assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                   hdr.gtpu_options.isValid:=(_ bv1 1);
                  {
                     assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                     hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                    {
                       assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                       hdr.inner_ipv4.isValid:=(_ bv1 1);
                       last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                             hdr.inner_icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                           hdr.inner_udp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                         hdr.inner_tcp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    }
                  }
                } [] {
                   assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                  {
                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                    {
                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                      {
                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                         hdr.inner_icmp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    } [] {
                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                       hdr.inner_udp.isValid:=(_ bv1 1);
                       parse_result:=(_ bv1 1)
                    }
                  } [] {
                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                     hdr.inner_tcp.isValid:=(_ bv1 1);
                     parse_result:=(_ bv1 1)
                  }
                }
              }
            }
          } [] {
             assume (= (_ bv6 8) hdr.ipv4.protocol);
             hdr.tcp.isValid:=(_ bv1 1);
             fabric_metadata.l4_sport:=hdr.tcp.srcPort;
             fabric_metadata.l4_dport:=hdr.tcp.dstPort;
             parse_result:=(_ bv1 1)
          }
        }
      }
    } [] {
       assume (= (_ bv33024 16) look_vlan);
       hdr.inner_vlan_tag.isValid:=(_ bv1 1);
       hdr.inner_vlan_tag.eth_type:=look_vlan;
       hdr.eth_type.isValid:=(_ bv1 1);
      {
         assume (not(= (_ bv34887 16) hdr.eth_type.value));
        {
           assume (not(= (_ bv2048 16) hdr.eth_type.value));
           parse_result:=(_ bv1 1)
        } [] {
           assume (= (_ bv2048 16) hdr.eth_type.value);
           hdr.ipv4.isValid:=(_ bv1 1);
           fabric_metadata.ip_proto:=hdr.ipv4.protocol;
           fabric_metadata.ip_eth_type:=(_ bv2048 16);
           fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
           fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
           last_ipv4_dscp:=hdr.ipv4.dscp;
          {
             assume (not(= (_ bv6 8) hdr.ipv4.protocol));
            {
               assume (not(= (_ bv17 8) hdr.ipv4.protocol));
              {
                 assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                 parse_result:=(_ bv1 1)
              } [] {
                 assume (= (_ bv1 8) hdr.ipv4.protocol);
                 hdr.icmp.isValid:=(_ bv1 1);
                 parse_result:=(_ bv1 1)
              }
            } [] {
               assume (= (_ bv17 8) hdr.ipv4.protocol);
               hdr.udp.isValid:=(_ bv1 1);
               fabric_metadata.l4_sport:=hdr.udp.srcPort;
               fabric_metadata.l4_dport:=hdr.udp.dstPort;
              {
                 assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                 parse_result:=(_ bv1 1)
              } [] {
                 assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                 hdr.gtpu.isValid:=(_ bv1 1);
                {
                   assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                   hdr.gtpu_options.isValid:=(_ bv1 1);
                  {
                     assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                     hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                    {
                       assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                       hdr.inner_ipv4.isValid:=(_ bv1 1);
                       last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                             hdr.inner_icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                           hdr.inner_udp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                         hdr.inner_tcp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    }
                  }
                } [] {
                   assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                  {
                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                    {
                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                      {
                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                         hdr.inner_icmp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    } [] {
                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                       hdr.inner_udp.isValid:=(_ bv1 1);
                       parse_result:=(_ bv1 1)
                    }
                  } [] {
                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                     hdr.inner_tcp.isValid:=(_ bv1 1);
                     parse_result:=(_ bv1 1)
                  }
                }
              }
            }
          } [] {
             assume (= (_ bv6 8) hdr.ipv4.protocol);
             hdr.tcp.isValid:=(_ bv1 1);
             fabric_metadata.l4_sport:=hdr.tcp.srcPort;
             fabric_metadata.l4_dport:=hdr.tcp.dstPort;
             parse_result:=(_ bv1 1)
          }
        }
      } [] {
         assume (= (_ bv34887 16) hdr.eth_type.value);
         hdr.mpls.isValid:=(_ bv1 1);
         fabric_metadata.mpls_label:=hdr.mpls.label;
         fabric_metadata.mpls_ttl:=hdr.mpls.ttl;
        {
           assume (not(= (_ bv4 4) look_mpls));
           fabric_metadata.vlan_id:=(_ bv4094 12);
           hdr.ethernet.isValid:=(_ bv1 1);
          {
             assume (not(= (_ bv34984 16) look_eth));
            {
               assume (not(= (_ bv37120 16) look_eth));
              {
                 assume (not(= (_ bv33024 16) look_eth));
                 hdr.eth_type.isValid:=(_ bv1 1);
                {
                   assume (not(= (_ bv34887 16) hdr.eth_type.value));
                  {
                     assume (not(= (_ bv2048 16) hdr.eth_type.value));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (= (_ bv2048 16) hdr.eth_type.value);
                     hdr.ipv4.isValid:=(_ bv1 1);
                     fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                     fabric_metadata.ip_eth_type:=(_ bv2048 16);
                     fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                     fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                     last_ipv4_dscp:=hdr.ipv4.dscp;
                    {
                       assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                      {
                         assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv1 8) hdr.ipv4.protocol);
                           hdr.icmp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv17 8) hdr.ipv4.protocol);
                         hdr.udp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.udp.srcPort;
                         fabric_metadata.l4_dport:=hdr.udp.dstPort;
                        {
                           assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                           hdr.gtpu.isValid:=(_ bv1 1);
                          {
                             assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                             hdr.gtpu_options.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                               hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                              {
                                 assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          } [] {
                             assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                             hdr.inner_ipv4.isValid:=(_ bv1 1);
                             last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                            {
                               assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                              {
                                 assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_icmp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_udp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                               hdr.inner_tcp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          }
                        }
                      }
                    } [] {
                       assume (= (_ bv6 8) hdr.ipv4.protocol);
                       hdr.tcp.isValid:=(_ bv1 1);
                       fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                       fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                       parse_result:=(_ bv1 1)
                    }
                  }
                } [] {
                   assume (= (_ bv34887 16) hdr.eth_type.value);
                   parse_result:=(_ bv0 1)
                }
              } [] {
                 assume (= (_ bv33024 16) look_eth);
                 hdr.vlan_tag.isValid:=(_ bv1 1);
                 hdr.vlan_tag.eth_type:=look_eth;
                {
                   assume (not(= (_ bv33024 16) look_vlan));
                   hdr.eth_type.isValid:=(_ bv1 1);
                  {
                     assume (not(= (_ bv34887 16) hdr.eth_type.value));
                    {
                       assume (not(= (_ bv2048 16) hdr.eth_type.value));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (= (_ bv2048 16) hdr.eth_type.value);
                       hdr.ipv4.isValid:=(_ bv1 1);
                       fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                       fabric_metadata.ip_eth_type:=(_ bv2048 16);
                       fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                       fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                       last_ipv4_dscp:=hdr.ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.ipv4.protocol);
                             hdr.icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.ipv4.protocol);
                           hdr.udp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.udp.srcPort;
                           fabric_metadata.l4_dport:=hdr.udp.dstPort;
                          {
                             assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                             hdr.gtpu.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                               hdr.gtpu_options.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                 hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                {
                                   assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                  {
                                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                         parse_result:=(_ bv1 1)
                                      } [] {
                                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_icmp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_udp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_tcp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                }
                              }
                            } [] {
                               assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                               hdr.inner_ipv4.isValid:=(_ bv1 1);
                               last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                              {
                                 assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_icmp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_udp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_tcp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            }
                          }
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.ipv4.protocol);
                         hdr.tcp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                         fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                         parse_result:=(_ bv1 1)
                      }
                    }
                  } [] {
                     assume (= (_ bv34887 16) hdr.eth_type.value);
                     parse_result:=(_ bv0 1)
                  }
                } [] {
                   assume (= (_ bv33024 16) look_vlan);
                   hdr.inner_vlan_tag.isValid:=(_ bv1 1);
                   hdr.inner_vlan_tag.eth_type:=look_vlan;
                   hdr.eth_type.isValid:=(_ bv1 1);
                  {
                     assume (not(= (_ bv34887 16) hdr.eth_type.value));
                    {
                       assume (not(= (_ bv2048 16) hdr.eth_type.value));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (= (_ bv2048 16) hdr.eth_type.value);
                       hdr.ipv4.isValid:=(_ bv1 1);
                       fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                       fabric_metadata.ip_eth_type:=(_ bv2048 16);
                       fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                       fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                       last_ipv4_dscp:=hdr.ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.ipv4.protocol);
                             hdr.icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.ipv4.protocol);
                           hdr.udp.isValid:=(_ bv1 1);
                           fabric_metadata.l4_sport:=hdr.udp.srcPort;
                           fabric_metadata.l4_dport:=hdr.udp.dstPort;
                          {
                             assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                             hdr.gtpu.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                               hdr.gtpu_options.isValid:=(_ bv1 1);
                              {
                                 assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                                 hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                                {
                                   assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                  {
                                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                      {
                                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                         parse_result:=(_ bv1 1)
                                      } [] {
                                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                         hdr.inner_icmp.isValid:=(_ bv1 1);
                                         parse_result:=(_ bv1 1)
                                      }
                                    } [] {
                                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_udp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_tcp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                }
                              }
                            } [] {
                               assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                               hdr.inner_ipv4.isValid:=(_ bv1 1);
                               last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                              {
                                 assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_icmp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_udp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_tcp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            }
                          }
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.ipv4.protocol);
                         hdr.tcp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                         fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                         parse_result:=(_ bv1 1)
                      }
                    }
                  } [] {
                     assume (= (_ bv34887 16) hdr.eth_type.value);
                     parse_result:=(_ bv0 1)
                  }
                }
              }
            } [] {
               assume (= (_ bv37120 16) look_eth);
               hdr.vlan_tag.isValid:=(_ bv1 1);
               hdr.vlan_tag.eth_type:=look_eth;
              {
                 assume (not(= (_ bv33024 16) look_vlan));
                 hdr.eth_type.isValid:=(_ bv1 1);
                {
                   assume (not(= (_ bv34887 16) hdr.eth_type.value));
                  {
                     assume (not(= (_ bv2048 16) hdr.eth_type.value));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (= (_ bv2048 16) hdr.eth_type.value);
                     hdr.ipv4.isValid:=(_ bv1 1);
                     fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                     fabric_metadata.ip_eth_type:=(_ bv2048 16);
                     fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                     fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                     last_ipv4_dscp:=hdr.ipv4.dscp;
                    {
                       assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                      {
                         assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv1 8) hdr.ipv4.protocol);
                           hdr.icmp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv17 8) hdr.ipv4.protocol);
                         hdr.udp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.udp.srcPort;
                         fabric_metadata.l4_dport:=hdr.udp.dstPort;
                        {
                           assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                           hdr.gtpu.isValid:=(_ bv1 1);
                          {
                             assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                             hdr.gtpu_options.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                               hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                              {
                                 assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          } [] {
                             assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                             hdr.inner_ipv4.isValid:=(_ bv1 1);
                             last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                            {
                               assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                              {
                                 assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_icmp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_udp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                               hdr.inner_tcp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          }
                        }
                      }
                    } [] {
                       assume (= (_ bv6 8) hdr.ipv4.protocol);
                       hdr.tcp.isValid:=(_ bv1 1);
                       fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                       fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                       parse_result:=(_ bv1 1)
                    }
                  }
                } [] {
                   assume (= (_ bv34887 16) hdr.eth_type.value);
                   parse_result:=(_ bv0 1)
                }
              } [] {
                 assume (= (_ bv33024 16) look_vlan);
                 hdr.inner_vlan_tag.isValid:=(_ bv1 1);
                 hdr.inner_vlan_tag.eth_type:=look_vlan;
                 hdr.eth_type.isValid:=(_ bv1 1);
                {
                   assume (not(= (_ bv34887 16) hdr.eth_type.value));
                  {
                     assume (not(= (_ bv2048 16) hdr.eth_type.value));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (= (_ bv2048 16) hdr.eth_type.value);
                     hdr.ipv4.isValid:=(_ bv1 1);
                     fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                     fabric_metadata.ip_eth_type:=(_ bv2048 16);
                     fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                     fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                     last_ipv4_dscp:=hdr.ipv4.dscp;
                    {
                       assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                      {
                         assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                        {
                           assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (= (_ bv1 8) hdr.ipv4.protocol);
                           hdr.icmp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv17 8) hdr.ipv4.protocol);
                         hdr.udp.isValid:=(_ bv1 1);
                         fabric_metadata.l4_sport:=hdr.udp.srcPort;
                         fabric_metadata.l4_dport:=hdr.udp.dstPort;
                        {
                           assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                           parse_result:=(_ bv1 1)
                        } [] {
                           assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                           hdr.gtpu.isValid:=(_ bv1 1);
                          {
                             assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                             hdr.gtpu_options.isValid:=(_ bv1 1);
                            {
                               assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                               hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                              {
                                 assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                                 hdr.inner_ipv4.isValid:=(_ bv1 1);
                                 last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                                {
                                   assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                    {
                                       assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                       parse_result:=(_ bv1 1)
                                    } [] {
                                       assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                       hdr.inner_icmp.isValid:=(_ bv1 1);
                                       parse_result:=(_ bv1 1)
                                    }
                                  } [] {
                                     assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_udp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_tcp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              }
                            }
                          } [] {
                             assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                             hdr.inner_ipv4.isValid:=(_ bv1 1);
                             last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                            {
                               assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                              {
                                 assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                   parse_result:=(_ bv1 1)
                                } [] {
                                   assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_icmp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_udp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                               hdr.inner_tcp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          }
                        }
                      }
                    } [] {
                       assume (= (_ bv6 8) hdr.ipv4.protocol);
                       hdr.tcp.isValid:=(_ bv1 1);
                       fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                       fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                       parse_result:=(_ bv1 1)
                    }
                  }
                } [] {
                   assume (= (_ bv34887 16) hdr.eth_type.value);
                   parse_result:=(_ bv0 1)
                }
              }
            }
          } [] {
             assume (= (_ bv34984 16) look_eth);
             hdr.vlan_tag.isValid:=(_ bv1 1);
             hdr.vlan_tag.eth_type:=look_eth;
            {
               assume (not(= (_ bv33024 16) look_vlan));
               hdr.eth_type.isValid:=(_ bv1 1);
              {
                 assume (not(= (_ bv34887 16) hdr.eth_type.value));
                {
                   assume (not(= (_ bv2048 16) hdr.eth_type.value));
                   parse_result:=(_ bv1 1)
                } [] {
                   assume (= (_ bv2048 16) hdr.eth_type.value);
                   hdr.ipv4.isValid:=(_ bv1 1);
                   fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                   fabric_metadata.ip_eth_type:=(_ bv2048 16);
                   fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                   fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                   last_ipv4_dscp:=hdr.ipv4.dscp;
                  {
                     assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                    {
                       assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                      {
                         assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv1 8) hdr.ipv4.protocol);
                         hdr.icmp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    } [] {
                       assume (= (_ bv17 8) hdr.ipv4.protocol);
                       hdr.udp.isValid:=(_ bv1 1);
                       fabric_metadata.l4_sport:=hdr.udp.srcPort;
                       fabric_metadata.l4_dport:=hdr.udp.dstPort;
                      {
                         assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                         hdr.gtpu.isValid:=(_ bv1 1);
                        {
                           assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                           hdr.gtpu_options.isValid:=(_ bv1 1);
                          {
                             assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                             hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                            {
                               assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                               hdr.inner_ipv4.isValid:=(_ bv1 1);
                               last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                              {
                                 assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_icmp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_udp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_tcp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            }
                          }
                        } [] {
                           assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                           hdr.inner_ipv4.isValid:=(_ bv1 1);
                           last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                          {
                             assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                            {
                               assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                              {
                                 assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_icmp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                               hdr.inner_udp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                             hdr.inner_tcp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        }
                      }
                    }
                  } [] {
                     assume (= (_ bv6 8) hdr.ipv4.protocol);
                     hdr.tcp.isValid:=(_ bv1 1);
                     fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                     fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                     parse_result:=(_ bv1 1)
                  }
                }
              } [] {
                 assume (= (_ bv34887 16) hdr.eth_type.value);
                 parse_result:=(_ bv0 1)
              }
            } [] {
               assume (= (_ bv33024 16) look_vlan);
               hdr.inner_vlan_tag.isValid:=(_ bv1 1);
               hdr.inner_vlan_tag.eth_type:=look_vlan;
               hdr.eth_type.isValid:=(_ bv1 1);
              {
                 assume (not(= (_ bv34887 16) hdr.eth_type.value));
                {
                   assume (not(= (_ bv2048 16) hdr.eth_type.value));
                   parse_result:=(_ bv1 1)
                } [] {
                   assume (= (_ bv2048 16) hdr.eth_type.value);
                   hdr.ipv4.isValid:=(_ bv1 1);
                   fabric_metadata.ip_proto:=hdr.ipv4.protocol;
                   fabric_metadata.ip_eth_type:=(_ bv2048 16);
                   fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
                   fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
                   last_ipv4_dscp:=hdr.ipv4.dscp;
                  {
                     assume (not(= (_ bv6 8) hdr.ipv4.protocol));
                    {
                       assume (not(= (_ bv17 8) hdr.ipv4.protocol));
                      {
                         assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv1 8) hdr.ipv4.protocol);
                         hdr.icmp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    } [] {
                       assume (= (_ bv17 8) hdr.ipv4.protocol);
                       hdr.udp.isValid:=(_ bv1 1);
                       fabric_metadata.l4_sport:=hdr.udp.srcPort;
                       fabric_metadata.l4_dport:=hdr.udp.dstPort;
                      {
                         assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                         hdr.gtpu.isValid:=(_ bv1 1);
                        {
                           assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                           hdr.gtpu_options.isValid:=(_ bv1 1);
                          {
                             assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                             hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                            {
                               assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                               parse_result:=(_ bv1 1)
                            } [] {
                               assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                               hdr.inner_ipv4.isValid:=(_ bv1 1);
                               last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                              {
                                 assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                                {
                                   assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                                  {
                                     assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                     parse_result:=(_ bv1 1)
                                  } [] {
                                     assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                     hdr.inner_icmp.isValid:=(_ bv1 1);
                                     parse_result:=(_ bv1 1)
                                  }
                                } [] {
                                   assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                                   hdr.inner_udp.isValid:=(_ bv1 1);
                                   parse_result:=(_ bv1 1)
                                }
                              } [] {
                                 assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_tcp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            }
                          }
                        } [] {
                           assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                           hdr.inner_ipv4.isValid:=(_ bv1 1);
                           last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                          {
                             assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                            {
                               assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                              {
                                 assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                                 parse_result:=(_ bv1 1)
                              } [] {
                                 assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                                 hdr.inner_icmp.isValid:=(_ bv1 1);
                                 parse_result:=(_ bv1 1)
                              }
                            } [] {
                               assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                               hdr.inner_udp.isValid:=(_ bv1 1);
                               parse_result:=(_ bv1 1)
                            }
                          } [] {
                             assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                             hdr.inner_tcp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        }
                      }
                    }
                  } [] {
                     assume (= (_ bv6 8) hdr.ipv4.protocol);
                     hdr.tcp.isValid:=(_ bv1 1);
                     fabric_metadata.l4_sport:=hdr.tcp.srcPort;
                     fabric_metadata.l4_dport:=hdr.tcp.dstPort;
                     parse_result:=(_ bv1 1)
                  }
                }
              } [] {
                 assume (= (_ bv34887 16) hdr.eth_type.value);
                 parse_result:=(_ bv0 1)
              }
            }
          }
        } [] {
           assume (= (_ bv4 4) look_mpls);
           hdr.ipv4.isValid:=(_ bv1 1);
           fabric_metadata.ip_proto:=hdr.ipv4.protocol;
           fabric_metadata.ip_eth_type:=(_ bv2048 16);
           fabric_metadata.ipv4_src_addr:=hdr.ipv4.srcAddr;
           fabric_metadata.ipv4_dst_addr:=hdr.ipv4.dstAddr;
           last_ipv4_dscp:=hdr.ipv4.dscp;
          {
             assume (not(= (_ bv6 8) hdr.ipv4.protocol));
            {
               assume (not(= (_ bv17 8) hdr.ipv4.protocol));
              {
                 assume (not(= (_ bv1 8) hdr.ipv4.protocol));
                 parse_result:=(_ bv1 1)
              } [] {
                 assume (= (_ bv1 8) hdr.ipv4.protocol);
                 hdr.icmp.isValid:=(_ bv1 1);
                 parse_result:=(_ bv1 1)
              }
            } [] {
               assume (= (_ bv17 8) hdr.ipv4.protocol);
               hdr.udp.isValid:=(_ bv1 1);
               fabric_metadata.l4_sport:=hdr.udp.srcPort;
               fabric_metadata.l4_dport:=hdr.udp.dstPort;
              {
                 assume (not(and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype)));
                 parse_result:=(_ bv1 1)
              } [] {
                 assume (and
  (= (_ bv2152 16) hdr.udp.dstPort)
  (= (_ bv1 4) gtpu_version)
  (= (_ bv255 8) gtpu_msgtype));
                 hdr.gtpu.isValid:=(_ bv1 1);
                {
                   assume (not(and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag)));
                   hdr.gtpu_options.isValid:=(_ bv1 1);
                  {
                     assume (not(and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len)));
                     parse_result:=(_ bv1 1)
                  } [] {
                     assume (and
  (= (_ bv133 8) hdr.gtpu_options.next_ext)
  (= (_ bv1 8) gtpu_ext_len));
                     hdr.gtpu_ext_psc.isValid:=(_ bv1 1);
                    {
                       assume (not(= (_ bv0 4) hdr.gtpu_ext_psc.next_ext));
                       parse_result:=(_ bv1 1)
                    } [] {
                       assume (= (_ bv0 4) hdr.gtpu_ext_psc.next_ext);
                       hdr.inner_ipv4.isValid:=(_ bv1 1);
                       last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                      {
                         assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                        {
                           assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                          {
                             assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                             parse_result:=(_ bv1 1)
                          } [] {
                             assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                             hdr.inner_icmp.isValid:=(_ bv1 1);
                             parse_result:=(_ bv1 1)
                          }
                        } [] {
                           assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                           hdr.inner_udp.isValid:=(_ bv1 1);
                           parse_result:=(_ bv1 1)
                        }
                      } [] {
                         assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                         hdr.inner_tcp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    }
                  }
                } [] {
                   assume (and
  (= (_ bv0 1) hdr.gtpu.ex_flag)
  (= (_ bv0 1) hdr.gtpu.seq_flag)
  (= (_ bv0 1) hdr.gtpu.npdu_flag));
                   hdr.inner_ipv4.isValid:=(_ bv1 1);
                   last_ipv4_dscp:=hdr.inner_ipv4.dscp;
                  {
                     assume (not(= (_ bv6 8) hdr.inner_ipv4.protocol));
                    {
                       assume (not(= (_ bv17 8) hdr.inner_ipv4.protocol));
                      {
                         assume (not(= (_ bv1 8) hdr.inner_ipv4.protocol));
                         parse_result:=(_ bv1 1)
                      } [] {
                         assume (= (_ bv1 8) hdr.inner_ipv4.protocol);
                         hdr.inner_icmp.isValid:=(_ bv1 1);
                         parse_result:=(_ bv1 1)
                      }
                    } [] {
                       assume (= (_ bv17 8) hdr.inner_ipv4.protocol);
                       hdr.inner_udp.isValid:=(_ bv1 1);
                       parse_result:=(_ bv1 1)
                    }
                  } [] {
                     assume (= (_ bv6 8) hdr.inner_ipv4.protocol);
                     hdr.inner_tcp.isValid:=(_ bv1 1);
                     parse_result:=(_ bv1 1)
                  }
                }
              }
            }
          } [] {
             assume (= (_ bv6 8) hdr.ipv4.protocol);
             hdr.tcp.isValid:=(_ bv1 1);
             fabric_metadata.l4_sport:=hdr.tcp.srcPort;
             fabric_metadata.l4_dport:=hdr.tcp.dstPort;
             parse_result:=(_ bv1 1)
          }
        }
      }
    }
  }
} [] {
   assume (= (_ bv510 9) standard_metadata.ingress_port);
  {
     assume (not(= (_ bv0 1) look_packet_out));
     parse_result:=(_ bv1 1)
  } [] {
     assume (= (_ bv0 1) look_packet_out);
     hdr.packet_out.isValid:=(_ bv1 1);
     parse_result:=(_ bv1 1)
  }
};
{
   assume (not(= parse_result (_ bv1 1)));
   standard_metadata.egress_spec:=(_ bv511 9)
} [] {
   assume (= parse_result (_ bv1 1));
   fabric_metadata.lkp.is_ipv4:=(_ bv0 1);
   fabric_metadata.lkp.ipv4_src:=(_ bv0 32);
   fabric_metadata.lkp.ipv4_dst:=(_ bv0 32);
   fabric_metadata.lkp.ip_proto:=(_ bv0 8);
   fabric_metadata.lkp.l4_sport:=(_ bv0 16);
   fabric_metadata.lkp.l4_dport:=(_ bv0 16);
   fabric_metadata.lkp.icmp_type:=(_ bv0 8);
   fabric_metadata.lkp.icmp_code:=(_ bv0 8);
  {
     assume (not(= (_ bv1 1) hdr.inner_ipv4.isValid));
    {
       assume (not(= (_ bv1 1) hdr.ipv4.isValid))
    } [] {
       assume (= (_ bv1 1) hdr.ipv4.isValid);
       fabric_metadata.lkp.is_ipv4:=(_ bv1 1);
       fabric_metadata.lkp.ipv4_src:=hdr.ipv4.srcAddr;
       fabric_metadata.lkp.ipv4_dst:=hdr.ipv4.dstAddr;
       fabric_metadata.lkp.ip_proto:=hdr.ipv4.protocol;
      {
         assume (not(= (_ bv1 1) hdr.tcp.isValid));
        {
           assume (not(= (_ bv1 1) hdr.udp.isValid));
          {
             assume (not(= (_ bv1 1) hdr.icmp.isValid))
          } [] {
             assume (= (_ bv1 1) hdr.icmp.isValid);
             fabric_metadata.lkp.icmp_type:=hdr.icmp.type;
             fabric_metadata.lkp.icmp_code:=hdr.icmp.code
          }
        } [] {
           assume (= (_ bv1 1) hdr.udp.isValid);
           fabric_metadata.lkp.l4_sport:=hdr.udp.srcPort;
           fabric_metadata.lkp.l4_dport:=hdr.udp.dstPort
        }
      } [] {
         assume (= (_ bv1 1) hdr.tcp.isValid);
         fabric_metadata.lkp.l4_sport:=hdr.tcp.srcPort;
         fabric_metadata.lkp.l4_dport:=hdr.tcp.dstPort
      }
    }
  } [] {
     assume (= (_ bv1 1) hdr.inner_ipv4.isValid);
     fabric_metadata.lkp.is_ipv4:=(_ bv1 1);
     fabric_metadata.lkp.ipv4_src:=hdr.inner_ipv4.srcAddr;
     fabric_metadata.lkp.ipv4_dst:=hdr.inner_ipv4.dstAddr;
     fabric_metadata.lkp.ip_proto:=hdr.inner_ipv4.protocol;
    {
       assume (not(= (_ bv1 1) hdr.inner_tcp.isValid));
      {
         assume (not(= (_ bv1 1) hdr.inner_udp.isValid));
        {
           assume (not(= (_ bv1 1) hdr.inner_icmp.isValid))
        } [] {
           assume (= (_ bv1 1) hdr.inner_icmp.isValid);
           fabric_metadata.lkp.icmp_type:=hdr.inner_icmp.type;
           fabric_metadata.lkp.icmp_code:=hdr.inner_icmp.code
        }
      } [] {
         assume (= (_ bv1 1) hdr.inner_udp.isValid);
         fabric_metadata.lkp.l4_sport:=hdr.inner_udp.srcPort;
         fabric_metadata.lkp.l4_dport:=hdr.inner_udp.dstPort
      }
    } [] {
       assume (= (_ bv1 1) hdr.inner_tcp.isValid);
       fabric_metadata.lkp.l4_sport:=hdr.inner_tcp.srcPort;
       fabric_metadata.lkp.l4_dport:=hdr.inner_tcp.dstPort
    }
  };
  {
     assume (not(= (_ bv1 1) hdr.packet_out.isValid))
  } [] {
     assume (= (_ bv1 1) hdr.packet_out.isValid);
     standard_metadata.egress_spec:=hdr.packet_out.egress_port;
     hdr.packet_out.isValid:=(_ bv0 1);
     fabric_metadata.is_controller_packet_out:=(_ bv1 1);
     exit:=(_ bv1 1)
  };
  {
     assume (= (_ bv1 1) exit)
  } [] {
     assume (not(= (_ bv1 1) exit));
     classifier.apply(){
	\(slice_id (_ BitVec 4)) (tc (_ BitVec 2))  -> {
		fabric_metadata.slice_id:=slice_id
		fabric_metadata.tc:=tc
	}
	\ -> {
		fabric_metadata.slice_id:=((_ extract 5 2) hdr.ipv4.dscp)
		fabric_metadata.tc:=((_ extract 1 0) hdr.ipv4.dscp)
	}
	\ -> {
		fabric_metadata.slice_id:=(_ bv0 4)
		fabric_metadata.tc:=(_ bv0 2)
	}};
    {
       assume (not(= (_ bv0 1) fabric_metadata.is_controller_packet_out))
    } [] {
       assume (= (_ bv0 1) fabric_metadata.is_controller_packet_out);
      {
         assume (not(= (_ bv1 1) hdr.vlan_tag.isValid))
      } [] {
         assume (= (_ bv1 1) hdr.vlan_tag.isValid);
         fabric_metadata.vlan_id:=hdr.vlan_tag.vlan_id;
         fabric_metadata.vlan_pri:=hdr.vlan_tag.pri;
         fabric_metadata.vlan_cfi:=hdr.vlan_tag.cfi
      };
      {
         assume (not(= (_ bv1 1) hdr.mpls.isValid))
      } [] {
         assume (= (_ bv1 1) hdr.mpls.isValid);
         fabric_metadata.mpls_ttl:=(_ bv65 8)
      };
       ingress_port_vlan.apply(){
	\ -> {
		fabric_metadata.skip_forwarding:=(_ bv1 1)
		fabric_metadata.skip_next:=(_ bv1 1)
		fabric_metadata.port_type:=(_ bv0 2)
	}
	\(port_type (_ BitVec 2))  -> {
		fabric_metadata.port_type:=port_type
	}
	\(vlan_id (_ BitVec 12)) (port_type (_ BitVec 2))  -> {
		fabric_metadata.vlan_id:=vlan_id
		fabric_metadata.port_type:=port_type
	}};
       fwd_classifier.apply(){
	\(fwd_type (_ BitVec 3))  -> {
		fabric_metadata.fwd_type:=fwd_type
	}
	\ -> {
		fabric_metadata.fwd_type:=(_ bv0 3)
	}};
      {
         assume (not(= (_ bv0 1) fabric_metadata.skip_forwarding))
      } [] {
         assume (= (_ bv0 1) fabric_metadata.skip_forwarding);
        {
           assume (not(= (_ bv0 3) fabric_metadata.fwd_type));
          {
             assume (not(= (_ bv1 3) fabric_metadata.fwd_type));
            {
               assume (not(= (_ bv2 3) fabric_metadata.fwd_type))
            } [] {
               assume (= (_ bv2 3) fabric_metadata.fwd_type);
               routing_v4.apply(){
	\(next_id (_ BitVec 32))  -> {
		fabric_metadata.next_id:=next_id
	}
	\ -> {
	}
	\ -> {
	}}
            }
          } [] {
             assume (= (_ bv1 3) fabric_metadata.fwd_type);
             mpls.apply(){
	\(next_id (_ BitVec 32))  -> {
		fabric_metadata.mpls_label:=(_ bv0 20)
		fabric_metadata.next_id:=next_id
	}
	\ -> {
	}}
          }
        } [] {
           assume (= (_ bv0 3) fabric_metadata.fwd_type);
           bridging.apply(){
	\(next_id (_ BitVec 32))  -> {
		fabric_metadata.next_id:=next_id
	}
	\ -> {
	}}
        }
      };
      {
         assume (not(= (_ bv0 1) fabric_metadata.skip_next))
      } [] {
         assume (= (_ bv0 1) fabric_metadata.skip_next);
         next_mpls.apply(){
	\(label (_ BitVec 20))  -> {
		fabric_metadata.mpls_label:=label
	}
	\ -> {
	}};
         next_vlan.apply(){
	\(vlan_id (_ BitVec 12))  -> {
		fabric_metadata.vlan_id:=vlan_id
	}
	\ -> {
	}}
      };
       acl.apply(){
	\(next_id (_ BitVec 32))  -> {
		fabric_metadata.next_id:=next_id
	}
	\ -> {
		standard_metadata.egress_spec:=(_ bv510 9)
		fabric_metadata.skip_next:=(_ bv1 1)
	}
	\(clone_id (_ BitVec 32))  -> {
	}
	\ -> {
		standard_metadata.egress_spec:=(_ bv511 9)
		fabric_metadata.skip_next:=(_ bv1 1)
	}
	\ -> {
	}};
      {
         assume (not(= (_ bv0 1) fabric_metadata.skip_next))
      } [] {
         assume (= (_ bv0 1) fabric_metadata.skip_next);
         xconnect.apply(){
	\(port_num (_ BitVec 9))  -> {
		standard_metadata.egress_spec:=port_num
	}
	\(next_id (_ BitVec 32))  -> {
		fabric_metadata.next_id:=next_id
	}
	\ -> {
	}};
         hashed.apply(){
	\(port_num (_ BitVec 9))  -> {
		standard_metadata.egress_spec:=port_num
	}
	\(port_num (_ BitVec 9)) (smac (_ BitVec 48)) (dmac (_ BitVec 48))  -> {
		hdr.ethernet.srcAddr:=smac
		hdr.ethernet.dstAddr:=dmac
		standard_metadata.egress_spec:=port_num
	}
	\ -> {
	}};
         multicast.apply(){
	\(group_id (_ BitVec 32))  -> {
		standard_metadata.mcast_grp:=group_id
		fabric_metadata.is_multicast:=(_ bv1 1)
	}
	\ -> {
	}}
      };
       slice_tc:=(concat fabric_metadata.slice_id fabric_metadata.tc);
       fabric_metadata.packet_color:=meter_havoc;
       fabric_metadata.dscp:=slice_tc;
       queues.apply(){
	\(qid (_ BitVec 5))  -> {
	}
	\ -> {
		standard_metadata.egress_spec:=(_ bv511 9)
	}
	\ -> {
	}}
    }
  };
   exit:=(_ bv0 1);
  {
     assume (= standard_metadata.egress_spec (_ bv511 9))
  } [] {
     assume (not(= standard_metadata.egress_spec (_ bv511 9)));
     standard_metadata.egress_port:=standard_metadata.egress_spec;
    {
       assume (not(= (_ bv1 1) fabric_metadata.is_controller_packet_out))
    } [] {
       assume (= (_ bv1 1) fabric_metadata.is_controller_packet_out);
       exit:=(_ bv1 1)
    };
    {
       assume (= (_ bv1 1) exit)
    } [] {
       assume (not(= (_ bv1 1) exit));
      {
         assume (not(= (_ bv510 9) standard_metadata.egress_port))
      } [] {
         assume (= (_ bv510 9) standard_metadata.egress_port);
         hdr.packet_in.isValid:=(_ bv1 1);
         hdr.packet_in.ingress_port:=standard_metadata.ingress_port;
         exit:=(_ bv1 1)
      }
    };
     exit:=(_ bv0 1);
    {
       assume (= (_ bv1 1) exit)
    } [] {
       assume (not(= (_ bv1 1) exit));
      {
         assume (not(= (_ bv0 1) fabric_metadata.is_controller_packet_out))
      } [] {
         assume (= (_ bv0 1) fabric_metadata.is_controller_packet_out);
        {
           assume (not(and
  (= (_ bv1 1) fabric_metadata.is_multicast)
  (= standard_metadata.egress_port standard_metadata.ingress_port)))
        } [] {
           assume (and
  (= (_ bv1 1) fabric_metadata.is_multicast)
  (= standard_metadata.egress_port standard_metadata.ingress_port));
           standard_metadata.egress_spec:=(_ bv511 9)
        };
        {
           assume (not(= (_ bv0 20) fabric_metadata.mpls_label));
           hdr.mpls.isValid:=(_ bv1 1);
           hdr.mpls.label:=egress_havoc_label;
           hdr.mpls.tc:=egress_havoc_tc;
           hdr.mpls.bos:=egress_havoc_bos;
           hdr.mpls.ttl:=egress_havoc_ttl;
           hdr.mpls.label:=fabric_metadata.mpls_label;
           hdr.mpls.tc:=(_ bv0 3);
           hdr.mpls.bos:=(_ bv1 1);
           hdr.mpls.ttl:=fabric_metadata.mpls_ttl;
           hdr.eth_type.value:=(_ bv34887 16)
        } [] {
           assume (= (_ bv0 20) fabric_metadata.mpls_label);
          {
             assume (not(= (_ bv1 1) hdr.mpls.isValid))
          } [] {
             assume (= (_ bv1 1) hdr.mpls.isValid);
             hdr.mpls.isValid:=(_ bv0 1);
             hdr.eth_type.value:=fabric_metadata.ip_eth_type
          }
        };
         egress_vlan.apply(){
	\ -> {
		hdr.vlan_tag.isValid:=(_ bv1 1)
		hdr.vlan_tag.cfi:=push_vlan_havoc_cfi
		hdr.vlan_tag.pri:=push_vlan_havoc_pri
		hdr.vlan_tag.eth_type:=push_vlan_havoc_eth_type
		hdr.vlan_tag.vlan_id:=push_vlan_havoc_vlan_id
		hdr.vlan_tag.cfi:=fabric_metadata.vlan_cfi
		hdr.vlan_tag.pri:=fabric_metadata.vlan_pri
		hdr.vlan_tag.eth_type:=(_ bv33024 16)
		hdr.vlan_tag.vlan_id:=fabric_metadata.vlan_id
	}
	\ -> {
		hdr.vlan_tag.isValid:=(_ bv0 1)
	}
	\ -> {
		standard_metadata.egress_spec:=(_ bv511 9)
	}};
        {
           assume (not(= (_ bv1 1) hdr.mpls.isValid));
          {
             assume (not(and
  (= (_ bv1 1) hdr.ipv4.isValid)
  (not(= (_ bv0 3) fabric_metadata.fwd_type))))
          } [] {
             assume (and
  (= (_ bv1 1) hdr.ipv4.isValid)
  (not(= (_ bv0 3) fabric_metadata.fwd_type)));
             hdr.ipv4.ttl:=(bvsub hdr.ipv4.ttl (_ bv1 8));
            {
               assume (not(= (_ bv0 8) hdr.ipv4.ttl))
            } [] {
               assume (= (_ bv0 8) hdr.ipv4.ttl);
               standard_metadata.egress_spec:=(_ bv511 9)
            }
          }
        } [] {
           assume (= (_ bv1 1) hdr.mpls.isValid);
           hdr.mpls.ttl:=(bvsub hdr.mpls.ttl (_ bv1 8));
          {
             assume (not(= (_ bv0 8) hdr.mpls.ttl))
          } [] {
             assume (= (_ bv0 8) hdr.mpls.ttl);
             standard_metadata.egress_spec:=(_ bv511 9)
          }
        };
         tmp_dscp:=fabric_metadata.dscp;
         rewriter_action_run:=(_ bv3 2);
         rewriter.apply(){
	\ -> {
		rewriter_action_run:=(_ bv0 2)
	}
	\ -> {
		rewriter_action_run:=(_ bv1 2)
		tmp_dscp:=(_ bv0 6)
	}
	\ -> {
		rewriter_action_run:=(_ bv2 2)
	}};
        {
           assume (not(= (_ bv0 2) rewriter_action_run));
          {
             assume (not(= (_ bv1 2) rewriter_action_run))
          } [] {
             assume (= (_ bv1 2) rewriter_action_run);
            {
               assume (not(= (_ bv1 1) hdr.ipv4.isValid))
            } [] {
               assume (= (_ bv1 1) hdr.ipv4.isValid);
               hdr.inner_ipv4.dscp:=tmp_dscp
            }
          }
        } [] {
           assume (= (_ bv0 2) rewriter_action_run);
          {
             assume (not(= (_ bv1 1) hdr.ipv4.isValid))
          } [] {
             assume (= (_ bv1 1) hdr.ipv4.isValid);
             hdr.inner_ipv4.dscp:=tmp_dscp
          }
        }
      }
    };
     exit:=(_ bv0 1)
  }
}
