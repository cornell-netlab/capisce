default = True
count_tables = False

def count(n):
    if count_tables:
        return 1
    else:
        return n + int(default)

vlan_decap__vlan_decap = count(3)
process_rewrite__rewrite = count(5)
process_egress_bd__egress_bd_map = count(2)
process_mac_rewrite__l3_rewrite = count(2)
process_mac_rewrite__smac_rewrite = count(1)
process_mtu__mtu = count(3)
process_vlan_xlate__egress_vlan_xlate = count(3)
process_egress_acl__egress_acl = count(4)
egress__egress_port_mapping = count(3)
egress__mirror = count(3)
process_ingress_port_mapping__ingress_port_mapping = count(1)
process_ingress_port_mapping__ingress_port_properties = count(1)
validate_outer_ipv4_header__validate_outer_ipv43_packet = count(1)
process_validate_outer_headervalidate_outer_ethernet = count(13)
process_global_params__switch_config_params = count(1)
process_port_vlan_mapping__port_vlan_mapping = count(2)
process_spanning_tree__spanning_tree = count(1)
process_ip_sourceguard__ipsg = count(1)
process_ip_sourceguard__ipsg_permit_special = count(1)
process_ingress_fabric__fabric_ingress_dst_lkp = count(2)
process_validate_packet__validate_packet = count(7)
process_mac__dmac = count(7)
process_mac__smac = count(3)
process_mac_acl__mac_acl = count(6)
process_ip_acl__ip_acl = count(6)
process_qos__qos = count(4)
process_ipv4_racl__ipv4_racl = count(5)
process_ipv4_urpf__ipv4_urpf = count(2)
process_ipv4_urpf__ipv4_urpf_lpm = count(2)
process_ipv4_fib__ipv4_fib = count(3)
process_ipv4_fib__ipv4_fib_lpm = count(3)
process_urpf_bd__urpf_bd = count(2)
process_hashes__compute_ipv4_hashes = count(2)
process_hashes__compute_non_ip_hashes = count(2)
process_hashes__compute_other_hashes = count(2)
process_fwd_results__fwd_results = count(6)
process_nexthop__ecmp_group = count(3)
process_nexthop__nexthop = count(3)
process_lag__lag_group = count(2)
process_mac_learning__learn_notify = count(2)
process_system_acl__drop_states_0 = count(1)
process_system_acl__system_acl = count(7)
ingress__rmac = count(2)


process_ingress_port_mapping =\
  process_ingress_port_mapping__ingress_port_mapping\
  * process_ingress_port_mapping__ingress_port_properties\

process_global_params = process_global_params__switch_config_params

process_port_vlan_mapping = process_port_vlan_mapping__port_vlan_mapping

process_spanning_tree = process_spanning_tree__spanning_tree + 1

process_ip_sourceguard = 1 + (process_ip_sourceguard__ipsg - 1) + process_ip_sourceguard__ipsg_permit_special

process_ingress_fabric = 1 + process_ingress_fabric__fabric_ingress_dst_lkp

process_tunnel = process_ingress_fabric

process_validate_packet = 1 + process_validate_packet__validate_packet

process_mac = (1 + process_mac__smac) + (1 + process_mac__dmac)

process_mac_acl = 1 + process_mac_acl__mac_acl

process_ip_acl = 1 + 1 + process_ip_acl__ip_acl

process_qos = process_qos__qos

process_ipv4_racl = process_ipv4_racl__ipv4_racl

process_ipv4_urpf = 1 + (process_ipv4_urpf__ipv4_urpf - 1) + process_ipv4_urpf__ipv4_urpf_lpm

process_ipv4_fib = (process_ipv4_fib__ipv4_fib - 1) + process_ipv4_fib__ipv4_fib_lpm

process_urpf_bd = 1 + process_urpf_bd__urpf_bd

process_hashes = (process_hashes__compute_ipv4_hashes + process_hashes__compute_non_ip_hashes) * process_hashes__compute_other_hashes

process_fwd_results = 1 + process_fwd_results__fwd_results

process_nexthop = process_nexthop__ecmp_group + process_nexthop__nexthop

process_lag = process_lag__lag_group

process_mac_learning = 1 + process_mac_learning__learn_notify

process_system_acl =  (1 + process_system_acl__system_acl) * (1 + process_system_acl__drop_states_0)

ingress =\
  process_ingress_port_mapping\
  * process_global_params\
  * process_port_vlan_mapping\
  * process_spanning_tree\
  * process_ip_sourceguard\
  * process_tunnel\
  * ((process_validate_packet\
      * process_mac\
      * (process_mac_acl + process_ip_acl)\
      * process_qos\
      * ingress__rmac\
      * (1 + ((process_ipv4_racl * process_ipv4_urpf * process_ipv4_fib) + 2) * process_urpf_bd))
     + 1)\
  * process_hashes\
  * (1 + (process_fwd_results * process_nexthop * (1 + process_lag) * process_mac_learning))\
  * (1 + process_system_acl)\

process_vlan_decap = vlan_decap__vlan_decap
process_rewrite = 1 + process_rewrite__rewrite
process_egress_bd = process_egress_bd__egress_bd_map
process_mac_rewrite = 1 + (process_mac_rewrite__l3_rewrite * process_mac_rewrite__smac_rewrite)
process_mtu = process_mtu__mtu
process_vlan_xlate = process_vlan_xlate__egress_vlan_xlate
process_egress_acl = 1 + process_egress_acl__egress_acl


egress =\
  (1 + ((1 + egress__mirror)\
       * (egress__egress_port_mapping - 1 + ((1 + process_vlan_decap)\
                                             * process_rewrite\
                                             * process_egress_bd\
                                             * process_mac_rewrite\
                                             * process_mtu))))\
  * (1 + process_vlan_xlate)\
  * process_egress_acl

total = ingress * (1 + egress)
print("Total_paths:", total)
