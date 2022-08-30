default = True

vlan_decap__vlan_decap = 3 + int(default) #actions
process_rewrite__rewrite = 5 + int(default) #actions
process_egress_bd__egress_bd_map = 2 + int(default) #actions
process_mac_rewrite__l3_rewrite = 2 + int(default) #actions
process_mac_rewrite__smac_rewrite = 1 + int(default) #action
process_mtu__mtu = 3 + int(default) #actions
process_vlan_xlate__egress_vlan_xlate = 3 + int(default) #actions
process_egress_acl__egress_acl = 4 + int(default) #actions
egress__egress_port_mapping = 3 + int(default) #actions
egress__mirror = 3 + int(default) #actions
process_ingress_port_mapping__ingress_port_mapping = 1 + int(default) #action
process_ingress_port_mapping__ingress_port_properties = 1 + int(default) #action
validate_outer_ipv4_header__validate_outer_ipv43_packet = 1 + int(default) #action
process_validate_outer_headervalidate_outer_ethernet = 13 + int(default) #actions
process_global_params__switch_config_params = 1 + int(default) #action
process_port_vlan_mapping__port_vlan_mapping = 2 + int(default) #actions
process_spanning_tree__spanning_tree = 1 + int(default) #action
process_ip_sourceguard__ipsg = 1 + int(default) #action
process_ip_sourceguard__ipsg_permit_special = 1 + int(default) #action
process_ingress_fabric__fabric_ingress_dst_lkp = 2 + int(default) #actions
process_validate_packet__validate_packet = 7 + int(default) #actions
process_mac__dmac = 7 + int(default) #actions
process_mac__smac = 3 + int(default) #actions
process_mac_acl__mac_acl = 6 + int(default) #actions
process_ip_acl__ip_acl = 6 + int(default) #actions
process_qos__qos = 4 + int(default) #actions
process_ipv4_racl__ipv4_racl = 5 + int(default) #actions
process_ipv4_urpf__ipv4_urpf = 2 + int(default) #actions
process_ipv4_urpf__ipv4_urpf_lpm = 2 + int(default) #actions
process_ipv4_fib__ipv4_fib = 3 + int(default) #actions
process_ipv4_fib__ipv4_fib_lpm = 3 + int(default) #actions
process_urpf_bd__urpf_bd = 2 + int(default) #actions
process_hashes__compute_ipv4_hashes = 2 + int(default) #actions
process_hashes__compute_non_ip_hashes = 2 + int(default) #actions
process_hashes__compute_other_hashes = 2 + int(default) #actions
process_fwd_results__fwd_results = 6 + int(default) #actions
process_nexthop__ecmp_group = 3 + int(default) #actions
process_nexthop__nexthop = 3 + int(default) #actions
process_lag__lag_group = 2 + int(default) #actions
process_mac_learning__learn_notify = 2 + int(default) #actions
process_system_acl__drop_states_0 = 1 + int(default) #action
process_system_acl__system_acl = 7 + int(default) #actions
ingress__rmac = 2 + int(default) #actions


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
