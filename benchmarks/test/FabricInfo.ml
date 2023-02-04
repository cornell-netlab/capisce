open Pbench
open Info

let info : t = {
  tables = [
    { name = "ingress_port_vlan";
      id = 43310977;
      match_fields = [
        {
          id = 1;
          name = "ig_port";
          bitwidth = 9;
          match_type = EXACT;
        };
        {
          id = 2;
          name = "vlan_is_valid";
          bitwidth = 1;
          match_type = EXACT;
        };
        {
          id = 3;
          name = "vlan_id";
          bitwidth = 12;
          match_type = TERNARY;
        };
      ];
      action_refs = [
        { id = 17164167 };
        { id = 24158268 };
        { id = 24266015 };
      ]
    };
    {
      name = "fwd_classifier";
      id = 49718154;
      match_fields = [
        {
          id = 1;
          name = "ig_port";
          bitwidth = 9;
          match_type = TERNARY;
        };
        {
          id = 2;
          name = "eth_dst";
          bitwidth = 48;
          match_type = TERNARY;
        };
        {
          id = 3;
          name = "eth_type";
          bitwidth = 16;
          match_type = TERNARY;
        };
        {
          id = 4;
          name = "ip_eth_type";
          bitwidth = 16;
          match_type = EXACT;
        }
      ];
      action_refs = [
        { id = 25032921 }
      ]
    };
    {
      name = "bridging";
      id = 43623757;
      match_fields = [
        {
          id = 1;
          name = "vlan_id";
          bitwidth = 12;
          match_type = EXACT;
        };
        {
          id = 2;
          name = "eth_dst";
          bitwidth = 48;
          match_type = TERNARY;
        }
      ];
      action_refs = [
        { id = 21791748 };
        { id = 28485346 }
      ]
    };
    {
      name = "mpls";
      id = 37768578;
      match_fields = [
        {
          id = 1;
          name = "mpls_label";
          bitwidth = 20;
          match_type = EXACT;
        }
      ];
      action_refs = [
        { id = 30066030 };
        { id = 28485346 }
      ]
    };
    {
      name = "routing_v4";
      id = 41754650;
      match_fields = [
        {
          id = 1;
          name = "ipv4_dst";
          bitwidth = 32;
          match_type = LPM;
        }
      ];
      action_refs = [
        { id = 19792090 };
        { id = 29124955 }
      ]
    };
    {
      name = "next_mpls";
      id = 36626242;
      match_fields = [
        {
          id = 1;
          name = "next_id";
          bitwidth = 32;
          match_type = EXACT;
        }
      ];
      action_refs = [
        { id = 22765924 };
        { id = 28485346 }
      ]
    };
    {
      name = "next_vlan";
      id = 48011802;
      match_fields = [
        {
          id = 1;
          name = "next_id";
          bitwidth = 32;
          match_type = EXACT;
        }
      ];
      action_refs = [
        { id = 33475378 };
        { id = 28485346 };
      ]
    };
    {
      name = "acl";
      id = 44104738;
      match_fields = [
        {
          id = 1;
          name = "ig_port";
          bitwidth = 9;
          match_type = TERNARY;
        };
        {
          id = 2;
          name = "eth_dst";
          bitwidth = 48;
          match_type = TERNARY;
        };
        {
          id = 3;
          name = "eth_src";
          bitwidth = 48;
          match_type = TERNARY;
        };
        {
          id = 4;
          name = "vlan_id";
          bitwidth = 12;
          match_type = TERNARY;
        };
        {
          id = 5;
          name = "eth_type";
          bitwidth = 16;
          match_type = TERNARY;
        };
        {
          id = 6;
          name = "ipv4_src";
          bitwidth = 32;
          match_type = TERNARY;
        };
        {
          id = 7;
          name = "ipv4_dst";
          bitwidth = 32;
          match_type = TERNARY;
        };
        {
          id = 8;
          name = "ip_proto";
          bitwidth = 8;
          match_type = TERNARY;
        };
        {
          id = 9;
          name = "icmp_type";
          bitwidth = 8;
          match_type = TERNARY;
        };
        {
          id = 10;
          name = "icmp_code";
          bitwidth = 8;
          match_type = TERNARY;
        };
        {
          id = 11;
          name = "l4_sport";
          bitwidth = 16;
          match_type = TERNARY;
        };
        {
          id = 12;
          name = "l4_dport";
          bitwidth = 16;
          match_type = TERNARY;
        };
        {
          id = 13;
          name = "port_type";
          bitwidth = 2;
          match_type = TERNARY;
        }
      ];
      action_refs = [
        { id = 23623126 };
        { id = 23579892 };
        { id = 16912673 };
        { id = 23570973 };
        { id = 29607214 }
      ]
    };
    {
      name = "xconnect";
      id = 48735793;
      match_fields = [
        {
          id = 1;
          name = "ig_port";
          bitwidth = 9;
          match_type = EXACT;
        };
        {
          id = 2;
          name = "next_id";
          bitwidth = 32;
          match_type = EXACT;
        };
      ];
      action_refs = [
        { id = 24640974 };
        { id = 30599612 };
        { id = 28485346 }
      ]
    };
    {
      name = "hashed";
      id = 47960972;
      match_fields = [
        {
          id = 1;
          name = "next_id";
          bitwidth = 32;
          match_type = EXACT;
        };
        (* { *)
        (*   id = 2; *)
        (*   name = "src_addr"; *)
        (*   bitwidth = 32; *)
        (*   match_type = EXACT; *)
        (* }; *)
        (* { *)
        (*   id = 3; *)
        (*   name = "dst_addr"; *)
        (*   bitwidth = 32; *)
        (*   match_type = EXACT; *)
        (* }; *)
        (* { *)
        (*   id = 4; *)
        (*   name = "ip_proto"; *)
        (*   bitwidth = 8; *)
        (*   match_type = EXACT; *)
        (* }; *)
        (* { *)
        (*   id = 5; *)
        (*   name = "l4_sport"; *)
        (*   bitwidth = 16; *)
        (*   match_type = EXACT; *)
        (* }; *)
        (* { *)
        (*   id = 6; *)
        (*   name = "l4_dport"; *)
        (*   bitwidth = 16; *)
        (*   match_type = EXACT; *)
        (* } *)
      ];
      action_refs = [
        { id = 27301117 };
        { id = 20985706 };
        { id = 28485346 };
      ]
    };
    {
      name = "multicast";
      id = 40619180;
      match_fields = [
        {
          id = 1;
          name = "next_id";
          bitwidth = 32;
          match_type = EXACT;
        }
      ];
      action_refs = [
        { id = 21629581 };
        { id = 28485346 }
      ]
    };
    {
      name = "classifier";
      id = 34606298;
      match_fields = [
        {
          id = 1;
          name = "ig_port";
          bitwidth = 9;
          match_type = TERNARY;
        };
        {
          id = 2;
          name = "ipv4_src";
          bitwidth = 32;
          match_type = TERNARY;
        };
        {
          id = 3;
          name = "ipv4_dst";
          bitwidth = 32;
          match_type = TERNARY;
        };
        {
          id = 4;
          name = "ip_proto";
          bitwidth = 8;
          match_type = TERNARY;
        };
        {
          id = 5;
          name = "l4_sport";
          bitwidth = 16;
          match_type = TERNARY;
        };
        {
          id = 6;
          name = "l4_dport";
          bitwidth = 16;
          match_type = TERNARY;
        };
      ];
      action_refs = [
        { id = 23786376 };
        { id = 25983516 }
      ]
    };
    {
      name = "queues";
      id = 36435258;
      match_fields = [
        {
          id = 1;
          name = "slice_id";
          bitwidth = 4;
          match_type = EXACT;
        };
        {
          id = 2;
          name = "tc";
          bitwidth = 2;
          match_type = EXACT;
        };
        {
          id = 4;
          name = "color";
          bitwidth = 2;
          match_type = TERNARY;
        }
      ];
      action_refs = [
        { id = 32116918 };
        { id = 28214351 }
      ]
    };
    {
      name = "egress_vlan";
      id = 49262446;
      match_fields = [
        {
          id = 1;
          name = "vlan_id";
          bitwidth = 12;
          match_type = EXACT;
        };
        {
          id = 2;
          name = "eg_port";
          bitwidth = 9;
          match_type = EXACT;
        };
      ];
      action_refs = [
        { id = 30307755 };
        { id = 17183246 };
        { id = 30812542 }
      ]
    };
    {
      name = "rewriter";
      id = 49970092;
      match_fields = [
        {
          id = 1;
          name = "eg_port";
          bitwidth = 9;
          match_type = EXACT;
        };
      ];
      action_refs = [
        { id = 27951287 };
        { id = 24120545 };
        { id = 28485346 }
      ]
    }
  ];
  actions = [
    {
      name = "nop";
      id = 28485346;
      params = [];
    };
    {
      name = "deny";
      id = 17164167;
      params = [];
    };
    {
      name = "permit";
      id = 24158268;
      params = [
        {
          id = 1;
          name = "port_type";
          bitwidth = 2;
        }
      ]
    };
    {
      name = "permit_with_internal_vlan";
      id = 24266015;
      params = [
        {
          id = 1;
          name = "vlan_id";
          bitwidth = 12;
        };
        {
          id = 2;
          name = "port_type";
          bitwidth = 2;
        };
      ]
    };
    {
      name = "set_forwarding_type";
      id = 25032921;
      params = [
        {
          id = 1;
          name = "fwd_type";
          bitwidth = 3;
        }
      ]
    };
    {
      name = "set_next_id_bridging";
      id = 21791748;
      params = [
        {
          id = 1;
          name = "next_id";
          bitwidth = 32;
        }
      ]
    };
    {
      name = "pop_mpls_and_next";
      id = 30066030;
      params = [
        {
          id = 1;
          name = "next_id";
          bitwidth = 32;
        }
      ]
    };
    {
      name = "set_next_id_routing_v4";
      id = 19792090;
      params = [
        {
          id = 1;
          name = "next_id";
          bitwidth = 32;
        }
      ]
    };
    {
      name = "nop_routing_v4";
      id = 29124955;
      params = []
    };
    {
      name = "set_mpls_label";
      id = 22765924;
      params = [
        {
          id = 1;
          name = "label";
          bitwidth = 20
        }
      ]
    };
    {
      name = "set_vlan";
      id = 33475378;
      params = [
        {
          id = 1;
          name = "vlan_id";
          bitwidth = 12;
        };
      ]
    };
    {
      name = "set_next_id_acl";
      id = 23623126;
      params = [
        {
          id = 1;
          name = "next_id";
          bitwidth = 32;
        }
      ]
    };
    {
      name = "punt_to_cpu";
      id = 23579892;
      params = []
    };
    {
      name = "set_clone_session_id";
      id = 16912673;
      params = [
        {
          id = 1;
          name = "clone_id";
          bitwidth = 32;
        }
      ]
    };
    {
      name = "drop";
      id = 23560973;
      params = []
    };
    {
      name = "nop_acl";
      id = 29607214;
      params = []
    };
    {
      name = "output_xconnect";
      id = 24640974;
      params = [
        {
          id = 1;
          name = "port_num";
          bitwidth = 9;
        }
      ]
    };
    {
      name = "set_next_id_xconnect";
      id = 30599612;
      params = [
        {
          id = 1;
          name = "next_id";
          bitwidth = 32;
        }
      ]
    };
    {
      name = "output_hashed";
      id = 27301117;
      params = [
        {
          id = 1;
          name = "port_num";
          bitwidth = 9;
        }
      ]
    };
    {
      name = "routing_hashed";
      id = 20985706;
      params = [
        {
          id = 1;
          name = "port_num";
          bitwidth = 9;
        };
        {
          id = 2;
          name = "smac";
          bitwidth = 48;
        };
        {
          id = 3;
          name = "dmac";
          bitwidth = 48;
        }
      ]
    };
    {
      name = "set_mcast_group_id";
      id = 21629581;
      params = [
        {
          id = 1;
          name = "group_id";
          bitwidth = 16;
        }
      ]
    };
    {
      name = "set_slice_id_tc";
      id = 23786376;
      params = [
        {
          id = 1;
          name = "slice_id";
          bitwidth = 4;
        };
        {
          id = 2;
          name = "tc";
          bitwidth = 2;
        }
      ]
    };
    {
      name = "trust_dscp";
      id = 25983516;
      params = []
    };
    {
      name = "set_queue";
      id = 32116918;
      params = [
        { id = 1;
          name = "qid";
          bitwidth = 5
        }
      ]
    };
    {
      name = "meter_drop";
      id = 28214351;
      params = []
    };
    {
      name = "NoAction";
      id = 21257015;
      params = []
    };
    {
      name = "int_source_dscp";
      id = 20062657;
      params = [
        {
          id = 1;
          name = "max_hop";
          bitwidth = 8;
        };
        {
          id = 2;
          name = "ins_cnt";
          bitwidth = 5;
        };
        {
          id = 3;
          name = "ins_mask003";
          bitwidth = 4;
        };
        {
          id = 4;
          name = "ins_mask0407";
          bitwidth = 4;
        }
      ]
    };
    {
      name = "init_metadata";
      id = 29232623;
      params = [
        {
          id = 1;
          name = "switch_id";
          bitwidth = 32;
        }
      ]
    };
    {
      name = "push_vlan";
      id = 30307755;
      params = []
    };
    {
      name = "pop_vlan";
      id = 17183246;
      params = [];
    };
    {
      name = "egress_next.drop";
      id = 30812642;
      params = []
    };
    {
      name = "rewrite";
      id = 27951287;
      params = []
    };
    {
      name = "clear";
      id = 24120545;
      params = []
    }
  ];
  action_profiles = [
    {
      id = 291115404;
      name = "hashed_selector";
      table_ids = [47960972];
    }
  ]
}
