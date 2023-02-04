(*test.FabricArpBroadcastMixedTest*)
open Runtime

(* 2023-02-04 18:15:48.789888;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\001" } } match { field_id: 2 exact { value: "\001" } } match { field_id: 3 ternary { value: "\000\n" mask: "\017\377" } } action { action { action_id: 24158268 params { param_id: 1 value: "\001" } } } priority: 10 } }; *)
(* 2023-02-04 18:15:48.790898;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\002" } } match { field_id: 2 exact { value: "\001" } } match { field_id: 3 ternary { value: "\000\n" mask: "\017\377" } } action { action { action_id: 24158268 params { param_id: 1 value: "\001" } } } priority: 10 } }; *)
(* 2023-02-04 18:15:48.791401;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\000" } } match { field_id: 2 exact { value: "\000" } } action { action { action_id: 24266015 params { param_id: 2 value: "\001" } params { param_id: 1 value: "\000\n" } } } priority: 10 } }; *)
(* 2023-02-04 18:15:48.791970;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\n" } } } priority: 10 } }; *)
(* 2023-02-04 18:15:48.792682;1;type: INSERT entity { table_entry { table_id: 44104738 match { field_id: 5 ternary { value: "\010\006" mask: "\377\377" } } action { action { action_id: 16912673 params { param_id: 1 value: "\000\000\001\377" } } } priority: 10 } }; *)
(* 2023-02-04 18:15:48.793419;1;type: INSERT entity { table_entry { table_id: 40619180 match { field_id: 1 exact { value: "\000\000\000\n" } } action { action { action_id: 21629581 params { param_id: 1 value: "\000\n" } } } } }; *)
(* 2023-02-04 18:15:48.793892;1;type: INSERT entity { packet_replication_engine_entry { multicast_group_entry { multicast_group_id: 10 replicas { egress_port: 1 } replicas { egress_port: 2 } replicas { } } } }; *)
(* 2023-02-04 18:15:48.794405;1;type: INSERT entity { packet_replication_engine_entry { clone_session_entry { session_id: 511 replicas { egress_port: 255 instance: 1 } } } }; *)
(* 2023-02-04 18:15:48.794973;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\001" } } action { action { action_id: 30307755 } } } }; *)
(* 2023-02-04 18:15:48.795409;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\002" } } action { action { action_id: 30307755 } } } }; *)
(* 2023-02-04 18:15:48.795808;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\000" } } action { action { action_id: 17183246 } } } }; *)
let test = [

  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.one } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.one } } ;
                          { field_id = 3;
                            match_key = Ternary { value = Bigint.of_int 10 ;
                                                  mask = Bigint.of_int 4095 } }];
               action = Action { action_id = 24158268;
                                 args = [ { arg_id = 1;
                                            value = Bigint.one } ] };
               priority = 10 };

TableEntry { table_id = 43310977;
             matches = [{ field_id = 1;
                          match_key = Exact { value = Bigint.of_int 2} } ;
                        { field_id = 2;
                          match_key = Exact { value = Bigint.of_int 1 } } ;
                        { field_id = 3;
                          match_key = Ternary { value = Bigint.of_int 10;
                                                mask = Bigint.of_int 4095 } }];
             action = Action { action_id = 24158268;
                               args = [ { arg_id = 1;
                                          value = Bigint.one } ] };
             priority = 10 };

TableEntry { table_id = 43310977;
             matches = [{ field_id = 1;
                          match_key = Exact { value = Bigint.zero } } ;
                        { field_id = 2;
                          match_key = Exact { value = Bigint.zero } }];
             action = Action { action_id = 24266015;
                               args = [ { arg_id = 2;
                                          value = Bigint.one };
                                        { arg_id = 1;
                                          value = Bigint.of_int 10 } ] };
             priority = 10 };

TableEntry { table_id = 43623757;
             matches = [{ field_id = 1;
                          match_key = Exact { value = Bigint.of_int 10 } }];
             action = Action { action_id = 21791748;
                               args = [ { arg_id = 1;
                                          value = Bigint.of_int 10 } ] };
             priority = 10 };

TableEntry { table_id = 44104738;
             matches = [{ field_id = 5;
                          match_key = Ternary { value = Bigint.of_int 2054;
                                                mask = Bigint.of_int 65535 } }];
             action = Action { action_id = 16912673;
                               args = [ { arg_id = 1;
                                          value = Bigint.of_int 511 } ] };
             priority = 10 };

  TableEntry { table_id = 40619180;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 10 } }];
               action = Action { action_id = 21629581;
                                 args = [ { arg_id = 1;
                                            value = Bigint.of_int 10 } ] };
               priority = -1;
             };

TableEntry { table_id = 49262446;
             matches = [{ field_id = 1;
                          match_key = Exact { value = Bigint.of_int 10 } } ;
                        { field_id = 2;
                          match_key = Exact { value = Bigint.of_int 1} }];
             action = Action { action_id = 30307755; args = [] };
             priority = -1;
           };

TableEntry { table_id = 49262446;
             matches = [{ field_id = 1;
                          match_key = Exact { value = Bigint.of_int 10 } } ;
                        { field_id = 2;
                          match_key = Exact { value = Bigint.of_int 2 } }];
             action = Action { action_id = 30307755; args = [] };
             priority = -1;
           };

TableEntry { table_id = 49262446;
             matches = [{ field_id = 1;
                          match_key = Exact { value = Bigint.of_int 10 } } ;
                        { field_id = 2;
                          match_key = Exact { value = Bigint.of_int 0 } }];
             action = Action { action_id = 17183246; args = [] };
             priority = -1
           };

];
