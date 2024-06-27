open Runtime

(* 2023-01-27 17:48:54.259526;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\000" } } match { field_id: 2 exact { value: "\000" } } action { action { action_id: 24266015 params { param_id: 2 value: "\001" } params { param_id: 1 value: "\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:54.260336;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\000" } } action { action { action_id: 17183246 } } } }; *)
(* 2023-01-27 17:48:54.260816;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\001" } } match { field_id: 2 exact { value: "\001" } } match { field_id: 3 ternary { value: "\000\n" mask: "\017\377" } } action { action { action_id: 24158268 params { param_id: 1 value: "\001" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:54.261335;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\001" } } action { action { action_id: 30307755 } } } }; *)
(* 2023-01-27 17:48:54.261847;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\006\007\010\t\n" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:54.262316;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\001\002\003\004\005" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\024" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:54.262761;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 1 action { action_id: 27301117 params { param_id: 1 value: "\000\000" } } } }; *)
(* 2023-01-27 17:48:54.263181;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\n" } } action { action_profile_member_id: 1 } } }; *)
(* 2023-01-27 17:48:54.263624;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 2 action { action_id: 27301117 params { param_id: 1 value: "\000\001" } } } }; *)
(* 2023-01-27 17:48:54.264011;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\024" } } action { action_profile_member_id: 2 } } }; *)
let test_0 = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } };
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [{ arg_id = 2; value = Bigint.of_int 1 };
                                         { arg_id = 1; value = Bigint.of_int 10}] };
               priority = 10;
             };
  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10} };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  0} }];
               action = Action { action_id = 17183246; args = [] };
               priority = -1; (*UNKNOWN*)
             };
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 3; match_key = Ternary { value = Bigint.of_int 10; mask = Bigint.of_int 4095 } }];
               action = Action { action_id = 24158268;
                                 args = [{ arg_id = 1; value = Bigint.of_int 1 }] } ;
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  1 } }];
               action = Action { action_id = 30307755; args = [] };
               priority = -1 (* unknown *)
             };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "25887770890";} (*"\000\006\007\010\t\n";*)
                         ];
               action = Action { action_id = 21791748;
                                 args = [{ arg_id = 1; value = Bigint.of_int 10; }]};
               priority = 10 };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "4328719365" } ];
               action = Action { action_id = 21791748; args = [ { arg_id = 1; value = Bigint.of_int 20 } ] };
               priority = 10 };
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 1;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 0 }]};
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } }];
               action = Profile {action_profile_member_id = 1 };
               priority = -1 (*unknown*)};
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 2;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 1} ] };
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 20 }}];
               action = Profile {action_profile_member_id = 2 };
               priority = -1;
             };
]



(* 2023-01-27 17:48:54.384688;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\000" } } match { field_id: 2 exact { value: "\000" } } action { action { action_id: 24266015 params { param_id: 2 value: "\001" } params { param_id: 1 value: "\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:54.386799;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\000" } } action { action { action_id: 17183246 } } } }; *)
(* 2023-01-27 17:48:54.388912;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\001" } } match { field_id: 2 exact { value: "\001" } } match { field_id: 3 ternary { value: "\000\n" mask: "\017\377" } } action { action { action_id: 24158268 params { param_id: 1 value: "\001" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:54.391062;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\001" } } action { action { action_id: 30307755 } } } }; *)
(* 2023-01-27 17:48:54.393149;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\006\007\010\t\n" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:54.395384;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\001\002\003\004\005" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\024" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:54.397425;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 3 action { action_id: 27301117 params { param_id: 1 value: "\000\000" } } } }; *)
(* 2023-01-27 17:48:54.399139;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\n" } } action { action_profile_member_id: 3 } } }; *)
(* 2023-01-27 17:48:54.401013;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 4 action { action_id: 27301117 params { param_id: 1 value: "\000\001" } } } }; *)
(* 2023-01-27 17:48:54.402721;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\024" } } action { action_profile_member_id: 4 } } }; *)
let test_1 = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } };
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [{ arg_id = 2; value = Bigint.of_int 1 };
                                         { arg_id = 1; value = Bigint.of_int 10}] };
               priority = 10;
             };
  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10} };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  0} }];
               action = Action { action_id = 17183246; args = [] };
               priority = -1; (*UNKNOWN*)
             };
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 3; match_key = Ternary { value = Bigint.of_int 10; mask = Bigint.of_int 4095 } }];
               action = Action { action_id = 24158268;
                                 args = [{ arg_id = 1; value = Bigint.of_int 1 }] } ;
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  1 } }];
               action = Action { action_id = 30307755; args = [] };
               priority = -1 (* unknown *)
             };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "25887770890";} (*"\000\006\007\010\t\n";*)
                         ];
               action = Action { action_id = 21791748;
                                 args = [{ arg_id = 1; value = Bigint.of_int 10; }]};
               priority = 10 };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "4328719365" } ];
               action = Action { action_id = 21791748; args = [ { arg_id = 1; value = Bigint.of_int 20 } ] };
               priority = 10 };
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 3;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 0 }]};
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } }];
               action = Profile {action_profile_member_id = 3 };
               priority = -1 (*unknown*)};
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 4;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 1} ] };
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 20 }}];
               action = Profile {action_profile_member_id = 4 };
               priority = -1;
             };
]

(* 2023-01-27 17:48:54.552546;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\000" } } match { field_id: 2 exact { value: "\000" } } action { action { action_id: 24266015 params { param_id: 2 value: "\001" } params { param_id: 1 value: "\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:54.554620;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\000" } } action { action { action_id: 17183246 } } } }; *)
(* 2023-01-27 17:48:54.557046;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\001" } } match { field_id: 2 exact { value: "\001" } } match { field_id: 3 ternary { value: "\000\n" mask: "\017\377" } } action { action { action_id: 24158268 params { param_id: 1 value: "\001" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:54.559412;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\001" } } action { action { action_id: 30307755 } } } }; *)
(* 2023-01-27 17:48:54.561619;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\006\007\010\t\n" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:54.563855;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\001\002\003\004\005" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\024" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:54.565006;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 5 action { action_id: 27301117 params { param_id: 1 value: "\000\000" } } } }; *)
(* 2023-01-27 17:48:54.565349;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\n" } } action { action_profile_member_id: 5 } } }; *)
(* 2023-01-27 17:48:54.565765;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 6 action { action_id: 27301117 params { param_id: 1 value: "\000\001" } } } }; *)
(* 2023-01-27 17:48:54.566139;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\024" } } action { action_profile_member_id: 6 } } }; *)
let test_2 = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } };
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [{ arg_id = 2; value = Bigint.of_int 1 };
                                         { arg_id = 1; value = Bigint.of_int 10}] };
               priority = 10;
             };
  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10} };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  0} }];
               action = Action { action_id = 17183246; args = [] };
               priority = -1; (*UNKNOWN*)
             };
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 3; match_key = Ternary { value = Bigint.of_int 10; mask = Bigint.of_int 4095 } }];
               action = Action { action_id = 24158268;
                                 args = [{ arg_id = 1; value = Bigint.of_int 1 }] } ;
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  1 } }];
               action = Action { action_id = 30307755; args = [] };
               priority = -1 (* unknown *)
             };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "25887770890";} (*"\000\006\007\010\t\n";*)
                         ];
               action = Action { action_id = 21791748;
                                 args = [{ arg_id = 1; value = Bigint.of_int 10; }]};
               priority = 10 };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "4328719365" } ];
               action = Action { action_id = 21791748; args = [ { arg_id = 1; value = Bigint.of_int 20 } ] };
               priority = 10 };
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 5;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 0 }]};
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } }];
               action = Profile {action_profile_member_id = 5 };
               priority = -1 (*unknown*)};
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 6;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 1} ] };
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 20 }}];
               action = Profile {action_profile_member_id = 6 };
               priority = -1;
             };
]



(* 2023-01-27 17:48:54.686047;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\000" } } match { field_id: 2 exact { value: "\001" } } match { field_id: 3 ternary { value: "\000\n" mask: "\017\377" } } action { action { action_id: 24158268 params { param_id: 1 value: "\001" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:54.688261;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\000" } } action { action { action_id: 30307755 } } } }; *)
(* 2023-01-27 17:48:54.690443;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\001" } } match { field_id: 2 exact { value: "\001" } } match { field_id: 3 ternary { value: "\000\n" mask: "\017\377" } } action { action { action_id: 24158268 params { param_id: 1 value: "\001" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:54.692587;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\001" } } action { action { action_id: 30307755 } } } }; *)
(* 2023-01-27 17:48:54.694836;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\006\007\010\t\n" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:54.697083;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\001\002\003\004\005" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\024" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:54.699094;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 7 action { action_id: 27301117 params { param_id: 1 value: "\000\000" } } } }; *)
(* 2023-01-27 17:48:54.700740;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\n" } } action { action_profile_member_id: 7 } } }; *)
(* 2023-01-27 17:48:54.702610;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 8 action { action_id: 27301117 params { param_id: 1 value: "\000\001" } } } }; *)
(* 2023-01-27 17:48:54.704296;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\024" } } action { action_profile_member_id: 8 } } }; *)
let test_3 = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } };
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [{ arg_id = 2; value = Bigint.of_int 1 };
                                         { arg_id = 1; value = Bigint.of_int 10}] };
               priority = 10;
             };
  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10} };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  0} }];
               action = Action { action_id = 17183246; args = [] };
               priority = -1; (*UNKNOWN*)
             };
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 3; match_key = Ternary { value = Bigint.of_int 10; mask = Bigint.of_int 4095 } }];
               action = Action { action_id = 24158268;
                                 args = [{ arg_id = 1; value = Bigint.of_int 1 }] } ;
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  1 } }];
               action = Action { action_id = 30307755; args = [] };
               priority = -1 (* unknown *)
             };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "25887770890";} (*"\000\006\007\010\t\n";*)
                         ];
               action = Action { action_id = 21791748;
                                 args = [{ arg_id = 1; value = Bigint.of_int 10; }]};
               priority = 10 };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "4328719365" } ];
               action = Action { action_id = 21791748; args = [ { arg_id = 1; value = Bigint.of_int 20 } ] };
               priority = 10 };
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 7;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 0 }]};
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } }];
               action = Profile {action_profile_member_id = 7 };
               priority = -1 (*unknown*)};
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 8;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 1} ] };
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 20 }}];
               action = Profile {action_profile_member_id = 8 };
               priority = -1;
             };
]



(* 2023-01-27 17:48:54.857540;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\000" } } match { field_id: 2 exact { value: "\001" } } match { field_id: 3 ternary { value: "\000\n" mask: "\017\377" } } action { action { action_id: 24158268 params { param_id: 1 value: "\001" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:54.859704;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\000" } } action { action { action_id: 30307755 } } } }; *)
(* 2023-01-27 17:48:54.861934;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\001" } } match { field_id: 2 exact { value: "\001" } } match { field_id: 3 ternary { value: "\000\n" mask: "\017\377" } } action { action { action_id: 24158268 params { param_id: 1 value: "\001" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:54.864161;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\001" } } action { action { action_id: 30307755 } } } }; *)
(* 2023-01-27 17:48:54.866290;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\006\007\010\t\n" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:54.868636;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\001\002\003\004\005" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\024" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:54.870605;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 9 action { action_id: 27301117 params { param_id: 1 value: "\000\000" } } } }; *)
(* 2023-01-27 17:48:54.872376;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\n" } } action { action_profile_member_id: 9 } } }; *)
(* 2023-01-27 17:48:54.874222;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 10 action { action_id: 27301117 params { param_id: 1 value: "\000\001" } } } }; *)
(* 2023-01-27 17:48:54.876079;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\024" } } action { action_profile_member_id: 10 } } }; *)
let test_4 = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } };
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [{ arg_id = 2; value = Bigint.of_int 1 };
                                         { arg_id = 1; value = Bigint.of_int 10}] };
               priority = 10;
             };
  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10} };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  0} }];
               action = Action { action_id = 17183246; args = [] };
               priority = -1; (*UNKNOWN*)
             };
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 3; match_key = Ternary { value = Bigint.of_int 10; mask = Bigint.of_int 4095 } }];
               action = Action { action_id = 24158268;
                                 args = [{ arg_id = 1; value = Bigint.of_int 1 }] } ;
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  1 } }];
               action = Action { action_id = 30307755; args = [] };
               priority = -1 (* unknown *)
             };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "25887770890";} (*"\000\006\007\010\t\n";*)
                         ];
               action = Action { action_id = 21791748;
                                 args = [{ arg_id = 1; value = Bigint.of_int 10; }]};
               priority = 10 };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "4328719365" } ];
               action = Action { action_id = 21791748; args = [ { arg_id = 1; value = Bigint.of_int 20 } ] };
               priority = 10 };
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 9;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 0 }]};
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } }];
               action = Profile {action_profile_member_id = 9 };
               priority = -1 (*unknown*)};
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 10;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 1} ] };
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 20 }}];
               action = Profile {action_profile_member_id = 10 };
               priority = -1;
             };
]

(* 2023-01-27 17:48:55.026988;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\000" } } match { field_id: 2 exact { value: "\001" } } match { field_id: 3 ternary { value: "\000\n" mask: "\017\377" } } action { action { action_id: 24158268 params { param_id: 1 value: "\001" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.029129;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\000" } } action { action { action_id: 30307755 } } } }; *)
(* 2023-01-27 17:48:55.031329;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\001" } } match { field_id: 2 exact { value: "\001" } } match { field_id: 3 ternary { value: "\000\n" mask: "\017\377" } } action { action { action_id: 24158268 params { param_id: 1 value: "\001" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.033422;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\001" } } action { action { action_id: 30307755 } } } }; *)
(* 2023-01-27 17:48:55.041279;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\006\007\010\t\n" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.045012;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\001\002\003\004\005" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\024" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.047934;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 11 action { action_id: 27301117 params { param_id: 1 value: "\000\000" } } } }; *)
(* 2023-01-27 17:48:55.049188;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\n" } } action { action_profile_member_id: 11 } } }; *)
(* 2023-01-27 17:48:55.050091;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 12 action { action_id: 27301117 params { param_id: 1 value: "\000\001" } } } }; *)
(* 2023-01-27 17:48:55.050687;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\024" } } action { action_profile_member_id: 12 } } }; *)
let test_5 = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } };
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [{ arg_id = 2; value = Bigint.of_int 1 };
                                         { arg_id = 1; value = Bigint.of_int 10}] };
               priority = 10;
             };
  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10} };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  0} }];
               action = Action { action_id = 17183246; args = [] };
               priority = -1; (*UNKNOWN*)
             };
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 3; match_key = Ternary { value = Bigint.of_int 10; mask = Bigint.of_int 4095 } }];
               action = Action { action_id = 24158268;
                                 args = [{ arg_id = 1; value = Bigint.of_int 1 }] } ;
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  1 } }];
               action = Action { action_id = 30307755; args = [] };
               priority = -1 (* unknown *)
             };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "25887770890";} (*"\000\006\007\010\t\n";*)
                         ];
               action = Action { action_id = 21791748;
                                 args = [{ arg_id = 1; value = Bigint.of_int 10; }]};
               priority = 10 };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "4328719365" } ];
               action = Action { action_id = 21791748; args = [ { arg_id = 1; value = Bigint.of_int 20 } ] };
               priority = 10 };
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 11;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 0 }]};
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } }];
               action = Profile {action_profile_member_id = 11 };
               priority = -1 (*unknown*)};
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 12;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 1} ] };
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 20 }}];
               action = Profile {action_profile_member_id = 12 };
               priority = -1;
             };
]

(* 2023-01-27 17:48:55.173677;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\000" } } match { field_id: 2 exact { value: "\000" } } action { action { action_id: 24266015 params { param_id: 2 value: "\001" } params { param_id: 1 value: "\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.175760;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\000" } } action { action { action_id: 17183246 } } } }; *)
(* 2023-01-27 17:48:55.177730;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\001" } } match { field_id: 2 exact { value: "\000" } } action { action { action_id: 24266015 params { param_id: 2 value: "\001" } params { param_id: 1 value: "\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.179855;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\001" } } action { action { action_id: 17183246 } } } }; *)
(* 2023-01-27 17:48:55.182181;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\006\007\010\t\n" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.184426;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\001\002\003\004\005" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\024" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.186397;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 13 action { action_id: 27301117 params { param_id: 1 value: "\000\000" } } } }; *)
(* 2023-01-27 17:48:55.188207;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\n" } } action { action_profile_member_id: 13 } } }; *)
(* 2023-01-27 17:48:55.190043;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 14 action { action_id: 27301117 params { param_id: 1 value: "\000\001" } } } }; *)
(* 2023-01-27 17:48:55.191833;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\024" } } action { action_profile_member_id: 14 } } }; *)
let test_6 = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } };
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [{ arg_id = 2; value = Bigint.of_int 1 };
                                         { arg_id = 1; value = Bigint.of_int 10}] };
               priority = 10;
             };
  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10} };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  0} }];
               action = Action { action_id = 17183246; args = [] };
               priority = -1; (*UNKNOWN*)
             };
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 3; match_key = Ternary { value = Bigint.of_int 10; mask = Bigint.of_int 4095 } }];
               action = Action { action_id = 24158268;
                                 args = [{ arg_id = 1; value = Bigint.of_int 1 }] } ;
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  1 } }];
               action = Action { action_id = 30307755; args = [] };
               priority = -1 (* unknown *)
             };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "25887770890";} (*"\000\006\007\010\t\n";*)
                         ];
               action = Action { action_id = 21791748;
                                 args = [{ arg_id = 1; value = Bigint.of_int 10; }]};
               priority = 10 };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "4328719365" } ];
               action = Action { action_id = 21791748; args = [ { arg_id = 1; value = Bigint.of_int 20 } ] };
               priority = 10 };
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 13;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 0 }]};
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } }];
               action = Profile {action_profile_member_id = 13 };
               priority = -1 (*unknown*)};
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 14;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 1} ] };
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 20 }}];
               action = Profile {action_profile_member_id = 14 };
               priority = -1;
             };
]

(* 2023-01-27 17:48:55.331470;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\000" } } match { field_id: 2 exact { value: "\000" } } action { action { action_id: 24266015 params { param_id: 2 value: "\001" } params { param_id: 1 value: "\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.333614;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\000" } } action { action { action_id: 17183246 } } } }; *)
(* 2023-01-27 17:48:55.335810;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\001" } } match { field_id: 2 exact { value: "\000" } } action { action { action_id: 24266015 params { param_id: 2 value: "\001" } params { param_id: 1 value: "\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.337892;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\001" } } action { action { action_id: 17183246 } } } }; *)
(* 2023-01-27 17:48:55.340137;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\006\007\010\t\n" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.342320;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\001\002\003\004\005" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\024" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.344439;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 15 action { action_id: 27301117 params { param_id: 1 value: "\000\000" } } } }; *)
(* 2023-01-27 17:48:55.346083;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\n" } } action { action_profile_member_id: 15 } } }; *)
(* 2023-01-27 17:48:55.347939;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 16 action { action_id: 27301117 params { param_id: 1 value: "\000\001" } } } }; *)
(* 2023-01-27 17:48:55.349604;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\024" } } action { action_profile_member_id: 16 } } }; *)
let test_7 = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } };
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [{ arg_id = 2; value = Bigint.of_int 1 };
                                         { arg_id = 1; value = Bigint.of_int 10}] };
               priority = 10;
             };
  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10} };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  0} }];
               action = Action { action_id = 17183246; args = [] };
               priority = -1; (*UNKNOWN*)
             };
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 3; match_key = Ternary { value = Bigint.of_int 10; mask = Bigint.of_int 4095 } }];
               action = Action { action_id = 24158268;
                                 args = [{ arg_id = 1; value = Bigint.of_int 1 }] } ;
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  1 } }];
               action = Action { action_id = 30307755; args = [] };
               priority = -1 (* unknown *)
             };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "25887770890";} (*"\000\006\007\010\t\n";*)
                         ];
               action = Action { action_id = 21791748;
                                 args = [{ arg_id = 1; value = Bigint.of_int 10; }]};
               priority = 10 };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "4328719365" } ];
               action = Action { action_id = 21791748; args = [ { arg_id = 1; value = Bigint.of_int 20 } ] };
               priority = 10 };
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 15;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 0 }]};
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } }];
               action = Profile {action_profile_member_id = 15 };
               priority = -1 (*unknown*)};
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 16;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 1} ] };
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 20 }}];
               action = Profile {action_profile_member_id = 16 };
               priority = -1;
             };
]

(* 2023-01-27 17:48:55.496203;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\000" } } match { field_id: 2 exact { value: "\000" } } action { action { action_id: 24266015 params { param_id: 2 value: "\001" } params { param_id: 1 value: "\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.498301;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\000" } } action { action { action_id: 17183246 } } } }; *)
(* 2023-01-27 17:48:55.500421;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\001" } } match { field_id: 2 exact { value: "\000" } } action { action { action_id: 24266015 params { param_id: 2 value: "\001" } params { param_id: 1 value: "\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.502552;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\001" } } action { action { action_id: 17183246 } } } }; *)
(* 2023-01-27 17:48:55.505040;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\006\007\010\t\n" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.507288;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\001\002\003\004\005" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\024" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.509648;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 17 action { action_id: 27301117 params { param_id: 1 value: "\000\000" } } } }; *)
(* 2023-01-27 17:48:55.511557;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\n" } } action { action_profile_member_id: 17 } } }; *)
(* 2023-01-27 17:48:55.513730;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 18 action { action_id: 27301117 params { param_id: 1 value: "\000\001" } } } }; *)
(* 2023-01-27 17:48:55.515419;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\024" } } action { action_profile_member_id: 18 } } }; *)
let test_8 = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } };
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [{ arg_id = 2; value = Bigint.of_int 1 };
                                         { arg_id = 1; value = Bigint.of_int 10}] };
               priority = 10;
             };
  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10} };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  0} }];
               action = Action { action_id = 17183246; args = [] };
               priority = -1; (*UNKNOWN*)
             };
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 3; match_key = Ternary { value = Bigint.of_int 10; mask = Bigint.of_int 4095 } }];
               action = Action { action_id = 24158268;
                                 args = [{ arg_id = 1; value = Bigint.of_int 1 }] } ;
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  1 } }];
               action = Action { action_id = 30307755; args = [] };
               priority = -1 (* unknown *)
             };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "25887770890";} (*"\000\006\007\010\t\n";*)
                         ];
               action = Action { action_id = 21791748;
                                 args = [{ arg_id = 1; value = Bigint.of_int 10; }]};
               priority = 10 };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "4328719365" } ];
               action = Action { action_id = 21791748; args = [ { arg_id = 1; value = Bigint.of_int 20 } ] };
               priority = 10 };
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 17;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 0 }]};
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } }];
               action = Profile {action_profile_member_id = 17 };
               priority = -1 (*unknown*)};
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 18;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 1} ] };
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 20 }}];
               action = Profile {action_profile_member_id = 18 };
               priority = -1;
             };
]

(* 2023-01-27 17:48:55.662541;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\000" } } match { field_id: 2 exact { value: "\001" } } match { field_id: 3 ternary { value: "\000\n" mask: "\017\377" } } action { action { action_id: 24158268 params { param_id: 1 value: "\001" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.664728;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\000" } } action { action { action_id: 30307755 } } } }; *)
(* 2023-01-27 17:48:55.666834;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\001" } } match { field_id: 2 exact { value: "\000" } } action { action { action_id: 24266015 params { param_id: 2 value: "\001" } params { param_id: 1 value: "\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.668948;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\001" } } action { action { action_id: 17183246 } } } }; *)
(* 2023-01-27 17:48:55.671217;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\006\007\010\t\n" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.673540;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\001\002\003\004\005" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\024" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.675785;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 19 action { action_id: 27301117 params { param_id: 1 value: "\000\000" } } } }; *)
(* 2023-01-27 17:48:55.677565;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\n" } } action { action_profile_member_id: 19 } } }; *)
(* 2023-01-27 17:48:55.679761;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 20 action { action_id: 27301117 params { param_id: 1 value: "\000\001" } } } }; *)
(* 2023-01-27 17:48:55.681442;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\024" } } action { action_profile_member_id: 20 } } }; *)
let test_9 = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } };
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [{ arg_id = 2; value = Bigint.of_int 1 };
                                         { arg_id = 1; value = Bigint.of_int 10}] };
               priority = 10;
             };
  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10} };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  0} }];
               action = Action { action_id = 17183246; args = [] };
               priority = -1; (*UNKNOWN*)
             };
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 3; match_key = Ternary { value = Bigint.of_int 10; mask = Bigint.of_int 4095 } }];
               action = Action { action_id = 24158268;
                                 args = [{ arg_id = 1; value = Bigint.of_int 1 }] } ;
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  1 } }];
               action = Action { action_id = 30307755; args = [] };
               priority = -1 (* unknown *)
             };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "25887770890";} (*"\000\006\007\010\t\n";*)
                         ];
               action = Action { action_id = 21791748;
                                 args = [{ arg_id = 1; value = Bigint.of_int 10; }]};
               priority = 10 };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "4328719365" } ];
               action = Action { action_id = 21791748; args = [ { arg_id = 1; value = Bigint.of_int 20 } ] };
               priority = 10 };
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 19;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 0 }]};
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } }];
               action = Profile {action_profile_member_id = 19 };
               priority = -1 (*unknown*)};
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 20;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 1} ] };
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 20 }}];
               action = Profile {action_profile_member_id = 20 };
               priority = -1;
             };
]

(* 2023-01-27 17:48:55.831125;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\000" } } match { field_id: 2 exact { value: "\001" } } match { field_id: 3 ternary { value: "\000\n" mask: "\017\377" } } action { action { action_id: 24158268 params { param_id: 1 value: "\001" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.833220;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\000" } } action { action { action_id: 30307755 } } } }; *)
(* 2023-01-27 17:48:55.835359;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\001" } } match { field_id: 2 exact { value: "\000" } } action { action { action_id: 24266015 params { param_id: 2 value: "\001" } params { param_id: 1 value: "\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.837407;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\001" } } action { action { action_id: 17183246 } } } }; *)
(* 2023-01-27 17:48:55.839583;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\006\007\010\t\n" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.841830;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\001\002\003\004\005" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\024" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:55.843883;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 21 action { action_id: 27301117 params { param_id: 1 value: "\000\000" } } } }; *)
(* 2023-01-27 17:48:55.845552;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\n" } } action { action_profile_member_id: 21 } } }; *)
(* 2023-01-27 17:48:55.847459;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 22 action { action_id: 27301117 params { param_id: 1 value: "\000\001" } } } }; *)
(* 2023-01-27 17:48:55.849204;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\024" } } action { action_profile_member_id: 22 } } }; *)
let test_10 = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } };
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [{ arg_id = 2; value = Bigint.of_int 1 };
                                         { arg_id = 1; value = Bigint.of_int 10}] };
               priority = 10;
             };
  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10} };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  0} }];
               action = Action { action_id = 17183246; args = [] };
               priority = -1; (*UNKNOWN*)
             };
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 3; match_key = Ternary { value = Bigint.of_int 10; mask = Bigint.of_int 4095 } }];
               action = Action { action_id = 24158268;
                                 args = [{ arg_id = 1; value = Bigint.of_int 1 }] } ;
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  1 } }];
               action = Action { action_id = 30307755; args = [] };
               priority = -1 (* unknown *)
             };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "25887770890";} (*"\000\006\007\010\t\n";*)
                         ];
               action = Action { action_id = 21791748;
                                 args = [{ arg_id = 1; value = Bigint.of_int 10; }]};
               priority = 10 };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "4328719365" } ];
               action = Action { action_id = 21791748; args = [ { arg_id = 1; value = Bigint.of_int 20 } ] };
               priority = 10 };
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 21;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 0 }]};
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } }];
               action = Profile {action_profile_member_id = 21 };
               priority = -1 (*unknown*)};
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 22;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 1} ] };
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 20 }}];
               action = Profile {action_profile_member_id = 22 };
               priority = -1;
             };
]

(* 2023-01-27 17:48:55.998752;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\000" } } match { field_id: 2 exact { value: "\001" } } match { field_id: 3 ternary { value: "\000\n" mask: "\017\377" } } action { action { action_id: 24158268 params { param_id: 1 value: "\001" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:56.000851;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\000" } } action { action { action_id: 30307755 } } } }; *)
(* 2023-01-27 17:48:56.002991;1;type: INSERT entity { table_entry { table_id: 43310977 match { field_id: 1 exact { value: "\000\001" } } match { field_id: 2 exact { value: "\000" } } action { action { action_id: 24266015 params { param_id: 2 value: "\001" } params { param_id: 1 value: "\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:56.005109;1;type: INSERT entity { table_entry { table_id: 49262446 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 exact { value: "\000\001" } } action { action { action_id: 17183246 } } } }; *)
(* 2023-01-27 17:48:56.007329;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\006\007\010\t\n" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\n" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:56.009810;1;type: INSERT entity { table_entry { table_id: 43623757 match { field_id: 1 exact { value: "\000\n" } } match { field_id: 2 ternary { value: "\000\001\002\003\004\005" mask: "\377\377\377\377\377\377" } } action { action { action_id: 21791748 params { param_id: 1 value: "\000\000\000\024" } } } priority: 10 } }; *)
(* 2023-01-27 17:48:56.011919;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 23 action { action_id: 27301117 params { param_id: 1 value: "\000\000" } } } }; *)
(* 2023-01-27 17:48:56.013883;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\n" } } action { action_profile_member_id: 23 } } }; *)
(* 2023-01-27 17:48:56.015820;1;type: INSERT entity { action_profile_member { action_profile_id: 291115404 member_id: 24 action { action_id: 27301117 params { param_id: 1 value: "\000\001" } } } }; *)
(* 2023-01-27 17:48:56.017527;1;type: INSERT entity { table_entry { table_id: 47960972 match { field_id: 1 exact { value: "\000\000\000\024" } } action { action_profile_member_id: 24 } } }; *)
let test_11 = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } };
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [{ arg_id = 2; value = Bigint.of_int 1 };
                                         { arg_id = 1; value = Bigint.of_int 10}] };
               priority = 10;
             };
  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10} };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  0} }];
               action = Action { action_id = 17183246; args = [] };
               priority = -1; (*UNKNOWN*)
             };
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int 1 } };
                          { field_id = 3; match_key = Ternary { value = Bigint.of_int 10; mask = Bigint.of_int 4095 } }];
               action = Action { action_id = 24158268;
                                 args = [{ arg_id = 1; value = Bigint.of_int 1 }] } ;
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = Exact { value = Bigint.of_int  1 } }];
               action = Action { action_id = 30307755; args = [] };
               priority = -1 (* unknown *)
             };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "25887770890";} (*"\000\006\007\010\t\n";*)
                         ];
               action = Action { action_id = 21791748;
                                 args = [{ arg_id = 1; value = Bigint.of_int 10; }]};
               priority = 10 };
  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } };
                          { field_id = 2; match_key = exact_mac "4328719365" } ];
               action = Action { action_id = 21791748; args = [ { arg_id = 1; value = Bigint.of_int 20 } ] };
               priority = 10 };
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 23;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 0 }]};
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1; match_key = Exact { value = Bigint.of_int 10 } }];
               action = Profile {action_profile_member_id = 23 };
               priority = -1 (*unknown*)};
  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 24;
                        action_id = 27301117;
                        args = [{ arg_id = 1; value = Bigint.of_int 1} ] };
  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 20 }}];
               action = Profile {action_profile_member_id = 24 };
               priority = -1;
             };
]
