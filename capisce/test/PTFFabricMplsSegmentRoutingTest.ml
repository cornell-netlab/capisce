(*test.FabricMplsSegmentRoutingTest*)
open Runtime

let test_0 = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [ { arg_id = 2;
                                            value = Bigint.of_int 2 };
                                          { arg_id = 1;
                                            value = Bigint.of_int 4094 } ] };
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 4094 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 17183246;
                                 args = []};
               priority = -1};

  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 1 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [ { arg_id = 2;
                                            value = Bigint.of_int 2 };
                                          { arg_id = 1;
                                            value = Bigint.of_int 4094 } ] };
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 4094 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 1 } }];
               action = Action { action_id = 17183246;
                                 args = []};
               priority = -1};

  TableEntry { table_id = 49718154;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } } ;
                          { field_id = 3;
                            match_key = Ternary { value = Bigint.of_int 8931116;
                                                  mask = Bigint.of_int 65535 } } ;
                          { field_id = 4;
                            match_key = Exact { value = Bigint.of_int 2048 } } ;
                          { field_id = 2;
                            match_key = Ternary { value =  Bigint.of_int 43521;
                                                  mask = Bigint.of_string "281474976710655"  } }];
               action = Action { action_id = 25032921;
                                 args = [ { arg_id = 1;
                                            value = Bigint.of_int 1 } ] };
               priority = 10 };

  TableEntry { table_id = 37768578;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } }];
               action = Action { action_id = 30066030;
                                 args = [ { arg_id = 1;
                                            value =  Bigint.of_int 100 } ] };
               priority = -1};

  TableEntry { table_id = 36626242;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } }];
               action = Action { action_id = 22765924;
                                 args = [ { arg_id = 1;
                                            value =  Bigint.of_int 100 } ] };
               priority = -1};

  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 1;
                        action_id = 20985706;
                        args = [ { arg_id = 1;
                                   value = Bigint.of_int 1 };
                                 { arg_id = 2;
                                   value =  Bigint.of_int 43521 };
                                 { arg_id = 3;
                                   value = Bigint.of_int 2 } ] };

  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } }];
               action = Profile { action_profile_member_id = 1 };
               priority = -1};
]
let test_1 = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [ { arg_id = 2;
                                            value = Bigint.of_int 2 };
                                          { arg_id = 1;
                                            value = Bigint.of_int 4094 } ] };
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 4094 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 17183246;
                                 args = []};
               priority = -1};

  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 1 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [ { arg_id = 2;
                                            value = Bigint.of_int 2 };
                                          { arg_id = 1;
                                            value = Bigint.of_int 4094 } ] };
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 4094 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 1 } }];
               action = Action { action_id = 17183246;
                                 args = []};
               priority = -1};

  TableEntry { table_id = 49718154;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } } ;
                          { field_id = 3;
                            match_key = Ternary { value = Bigint.of_int 8931116;
                                                  mask = Bigint.of_int 65535 } } ;
                          { field_id = 4;
                            match_key = Exact { value = Bigint.of_int 2048 } } ;
                          { field_id = 2;
                            match_key = Ternary { value =  Bigint.of_int 43521;
                                                  mask = Bigint.of_string "281474976710655"  } }];
               action = Action { action_id = 25032921;
                                 args = [ { arg_id = 1;
                                            value = Bigint.of_int 1 } ] };
               priority = 10 };

  TableEntry { table_id = 37768578;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } }];
               action = Action { action_id = 30066030;
                                 args = [ { arg_id = 1;
                                            value =  Bigint.of_int 100 } ] };
               priority = -1};

  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 2;
                        action_id = 20985706;
                        args = [ { arg_id = 1;
                                   value = Bigint.of_int 1 };
                                 { arg_id = 2;
                                   value =  Bigint.of_int 43521 };
                                 { arg_id = 3;
                                   value = Bigint.of_int 2 } ] };

  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } }];
               action = Profile { action_profile_member_id = 2 };
               priority = -1};
]

let test_2 = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [ { arg_id = 2;
                                            value = Bigint.of_int 2 };
                                          { arg_id = 1;
                                            value = Bigint.of_int 4094 } ] };
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 4094 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 17183246;
                                 args = []};
               priority = -1};

  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 1 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [ { arg_id = 2;
                                            value = Bigint.of_int 2 };
                                          { arg_id = 1;
                                            value = Bigint.of_int 4094 } ] };
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 4094 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 1 } }];
               action = Action { action_id = 17183246;
                                 args = []};
               priority = -1};

  TableEntry { table_id = 49718154;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } } ;
                          { field_id = 3;
                            match_key = Ternary { value = Bigint.of_int 8931116;
                                                  mask = Bigint.of_int 65535 } } ;
                          { field_id = 4;
                            match_key = Exact { value = Bigint.of_int 2048 } } ;
                          { field_id = 2;
                            match_key = Ternary { value =  Bigint.of_int 43521;
                                                  mask = Bigint.of_string "281474976710655"  } }];
               action = Action { action_id = 25032921;
                                 args = [ { arg_id = 1;
                                            value = Bigint.of_int 1 } ] };
               priority = 10 };

  TableEntry { table_id = 37768578;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } }];
               action = Action { action_id = 30066030;
                                 args = [ { arg_id = 1;
                                            value =  Bigint.of_int 100 } ] };
               priority = -1};

  TableEntry { table_id = 36626242;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } }];
               action = Action { action_id = 22765924;
                                 args = [ { arg_id = 1;
                                            value =  Bigint.of_int 100 } ] };
               priority = -1};

  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 3;
                        action_id = 20985706;
                        args = [ { arg_id = 1;
                                   value = Bigint.of_int 1 };
                                 { arg_id = 2;
                                   value =  Bigint.of_int 43521 };
                                 { arg_id = 3;
                                   value = Bigint.of_int 2 } ] };

  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } }];
               action = Profile { action_profile_member_id = 3 };
               priority = -1};
]

let test_3 = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [ { arg_id = 2;
                                            value = Bigint.of_int 2 };
                                          { arg_id = 1;
                                            value = Bigint.of_int 4094 } ] };
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 4094 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 17183246;
                                 args = []};
               priority = -1};

  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 1 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [ { arg_id = 2;
                                            value = Bigint.of_int 2 };
                                          { arg_id = 1;
                                            value = Bigint.of_int 4094 } ] };
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 4094 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 1 } }];
               action = Action { action_id = 17183246;
                                 args = []};
               priority = -1};

  TableEntry { table_id = 49718154;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } } ;
                          { field_id = 3;
                            match_key = Ternary { value = Bigint.of_int 8931116;
                                                  mask = Bigint.of_int 65535 } } ;
                          { field_id = 4;
                            match_key = Exact { value = Bigint.of_int 2048 } } ;
                          { field_id = 2;
                            match_key = Ternary { value =  Bigint.of_int 43521;
                                                  mask = Bigint.of_string "281474976710655"  } }];
               action = Action { action_id = 25032921;
                                 args = [ { arg_id = 1;
                                            value = Bigint.of_int 1 } ] };
               priority = 10 };

  TableEntry { table_id = 37768578;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } }];
               action = Action { action_id = 30066030;
                                 args = [ { arg_id = 1;
                                            value =  Bigint.of_int 100 } ] };
               priority = -1};

  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 4;
                        action_id = 20985706;
                        args = [ { arg_id = 1;
                                   value = Bigint.of_int 1 };
                                 { arg_id = 2;
                                   value =  Bigint.of_int 43521 };
                                 { arg_id = 3;
                                   value = Bigint.of_int 2 } ] };

  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } }];
               action = Profile { action_profile_member_id = 4 };
               priority = -1};
]

let test_4 = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [ { arg_id = 2;
                                            value = Bigint.of_int 2 };
                                          { arg_id = 1;
                                            value = Bigint.of_int 4094 } ] };
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 4094 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 17183246;
                                 args = []};
               priority = -1};

  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 1 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [ { arg_id = 2;
                                            value = Bigint.of_int 2 };
                                          { arg_id = 1;
                                            value = Bigint.of_int 4094 } ] };
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 4094 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 1 } }];
               action = Action { action_id = 17183246;
                                 args = []};
               priority = -1};

  TableEntry { table_id = 49718154;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } } ;
                          { field_id = 3;
                            match_key = Ternary { value = Bigint.of_int 8931116;
                                                  mask = Bigint.of_int 65535 } } ;
                          { field_id = 4;
                            match_key = Exact { value = Bigint.of_int 2048 } } ;
                          { field_id = 2;
                            match_key = Ternary { value =  Bigint.of_int 43521;
                                                  mask = Bigint.of_string "281474976710655"  } }];
               action = Action { action_id = 25032921;
                                 args = [ { arg_id = 1;
                                            value = Bigint.of_int 1 } ] };
               priority = 10 };

  TableEntry { table_id = 37768578;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } }];
               action = Action { action_id = 30066030;
                                 args = [ { arg_id = 1;
                                            value =  Bigint.of_int 100 } ] };
               priority = -1};

  TableEntry { table_id = 36626242;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } }];
               action = Action { action_id = 22765924;
                                 args = [ { arg_id = 1;
                                            value =  Bigint.of_int 100 } ] };
               priority = -1};

  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 5;
                        action_id = 20985706;
                        args = [ { arg_id = 1;
                                   value = Bigint.of_int 1 };
                                 { arg_id = 2;
                                   value =  Bigint.of_int 43521 };
                                 { arg_id = 3;
                                   value = Bigint.of_int 5 } ] };

  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } }];
               action = Profile { action_profile_member_id = 5 };
               priority = -1};
]

let test_5 = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [ { arg_id = 2;
                                            value = Bigint.of_int 2 };
                                          { arg_id = 1;
                                            value = Bigint.of_int 4094 } ] };
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 4094 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 17183246;
                                 args = []};
               priority = -1};

  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 1 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [ { arg_id = 2;
                                            value = Bigint.of_int 2 };
                                          { arg_id = 1;
                                            value = Bigint.of_int 4094 } ] };
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 4094 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 1 } }];
               action = Action { action_id = 17183246;
                                 args = []};
               priority = -1};

  TableEntry { table_id = 49718154;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } } ;
                          { field_id = 3;
                            match_key = Ternary { value = Bigint.of_int 8931116;
                                                  mask = Bigint.of_int 65535 } } ;
                          { field_id = 4;
                            match_key = Exact { value = Bigint.of_int 2048 } } ;
                          { field_id = 2;
                            match_key = Ternary { value =  Bigint.of_int 43521;
                                                  mask = Bigint.of_string "281474976710655"  } }];
               action = Action { action_id = 25032921;
                                 args = [ { arg_id = 1;
                                            value = Bigint.of_int 1 } ] };
               priority = 10 };

  TableEntry { table_id = 37768578;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } }];
               action = Action { action_id = 30066030;
                                 args = [ { arg_id = 1;
                                            value =  Bigint.of_int 100 } ] };
               priority = -1};

  TableEntry { table_id = 36626242;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } }];
               action = Action { action_id = 22765924;
                                 args = [ { arg_id = 1;
                                            value =  Bigint.of_int 100 } ] };
               priority = -1};

  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 5;
                        action_id = 20985706;
                        args = [ { arg_id = 1;
                                   value = Bigint.of_int 1 };
                                 { arg_id = 2;
                                   value =  Bigint.of_int 43521 };
                                 { arg_id = 3;
                                   value = Bigint.of_int 2 } ] };

  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } }];
               action = Profile { action_profile_member_id = 5 };
               priority = -1};
]

let test_6 = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [ { arg_id = 2;
                                            value = Bigint.of_int 2 };
                                          { arg_id = 1;
                                            value = Bigint.of_int 4094 } ] };
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 4094 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 17183246;
                                 args = []};
               priority = -1};

  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 1 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [ { arg_id = 2;
                                            value = Bigint.of_int 2 };
                                          { arg_id = 1;
                                            value = Bigint.of_int 4094 } ] };
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 4094 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 1 } }];
               action = Action { action_id = 17183246;
                                 args = []};
               priority = -1};

  TableEntry { table_id = 49718154;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } } ;
                          { field_id = 3;
                            match_key = Ternary { value = Bigint.of_int 8931116;
                                                  mask = Bigint.of_int 65535 } } ;
                          { field_id = 4;
                            match_key = Exact { value = Bigint.of_int 2048 } } ;
                          { field_id = 2;
                            match_key = Ternary { value =  Bigint.of_int 43521;
                                                  mask = Bigint.of_string "281474976710655"  } }];
               action = Action { action_id = 25032921;
                                 args = [ { arg_id = 1;
                                            value = Bigint.of_int 1 } ] };
               priority = 10 };

  TableEntry { table_id = 37768578;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } }];
               action = Action { action_id = 30066030;
                                 args = [ { arg_id = 1;
                                            value =  Bigint.of_int 100 } ] };
               priority = -1};

  ActionProfileMember { action_profile_id = 291115404;
                        member_id = 6;
                        action_id = 20985706;
                        args = [ { arg_id = 1;
                                   value = Bigint.of_int 1 };
                                 { arg_id = 2;
                                   value =  Bigint.of_int 43521 };
                                 { arg_id = 3;
                                   value = Bigint.of_int 2 } ] };

  TableEntry { table_id = 47960972;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } }];
               action = Profile { action_profile_member_id = 6 };
               priority = -1};
]