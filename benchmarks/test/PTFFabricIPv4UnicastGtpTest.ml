(* test.FabricIPv4UnicastGtpTest *)
open Runtime

let test = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 0 } }];
               action = Action { action_id = 24266015;
                                 args = [ { arg_id = 2;
                                            value = Bigint.of_int 1 };
                                          { arg_id = 1;
                                            value =  Bigint.of_int 100 } ] };
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } } ;
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
                                            value = Bigint.of_int 1 };
                                          { arg_id = 1;
                                            value =  Bigint.of_int 200 } ] };
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 200 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.of_int 1 } }];
               action = Action { action_id = 17183246;
                                 args = []};
               priority = -1};

  TableEntry { table_id = 49718154;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.of_int 0 } } ;
                          { field_id = 4;
                            match_key = Exact { value = Bigint.of_int 2048 } } ;
                          { field_id = 2;
                            match_key = Ternary { value =  Bigint.of_int 43521;
                                                  mask = Bigint.of_string "281474976710655"  } }];
               action = Action { action_id = 25032921;
                                 args = [ { arg_id = 1;
                                            value = Bigint.of_int 2 } ] };
               priority = 10 };

  TableEntry { table_id = 41754650;
               matches = [{ field_id = 1;
                            match_key = Ternary { value =  Bigint.of_int 167773184;
                                                  mask = Bigint.of_int 4294967040  } }];
               action = Action { action_id = 19792090;
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

  TableEntry { table_id = 48011802;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } }];
               action = Action { action_id = 33475378;
                                 args = [ { arg_id = 1;
                                            value =  Bigint.of_int 200 } ] };
               priority = -1};
]
