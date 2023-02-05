(* test.FabricTaggedPacketInTest *)
open Runtime

let test = [
  TableEntry { table_id = 44104738;
               matches = [{ field_id = 5;
                            match_key = Ternary { value = Bigint.of_int 2048;
                                                  mask = Bigint.of_int 65535 } }];
               action = Action { action_id = 23579892; args = [] };
               priority = 10 };

TableEntry { table_id = 43310977;
             matches = [{ field_id = 1;
                          match_key = Exact { value = Bigint.of_int 0 } } ;
                        { field_id = 2;
                          match_key = Exact { value = Bigint.of_int 1 } } ;
                        { field_id = 3;
                          match_key = Ternary { value = Bigint.of_int 10;
                                                mask = Bigint.of_int 4095 } }];
             action = Action { action_id = 24158268;
                               args = [ { arg_id = 1;
                                          value = Bigint.of_int 1 } ] };
             priority = 10 };

TableEntry { table_id = 43310977;
             matches = [{ field_id = 1;
                          match_key = Exact { value = Bigint.of_int 1 } } ;
                        { field_id = 2;
                          match_key = Exact { value = Bigint.of_int 1 } } ;
                        { field_id = 3;
                          match_key = Ternary { value = Bigint.of_int 10;
                                                mask = Bigint.of_int 4095 } }];
             action = Action { action_id = 24158268;
                               args = [ { arg_id = 1;
                                          value = Bigint.of_int 1 } ] };
             priority = 10 };
]
