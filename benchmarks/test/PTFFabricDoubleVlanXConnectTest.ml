(* test.FabricDoubleVlanXConnectTest *)
open Runtime

let test_0 = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.zero } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.one } } ;
                          { field_id = 3;
                            match_key = Ternary { value = Bigint.of_int 100;
                                                  mask = Bigint.of_int 4095 } }];
               action = Action { action_id = 24158268;
                                 args = [ { arg_id = 1;
                                            value = Bigint.one } ] };
               priority = 10 };

TableEntry { table_id = 49262446;
             matches = [{ field_id = 1;
                          match_key = Exact { value = Bigint.of_int 100} } ;
                        { field_id = 2;
                          match_key = Exact { value = Bigint.zero } }];
             action = Action { action_id = 30307755; args = []};
           priority = 01};

TableEntry { table_id = 43310977;
             matches = [{ field_id = 1;
                          match_key = Exact { value = Bigint.one } } ;
                        { field_id = 2;
                          match_key = Exact { value = Bigint.one } } ;
                        { field_id = 3;
                          match_key = Ternary { value = Bigint.of_int 100;
                                                mask = Bigint.of_int 4095} }];
             action = Action { action_id = 24158268;
                               args = [ { arg_id = 1;
                                          value = Bigint.one } ] };
             priority = 10 };

TableEntry { table_id = 49262446;
             matches = [{ field_id = 1;
                          match_key = Exact { value = Bigint.of_int 100 } } ;
                        { field_id = 2;
                          match_key = Exact { value = Bigint.one } }];
             action = Action { action_id = 30307755; args = []};
             priority = -1;
           };

TableEntry { table_id = 43623757;
             matches = [{ field_id = 1;
                          match_key = Exact { value = Bigint.of_int 100 } }];
             action = Action { action_id = 21791748;
                               args = [ { arg_id = 1;
                                          value = Bigint.of_int 99 } ] };
             priority = 10 };

TableEntry { table_id = 48735793;
             matches = [{ field_id = 2;
                          match_key = Exact { value = Bigint.of_int 99 } } ;
                        { field_id = 1;
                          match_key = Exact { value = Bigint.zero } }];
             action = Action { action_id = 24640974;
                               args = [ { arg_id = 1;
                                          value = Bigint.one } ] };
             priority = -1;
           };

TableEntry { table_id = 48735793;
             matches = [{ field_id = 2;
                          match_key = Exact { value = Bigint.of_int 99 } } ;
                        { field_id = 1;
                          match_key = Exact { value = Bigint.one } }];
             action = Action { action_id = 24640974;
                               args = [ { arg_id = 1;
                                          value = Bigint.zero } ] };
             priority = -1};
]

let test_1 = [

  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.zero } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.one } } ;
                          { field_id = 3;
                            match_key = Ternary { value =  Bigint.of_int 100;
                                                  mask = Bigint.of_int 4095 } }];
               action = Action { action_id = 24158268;
                                 args = [ { arg_id = 1;
                                            value = Bigint.one } ] };
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.zero } }];
               action = Action { action_id = 30307755; args = []};
               priority = -1;
             };

  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.one } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.one } } ;
                          { field_id = 3;
                            match_key = Ternary { value =  Bigint.of_int 100;
                                                  mask = Bigint.of_int 4095 } }];
               action = Action { action_id = 24158268;
                                 args = [ { arg_id = 1;
                                            value = Bigint.one } ] };
               priority = 10 };

TableEntry { table_id = 49262446;
             matches = [{ field_id = 1;
                          match_key = Exact { value =  Bigint.of_int 100 } } ;
                        { field_id = 2;
                          match_key = Exact { value = Bigint.one } }];
             action = Action { action_id = 30307755; args = []};
             priority = -1
           };

  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } }];
               action = Action { action_id = 21791748;
                                 args = [ { arg_id = 1;
                                            value =  Bigint.of_int 99 } ] };
               priority = 10 };

  TableEntry { table_id = 48735793;
               matches = [{ field_id = 2;
                            match_key = Exact { value =  Bigint.of_int 99 } } ;
                          { field_id = 1;
                            match_key = Exact { value = Bigint.zero } }];
               action = Action { action_id = 24640974;
                                 args = [ { arg_id = 1;
                                            value = Bigint.one } ] };
             priority = -1};

  TableEntry { table_id = 48735793;
               matches = [{ field_id = 2;
                            match_key = Exact { value =  Bigint.of_int 99 } } ;
                          { field_id = 1;
                            match_key = Exact { value = Bigint.one } }];
               action = Action { action_id = 24640974;
                                 args = [ { arg_id = 1;
                                            value = Bigint.zero } ] };
               priority = -1;
             }
]

let test_2 = [
  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.zero } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.one } } ;
                          { field_id = 3;
                            match_key = Ternary { value =  Bigint.of_int 100;
                                                  mask = Bigint.of_int 4095 } }];
               action = Action { action_id = 24158268;
                                 args = [ { arg_id = 1;
                                            value = Bigint.one } ] };
               priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.zero } }];
               action = Action { action_id = 30307755; args = []};
               priority = -1;
             };

  TableEntry { table_id = 43310977;
               matches = [{ field_id = 1;
                            match_key = Exact { value = Bigint.one } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.one } } ;
                          { field_id = 3;
                            match_key = Ternary { value =  Bigint.of_int 100;
                                                  mask = Bigint.of_int 4095 } }];
               action = Action { action_id = 24158268;
                                 args = [ { arg_id = 1;
                                            value = Bigint.one } ] };
             priority = 10 };

  TableEntry { table_id = 49262446;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } } ;
                          { field_id = 2;
                            match_key = Exact { value = Bigint.one } }];
               action = Action { action_id = 30307755; args = []};
               priority = -1};

  TableEntry { table_id = 43623757;
               matches = [{ field_id = 1;
                            match_key = Exact { value =  Bigint.of_int 100 } }];
               action = Action { action_id = 21791748;
                                 args = [ { arg_id = 1;
                                            value =  Bigint.of_int 99 } ] };
               priority = 10 };

  TableEntry { table_id = 48735793;
               matches = [{ field_id = 2;
                            match_key = Exact { value =  Bigint.of_int 99 } } ;
                          { field_id = 1;
                            match_key = Exact { value = Bigint.zero } }];
               action = Action { action_id = 24640974;
                                 args = [ { arg_id = 1;
                                            value = Bigint.one } ]};
               priority = -1};

  TableEntry { table_id = 48735793;
               matches = [{ field_id = 2;
                            match_key = Exact { value =  Bigint.of_int 99 } } ;
                          { field_id = 1;
                            match_key = Exact { value = Bigint.one } }];
               action = Action { action_id = 24640974;
                                 args = [ { arg_id = 1;
                                            value = Bigint.zero } ] };
               priority = -1 };
]
