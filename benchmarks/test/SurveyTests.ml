let tests : unit Alcotest.test_case list =
  ECMPTest.tests
  @ NetpaxosAcceptorTest.tests
  @ ResubmitTest.tests
