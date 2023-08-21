let tests : unit Alcotest.test_case list =
  ECMPTest.tests
  @ NetpaxosAcceptorTest.tests
  @ ResubmitTest.tests
  @ NDPRouterTest.tests
  @ HeavyHitter1Test.tests
  @ ArpTest.tests
  @ MultiprotocolTest.tests
  @ MCNatTest.tests
  @ TSSwitchingTest.tests
  @ HeavyHitter2Test.tests
  @ FlowletTest.tests
  @ HulaTest.tests
