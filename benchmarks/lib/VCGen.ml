let rec wp (c : Cmd.t) (t : Test.t) : Test.t =
  match c with
  | Assume t1 -> TBin(LArr, t1, t)
  | Assert t1 -> TBin(LAnd, t1, t)
  | Havoc x -> Forall([x], t)
  | Assign (x,e) -> Test.subst x e t
  | Seq (c1,c2) ->  wp c2 t |> wp c1
  | Choice (c1,c2) -> TBin(LAnd, wp c1 t, wp c2 t)                        

