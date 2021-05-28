let k tid = Var.make (Printf.sprintf "k%d" tid) 8
let x tid = Var.make (Printf.sprintf "x%d" tid) 8

let tablegen n : Cmd.t =
  let open Cmd in
  let keys = [k n] in
  let d = Var.make "d" 8 in
  let actions = [
      d,
      Assign (x n, Var d)
    ]
  in
  let def = Assume TTrue in
  table n keys actions def

let rec gen_asst n : Test.t =
  let open Test in
  if n <= 0 then
    TTrue
  else 
    TBin(LAnd, TNot(TEq(Var (x n), Var (k (n+1)))), gen_asst (n-1))
  
                       
let rec gen_benchmark ntables cs =
  if ntables <= 0 then
    cs
  else
    tablegen ntables :: cs
    |> gen_benchmark (ntables - 1)

  
let benchmark ntables =  
  let prog = Cmd.sequence (gen_benchmark ntables []) in
  let asst = gen_asst (ntables - 1) in
  let phi = VCGen.wp prog asst in
  let (ds,_) = Test.vars phi in
  Test.Forall(ds, phi)
