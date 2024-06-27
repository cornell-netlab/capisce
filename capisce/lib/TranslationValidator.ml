open Core

module type Cmd_intf = sig
  type t
  val vc : t -> BExpr.t option
end

module Make
    (Source : Cmd_intf)
    (Target : Cmd_intf)
    (Simulation : sig
       val relate_st : Source.t -> Target.t -> BExpr.t option
       val relate_nd : Source.t -> Target.t -> BExpr.t option
     end
    ) = struct

  let validate (src : Source.t) (tgt : Target.t) =
    let open Option.Let_syntax in
    let%bind phi_src = Source.vc src in
    let%bind phi_tgt = Target.vc tgt in
    let%bind phi_st  = Simulation.relate_st src tgt in
    let%map  phi_nd  = Simulation.relate_nd src tgt in
    let formula =
      BExpr.ands_
        [phi_src;
         phi_tgt;
         phi_st;
         BExpr.not_ phi_nd;
        ]
    in
    let variables = BExpr.vars formula |> Tuple2.uncurry (@) in
    Solver.check_sat_model
      ~timeout:None
      variables
      formula

  end
