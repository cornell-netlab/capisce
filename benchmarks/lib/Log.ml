open Core
open ANSITerminal

type t = Off | On | Break [@@deriving eq]

let is_off flg = equal !flg Off
let enabled flg = not (is_off flg)
let is_break flg = equal !flg Break

module FLAGS = struct
  let debug = ref Off
  (** debug should correspond to the current debugging effort; no commit should contain debug messages *)

  let override = ref false
  (** If the overide flag is on, debug statements are allowed, otherwise they produce runtime exceptions *)

  let measure = ref Off
  (** Triggers measurement commands. print to stderr *)

  let dot = ref Off
  (** generates graphs and prints dot compilation commands information *)

  let smt = ref Off
  (** prints SMT queries and their results *)

  let irs = ref Off
  (** shows IRs  *)

  let graph = ref Off
  (** shows graph creation information*)

  let path_gen = ref On
  (** shows path generation/iteration information *)

  let compiler = ref Off
  (** Prints info about the compiler passes *)

  let smart = ref Off
  (* Prints smart constructor information messages*)

  let rewrites = ref Off
  (* Prints the smart-constructor rewrites that are being performed *)

  let qe = ref Off
  (* printfs messages regarding top-level quantifier elimination *)

  let monitor = ref Off
  (* printfs messages regarding runtime CP monitor  *)

  let exploder = ref Off

  let tree = ref Off

  let error = ref On
  let warn = ref On
end

let parse verbosity flag char =
  if not (Char.is_lowercase char) then begin
    failwithf "Tried to check verbosity of %c in %s" char verbosity ()
  end;
  let contains = String.contains verbosity in
  if contains char then
    flag := On
  else if contains (Char.uppercase char) then
    flag := Break
  else
    flag := Off

let override () =
  FLAGS.override := true

let parse_flags verbosity =
  let parse = parse verbosity in
  parse FLAGS.debug 'd';          (* Debug *)
  parse FLAGS.measure 'm';        (* Measure  *)
  parse FLAGS.dot 'v';            (* graphViz *)
  parse FLAGS.smt 'z';            (* Z3 *)
  parse FLAGS.irs 'i';            (* Irs *)
  parse FLAGS.graph 'g';          (* Graph *)
  parse FLAGS.path_gen 'p';       (* Path_gen *)
  parse FLAGS.compiler 'c';       (* Compiler *)
  parse FLAGS.smart 's';          (* Smart constructors *)
  parse FLAGS.rewrites 'r';       (* Rewrites *)
  parse FLAGS.qe 'q';             (* Quantifier elimination *)
  parse FLAGS.exploder 'e';       (* Exploder *)
  parse FLAGS.tree 't';           (* spanning Tree logging *)
  parse FLAGS.monitor 'o'         (* Runtime mOnitor *)

  (* let size d = measure (Printf.sprintf "size,%f,%d" (Clock.now()) d) *)

let dot_string f = Printf.sprintf "dot -Tps %s.dot -o %s.pdf; xdg-open %s.pdf;" f f f

let log flag fmt colors a : unit =
  if enabled flag then begin
    ANSITerminal.printf colors (fmt ^^ "\n%!") (Lazy.force a);
    Out_channel.flush stdout;
    Breakpoint.set ~colors (is_break flag)
  end


let error fmt   = log FLAGS.error     fmt [red]
let error_s s = error "%s" (lazy s)
let warn fmt    = log FLAGS.warn      fmt [yellow; Bold]
let smt fmt      = log FLAGS.smt      fmt [green]
let irs fmt      = log FLAGS.irs      fmt []
let path_gen fmt = log FLAGS.path_gen fmt [cyan; Bold]
let path_gen_s s = path_gen "%s" (lazy s)
let compiler fmt = log FLAGS.compiler fmt []
let compiler_s s = compiler "%s" (lazy s)
let smart fmt    = log FLAGS.smart    fmt []
let rewrites fmt = log FLAGS.rewrites fmt []
let qe fmt       = log FLAGS.qe       fmt []

let measure fmt = log FLAGS.measure   fmt []
let measure_s s = measure "%s" (lazy s)

let monitor fmt = log FLAGS.graph     fmt [cyan; Bold]
let monitor_s s = monitor "%s" @@ lazy s

let graph fmt    = log FLAGS.graph    fmt [green]
let graph_s s    = graph "%s" (lazy s)

let exploder fmt = log FLAGS.exploder fmt [red; Bold]
let exploder_s s = exploder "%s" (lazy s)

let tree fmt = log FLAGS.tree fmt []
let tree_s s = tree "%s" (lazy s)

let dot flag do_ fn =
  (*run [do_] then use [fn] to create the message*)
  if enabled FLAGS.dot && enabled flag then begin
    assert (not (String.is_substring fn ~substring:".dot"));
    do_ (Some (Printf.sprintf "%s.dot" fn));
    log FLAGS.dot "%s" [] (lazy (dot_string fn));
    Breakpoint.set (is_break FLAGS.dot || is_break flag)
  end

let graph_dot    = dot FLAGS.graph
let path_gen_dot = dot FLAGS.path_gen
let tree_dot     = dot FLAGS.tree

let debug fmt =
  if !FLAGS.override then
    log FLAGS.debug fmt [magenta; Bold]
  else
    failwith "REMOVE ALL DEBUG STATEMENTS"

let debug_s s = debug "%s" (lazy s)
