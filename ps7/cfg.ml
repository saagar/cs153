(* Saagar Deshpande and Emmet Jao *)
open Cfg_ast
module C = Cish_ast
exception Implement_Me
exception FatalError

(*******************************************************************)
(* PS7 TODO:  interference graph construction *)

module InterfereGraph =
struct
  type 'a graph = { nodes : 'a list; move_edges : ('a * 'a) list; non_move_edges : ('a * 'a) list }
  let empty_graph = { nodes = []; move_edges = []; non_move_edges = [] }
  let node_mem g v = List.mem v g.nodes
  let add_node g v = if node_mem g v then g else { nodes = v :: g.nodes; move_edges = g.move_edges; non_move_edges = g.non_move_edges }
  let edge_mem g v1 v2 move_related =
    (let (vv1, vv2) = if v1 < v2 then (v1, v2) else (v2, v1) in
     if move_related then List.mem (vv1, vv2) g.move_edges else List.mem (vv1, vv2) g.non_move_edges)
  let add_edge g v1 v2 move_related = if edge_mem g v1 v2 move_related then g else
    (let (vv1, vv2) = if v1 < v2 then (v1, v2) else (v2, v1) in
     if move_related then { nodes = g.nodes; move_edges = (vv1, vv2) :: g.move_edges; non_move_edges = g.non_move_edges }
     else { nodes = g.nodes; move_edges = g.move_edges; non_move_edges = (vv1, vv2) :: g.non_move_edges })
end

(* an interference graph maps a variable x to the set of variables that
 * y such that x and y are live at the same point in time.  It's up to
 * you how you want to represent the graph.  I've just put in a dummy
 * definition for now.  *)
type interfere_graph = operand InterfereGraph.graph

(* given a function (i.e., list of basic blocks), construct the
 * interference graph for that function.  This will require that
 * you build a dataflow analysis for calculating what set of variables
 * are live-in and live-out for each program point. *)
let build_interfere_graph (f : func) : interfere_graph =
  (*let insts = List.flatten f in
  let init_live_in*) raise Implement_Me

(* given an interference graph, generate a string representing it *)
let str_of_interfere_graph (g : interfere_graph) : string =
    raise Implement_Me


(*******************************************************************)
(* PS8 TODO:  graph-coloring, coalescing register assignment *)
(* You will need to build a mapping from variables to MIPS registers
   using the ideas behind the graph-coloring register allocation
   heuristics described in class.  This may involve spilling some
   of the variables into memory, so be sure to adjust the prelude
   of the function so that you allocate enough space on the stack
   to store any spilled variables.  The output should be a CFG
   function that doesn't use any variables (except for function
   names.)
*)
let reg_alloc (f : func) : func = 
    raise Implement_Me

(* Finally, translate the ouptut of reg_alloc to Mips instructions *)
let cfg_to_mips (f : func ) : Mips.inst list = 
    raise Implement_Me



(*******************************************************************)
(* Command-Line Interface for printing CFG. You probably will not 
    need to modify this for PS7, but will definitely need to for 
    PS8. Feel free to add additional command-line options as you
    see fit (e.g. -printmips, -evalmips, -printcfg, etc...). 
    Please make sure to document any changes you make.
*)
let parse_file() =
  let argv = Sys.argv in
  let _ = 
    if Array.length argv != 2
    then (prerr_string ("usage: " ^ argv.(0) ^ " [file-to-parse]\n");
    exit 1) in
  let ch = open_in argv.(1) in
  Cish_parse.program Cish_lex.lexer (Lexing.from_channel ch)

let parse_stdin() = 
  Cish_parse.program Cish_lex.lexer (Lexing.from_channel stdin)

let print_interference_graph (():unit) (f : C.func) : unit =
  let graph = build_interfere_graph (fn2blocks f) in
  Printf.printf "%s\n%s\n\n" (C.fn2string f) (str_of_interfere_graph graph)

let _ =
  let prog = parse_file() in
  List.fold_left print_interference_graph () prog


