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

module OperandSet = Set.Make(struct
                               type t = operand
                               let compare = compare
                             end)

let inst_gen inst : OperandSet.t =
  let opset = OperandSet.empty in
  match inst with
  | Label _ | Jump _ | Return -> opset
  | Move (o1, o2) -> OperandSet.add o2 opset
  | Arith (o1, o2, _, o3) -> OperandSet.add o2 (OperandSet.add o3 opset)
  | Load (o1, o2, _) -> OperandSet.add o2 opset
  | Store (o1, _, o2) -> OperandSet.add o1 (OperandSet.add o2 opset)
  | Call op -> OperandSet.add op opset
  | If (o1, _, o2, _, _) -> OperandSet.add o1 (OperandSet.add o2 opset)

let inst_kill inst : OperandSet.t =
  let killset = OperandSet.empty in
  match inst with
  | Move (o1, _)
  | Arith (o1, _, _, _) 
  | Load (o1, _, _) -> OperandSet.add o1 killset
  | _ -> killset

let changed : bool ref = ref true
let change x = (changed := true; x)

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
  let insts = List.flatten f in
  let rec live_in_init (instructions : inst list) : OperandSet.t list =
    match instructions with
      [] -> []
    | hd :: tl -> inst_gen hd :: live_in_init tl in
  let rec live_out_init (instructions : inst list) : OperandSet.t list =
    match instructions with
      [] -> []
    | hd :: tl -> OperandSet.empty :: live_out_init tl in
  let live_in_full = live_in_init insts in
  let live_out_full = live_out_init insts in
  let rec find_in live_in instructions lbl =
    match instructions, live_in with
      [], _ | _, [] -> raise FatalError (* failed to find label in the instruction list *)
    | hd :: tl, hd2 :: tl2 ->
      (match hd with
	Label l -> if l = lbl then hd2 else find_in tl2 tl lbl
      | _ -> find_in tl2 tl lbl) in
  let rec update_lives instructions live_in live_out accum : (OperandSet.t list * OperandSet.t list) =
    match instructions with
      [] -> accum
    | hd :: tl ->
      (let out =
	 match hd with
	   Jump lbl -> find_in live_in_full insts lbl
	 | If (o1, c, o2, l1, l2) -> OperandSet.union (find_in live_in_full insts l1) (find_in live_in_full insts l2)
	 | Return -> OperandSet.empty
	 | _ ->
	   (match live_in with
	     [] -> raise FatalError (* should never happen because live_in and instructions should be the same length *)
	   | hd2 :: [] -> OperandSet.empty
	   | hd2 :: next :: tl2 -> next) in
       match live_in, live_out with
	 [], _ | _, [] -> raise FatalError (* should never happen because live_in, live_out, and instructions should be the same length *)
       | hd2 :: tl2, hd3 :: tl3 ->
	 (let live_in_rest, live_out_rest = accum in
	  if OperandSet.equal out hd3 then update_lives tl tl2 tl3 (live_in_rest @ [hd2], live_out_rest @ [hd3])
	  else (let new_in = OperandSet.union (inst_gen hd) (OperandSet.diff hd3 (inst_kill hd)) in
		change (update_lives tl tl2 tl3 (live_in_rest @ [new_in], live_out_rest @ [out]))))) in
  let rec loop live_in live_out =
    if (!changed) then
      (let _ = changed := false in
       let new_live_in, new_live_out = update_lives insts live_in live_out ([], []) in
       loop new_live_in new_live_out)
    else (live_in, live_out) in
  let (final_live_in, final_live_out) = changed := true; loop live_in_full live_out_full in
  let add_clique (t:OperandSet.t) (g:interfere_graph) = raise Implement_Me in
  let rec build_graph g instructions live_in =
    match instructions with
      [] -> g
    | hd :: tl ->
      (match live_in with
	[] -> raise FatalError (* should never happen because instructions and live_in should be the same length *)
      | hd2 :: tl2 -> build_graph (add_clique hd2 g) tl tl2) in
  let rec graph_with_nodes = raise Implement_Me in
  build_graph InterfereGraph.empty_graph insts final_live_in

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


