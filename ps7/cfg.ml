(* Saagar Deshpande and Emmet Jao *)
open Cfg_ast
module C = Cish_ast
exception Implement_Me
exception FatalError
exception IllegalCFG

(*******************************************************************)
(* PS7 TODO:  interference graph construction *)

(* our graph implementation uses an adjacency list *)
module InterfereGraph =
struct
  type 'a graph = { nodes : 'a list; move_edges : ('a * 'a) list; non_move_edges : ('a * 'a) list }
  let empty_graph = { nodes = []; move_edges = []; non_move_edges = [] }
  let node_mem g v = List.mem v g.nodes
  let add_node g v = if node_mem g v then g else { nodes = v :: g.nodes; move_edges = g.move_edges; non_move_edges = g.non_move_edges }
  let edge_mem g v1 v2 move_related =
    (let (vv1, vv2) = if v1 < v2 then (v1, v2) else (v2, v1) in
     if move_related then List.mem (vv1, vv2) g.move_edges else List.mem (vv1, vv2) g.non_move_edges)
  let add_edge g v1 v2 move_related = 
    if (edge_mem g v1 v2 move_related) || (node_mem g v1 = false) || (node_mem g v2 = false) || (v1 = v2) then g else
    (let (vv1, vv2) = if v1 < v2 then (v1, v2) else (v2, v1) in
     if move_related then { nodes = g.nodes; move_edges = (vv1, vv2) :: g.move_edges; non_move_edges = g.non_move_edges }
     else { nodes = g.nodes; move_edges = g.move_edges; non_move_edges = (vv1, vv2) :: g.non_move_edges })
end

module OperandSet = Set.Make(struct
                               type t = operand
                               let compare = compare
                             end)
(* This is a tuple, which can be used to represent a MOVE or just an edge in the graph *)
module TupleSet = Set.Make(struct
                              type t = operand * operand
                              let compare = compare
                            end)

(* Gen for instructions. Returns operand set containing all Gens required for
 * one instruction *)
let inst_gen inst : OperandSet.t =
  match inst with
  | Label _ | Jump _ -> OperandSet.empty
  (* Return uses $2 (and $31 but that's not an available color) *)
  | Return -> OperandSet.singleton (Reg Mips.R2)
  | Move (o1, o2) -> OperandSet.singleton o2
  | Arith (o1, o2, _, o3) -> List.fold_right OperandSet.add [o2; o3] OperandSet.empty
  | Load (o1, o2, _) -> OperandSet.singleton o2
  | Store (o1, _, o2) -> List.fold_right OperandSet.add [o1; o2] OperandSet.empty
  (* Call uses the argument registers according to Lucas *)
  | Call op -> List.fold_right OperandSet.add [op; Reg Mips.R4; Reg Mips.R5; Reg Mips.R6; Reg Mips.R7] OperandSet.empty
  | If (o1, _, o2, _, _) -> List.fold_right OperandSet.add [o1; o2] OperandSet.empty

(* Kill for instructions. Returns operand set containing all Kills required for
 * one instruction *)
let inst_kill inst : OperandSet.t =
  match inst with
  | Move (o1, _)
  | Arith (o1, _, _, _) 
  | Load (o1, _, _) -> OperandSet.singleton o1
  | Call _ -> OperandSet.singleton (Reg Mips.R2)
  | _ -> OperandSet.empty

(* for convergence *)
let changed : bool ref = ref true
let change x = (changed := true; x)

(* an interference graph maps a variable x to the set of variables that
 * y such that x and y are live at the same point in time.  It's up to
 * you how you want to represent the graph.  I've just put in a dummy
 * definition for now.  *)
type interfere_graph = operand InterfereGraph.graph

(* add all operands for the given instruction to  the interference graph. *)
let add_inst_to_graph inst graph : interfere_graph =
  match inst with
  (* these do nothing *)
  | Label _ | Jump _ | Return -> graph
  | Move (o1, o2) -> InterfereGraph.add_node (InterfereGraph.add_node graph o1) o2
  | Arith (o1, o2, _, o3) -> InterfereGraph.add_node (InterfereGraph.add_node (InterfereGraph.add_node graph o1) o2) o3
  | Load (o1, o2, _) -> InterfereGraph.add_node (InterfereGraph.add_node graph o1) o2
  | Store (o1, _, o2) -> InterfereGraph.add_node (InterfereGraph.add_node graph o1) o2
  | Call op -> InterfereGraph.add_node graph op
  | If (o1, _, o2, _, _) -> InterfereGraph.add_node (InterfereGraph.add_node graph o1) o2

(* prune the interference graph nodes
 * only keep Var and Reg nodes in the graph *)
let prune_interfere_graph_nodes (g : interfere_graph) : interfere_graph =
  let all_nodes = g.InterfereGraph.nodes in
  let rec prune_node_helper (node_list : operand list) : operand list =
    match node_list with
    | [] -> []
    | hd::tl ->
        (* should keep Vars and Regs, ignore everything else *)
        (match hd with 
        | Var _ -> hd :: (prune_node_helper tl)
        (*| Reg _ | Lab _ -> hd :: (prune_node_helper tl)*)
        | Reg _ -> hd :: (prune_node_helper tl)
        | _ -> prune_node_helper tl
        )
  in
  { InterfereGraph.nodes = (prune_node_helper all_nodes) ; 
    InterfereGraph.move_edges = g.InterfereGraph.move_edges; 
    InterfereGraph.non_move_edges = g.InterfereGraph.non_move_edges }

let pig_debug = ref false

(* given a function (i.e., list of basic blocks), construct the
 * interference graph for that function.  This will require that
 * you build a dataflow analysis for calculating what set of variables
 * are live-in and live-out for each program point. *)
let build_interfere_graph (f : func) : interfere_graph =
  (* debug code *)
  let rec set2str opset =
    match OperandSet.elements opset with
      [] -> ""
    | hd::tl -> (match hd with Reg _ | Var _ -> op2string hd | _ -> "") ^ " " ^ set2str (OperandSet.remove hd opset) in
  let rec print_live_in live_in instructions =
    match (live_in, instructions) with
      [], _ -> ()
    | _, [] -> ()
    | hd::tl, hd2::tl2 -> print_string (inst2string hd2 ^ "     " ^ set2str hd ^ "\n"); print_live_in tl tl2 in
  (* end debug code *)

  (* flatten the blocks into a pure list of instructions. we will do livein and
   * liveout for each instruction *)
  (*print_string (fun2string f);*)
  let insts = List.flatten f in
  (* all live in sets are Gen(instruction) at start *)
  let rec live_in_init (instructions : inst list) : OperandSet.t list =
    match instructions with
      [] -> []
    | hd :: tl -> inst_gen hd :: live_in_init tl in
  let rec live_out_init (instructions : inst list) : OperandSet.t list =
    match instructions with
      [] -> []
    | hd :: tl -> OperandSet.empty :: live_out_init tl in
  let rec find_in live_in instructions lbl =
    match instructions, live_in with
      [], _ | _, [] -> raise FatalError (* failed to find label in the instruction list *)
    | hd :: tl, hd2 :: tl2 ->
      (match hd with
	Label l -> if l = lbl then hd2 else find_in tl2 tl lbl
      | _ -> find_in tl2 tl lbl) in
  let rec update_lives instructions live_in live_out accum live_in_full: (OperandSet.t list * OperandSet.t list) =
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
	  if OperandSet.equal out hd3 then update_lives tl tl2 tl3 (live_in_rest @ [hd2], live_out_rest @ [hd3]) live_in_full
	  else (let new_in = OperandSet.union (inst_gen hd) (OperandSet.diff out (inst_kill hd)) in
		change (update_lives tl tl2 tl3 (live_in_rest @ [new_in], live_out_rest @ [out]) live_in_full)))) in
  let rec loop live_in live_out =
    if (!changed) then
      (let _ = changed := false in
       let new_live_in, new_live_out = update_lives insts live_in live_out ([], []) live_in in
       loop new_live_in new_live_out)
    else (live_in, live_out) in
  (* all live in sets are Gen(instruction) at start *)
  (* all live out sets are empty at start.*)
  let (final_live_in, final_live_out) = changed := true; loop (live_in_init insts) (live_out_init insts) in
  (* create an empty graph with all nodes from instructions *)
  let rec graph_init (instructions : inst list) (giraffe : interfere_graph) : interfere_graph =
    match instructions with
    [] -> giraffe
    | hd :: tl -> graph_init tl (add_inst_to_graph hd giraffe) in
  (* new interference graph with only var and register nodes*)
  let igraph = prune_interfere_graph_nodes (graph_init insts InterfereGraph.empty_graph) in
  (* add a set into the graph *)
  let add_clique (t:OperandSet.t) (g:interfere_graph) = 
    let elts = OperandSet.elements t in
    (* for a single node in a LiveIn set, add all edges to elts in LiveIn set *)
    let rec add_edges_for_item item things_added graph : interfere_graph =
      (match things_added with
      | [] -> graph
      | hd::tl ->
	(match (item, hd) with
	  (Reg _, Reg _) -> add_edges_for_item item tl graph
	| _ -> add_edges_for_item item tl (InterfereGraph.add_edge graph item hd false))) in 
    (* for each LiveIn set, add all of the edges between all possible pairs in
    * the set. *)
    let rec add_clique_helper things_to_add things_added graph : interfere_graph =
      match things_to_add with
      | [] -> graph
      | hd::tl -> add_clique_helper tl (hd::things_added) (add_edges_for_item hd things_added graph) in
    add_clique_helper elts [] g
  in
  (* for each element in the set, add edges from the element to each caller saves register *)
  let add_caller_saves_interfere (t:OperandSet.t) (g:interfere_graph) =
    let elts = OperandSet.elements t in
    let all_caller_saves = List.map (fun x -> Reg x) 
                      [Mips.R2;Mips.R8;Mips.R9;Mips.R10;Mips.R11;Mips.R12;Mips.R13;Mips.R14;Mips.R15;Mips.R24;Mips.R25] in
    let rec add_rest_caller_saves item caller_saves graph : interfere_graph =
      (match caller_saves with
      | [] -> graph
      | hd::tl ->
	(match (item, hd) with
	  (Reg _, Reg _) -> add_rest_caller_saves item tl graph
	| _ -> add_rest_caller_saves item tl (InterfereGraph.add_edge graph item hd false))) in 
    let rec add_caller_saves_helper things_to_add graph : interfere_graph =
      match things_to_add with
	[] -> graph
      | hd::tl -> add_caller_saves_helper tl (add_rest_caller_saves hd all_caller_saves graph) in
    let rec add_nodes_to_graph nodes graph =
      match nodes with
	[] -> graph
      | hd::tl -> add_nodes_to_graph tl (InterfereGraph.add_node graph hd) in
    let graph_with_nodes = add_nodes_to_graph all_caller_saves g in
    add_caller_saves_helper elts graph_with_nodes
  in
  let rec build_graph g instructions live_in =
    match instructions with
      [] -> g
    | hd :: tl ->
      (match live_in with
	[] -> raise FatalError (* should never happen because instructions and live_in should be the same length *)
      | hd2 :: tl2 ->
	(match hd with
	  Call op -> build_graph (add_clique hd2 (add_caller_saves_interfere hd2 g)) tl tl2
	| _ -> build_graph (add_clique hd2 g) tl tl2)) in
  (* need to handle zero-length live ranges caused by unused variables *)
  (* suppose we have an instruction i. if i kills a variable x and x is not in i's live-out set and i doesn't gen x, then add
     edges from x to everything in i's live-out set *)
  let rec add_edges_for_dead_code instructions live_in live_out g : interfere_graph =
    (* add edges from item to each of items *)
    let rec add_rest_edges item items graph : interfere_graph =
      (match items with
	[] -> graph
      | hd::tl ->
	(match (item, hd) with
	  (Reg _, Reg _) -> add_rest_edges item tl graph
	| _ -> add_rest_edges item tl (InterfereGraph.add_edge graph item hd false))) in
    let rec add_edges_dead_helper x inset outset genset graph : interfere_graph =
      if (OperandSet.mem x outset = false) && (OperandSet.mem x genset = false) then add_rest_edges x (OperandSet.elements outset) graph else graph in
    match instructions, live_in, live_out with
      [], _, _ | _, [], _ | _, _, [] -> g
    | hd::tl, hd2::tl2, hd3::tl3 ->
      (let killlist = OperandSet.elements (inst_kill hd) in
       let genset = inst_gen hd in
       let rec add_edges_dead_helper_2 kl graph =
	 (match kl with
	   [] -> graph
	 | x::rest -> add_edges_dead_helper_2 rest (add_edges_dead_helper x hd2 hd3 genset graph)) in
       add_edges_for_dead_code tl tl2 tl3 (add_edges_dead_helper_2 killlist g))
  in
  (* the graph now has all interference (non-move-related) edges *)
  let graph_without_move_edges = add_edges_for_dead_code insts final_live_in final_live_out (build_graph igraph insts final_live_in) in
  let rec add_move_edges instructions g : interfere_graph =
    match instructions with
      [] -> g
    | hd::tl ->
      (match hd with
	Move (o1, o2) -> add_move_edges tl (InterfereGraph.add_edge g o1 o2 true)
      | _ -> add_move_edges tl g)
  in
  let complete_graph = add_move_edges insts graph_without_move_edges in
  (if !pig_debug then print_live_in final_live_in insts else ());
  complete_graph

(* given an interference graph, generate a string representing it *)
(* move edges should be dashed, non move edges should be solid *)
let str_of_interfere_graph (g : interfere_graph) : string =
  let graph_str = "graph interfere_graph {" in
  let rec edge2string (edges : ('a * 'a) list) (style : string) : string =
    match edges with
    | [] -> ""
    | (t,f)::tl -> ("\n\t" ^ op2string t ^ " -- " ^ op2string f ^ style ^ ";") ^ 
                    (edge2string tl style)
  in
  graph_str ^ (edge2string g.InterfereGraph.move_edges "[style=dashed]") ^ 
  (edge2string g.InterfereGraph.non_move_edges "") ^ "\n}"

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

let rec list_to_operandset list_to_convert : OperandSet.t =
    match list_to_convert with
    | [] -> OperandSet.empty
    | hd::tl -> OperandSet.add hd (list_to_operandset tl)

let rec list_to_moveset list_to_convert : TupleSet.t =
    match list_to_convert with
    | [] -> TupleSet.empty
    | hd::tl -> TupleSet.add hd (list_to_moveset tl)

(* push node into list as if stack *)
let list_push (ref_list : operand list ref) node =
  let deref_list = !ref_list in
  let new_list = node::deref_list in
  ref_list := new_list 

(* pop top item from list, or return none *)
let list_pop (ref_list : operand list ref) node : operand option =
  let deref_list = !ref_list in
  match deref_list with
  | [] -> None
  | hd::tl -> ref_list := tl; Some hd

let reg_alloc (f : func) : func =
  (* copy of f that we modify over iterations *)
  let current_func = ref f in

  (* ignore 0, 1, 26, 27 - kernel
   * ignore 29, 30, 31 - sp, fp, ra *)
  (* reserve R3 for pseudo-ops involving immediates *)
  let reserved_regs : operand list = [Reg Mips.R0; Reg Mips.R1; Reg Mips.R3; Reg Mips.R26; 
                                    Reg Mips.R27; Reg Mips.R29; Reg Mips.R30; Reg Mips.R31] in
  let usable_regs : operand list = [Reg Mips.R2; Reg Mips.R4; Reg Mips.R5;
                                    Reg Mips.R6; Reg Mips.R7; Reg Mips.R8; Reg Mips.R9; Reg Mips.R10;
                                    Reg Mips.R11; Reg Mips.R12; Reg Mips.R13; Reg Mips.R14; Reg Mips.R15;
                                    Reg Mips.R16; Reg Mips.R17; Reg Mips.R18; Reg Mips.R19; Reg Mips.R20;
                                    Reg Mips.R21; Reg Mips.R22; Reg Mips.R23; Reg Mips.R24; Reg Mips.R25; Reg Mips.R28] in
  (* Number of registers, used to distinguish low- from high-degree nodes *)
  let k_reg = List.length usable_regs in
  let is_machine_register oper =
    match oper with
      Reg _ -> true
    | _ -> false in
  if List.length reserved_regs + List.length usable_regs <> 32 then raise FatalError;
  (* operand sets for all of the node types. *)
  let precolored = ref OperandSet.empty in
  let initial = ref OperandSet.empty in
  let simplifyWorklist = ref OperandSet.empty in
  let freezeWorklist = ref OperandSet.empty in
  let spillWorklist = ref OperandSet.empty in
  let spilledNodes = ref OperandSet.empty in
  let coalescedNodes = ref OperandSet.empty in
  let coloredNodes = ref OperandSet.empty in
  (* select stack for pushing and pulling nodes in order from graph *)
  let selectStack : operand list ref = ref [] in

  (* tuplesets for all of the move types *)
  let coalescedMoves = ref TupleSet.empty in
  let constrainedMoves = ref TupleSet.empty in
  let frozenMoves = ref TupleSet.empty in
  let worklistMoves = ref TupleSet.empty in
  let activeMoves = ref TupleSet.empty in

  (* list of all interfere edges *)
  let adjSet = ref TupleSet.empty in
  let adjList : (operand * OperandSet.t) list ref = ref [] in
  let degree : (operand * int) list ref = ref [] in
  let moveList : (operand * TupleSet.t) list ref = ref [] in
  (* alias[u] = v is a tuple of node u to alias mapping of v after coalescing *)
  let alias : (operand * operand) list ref = ref [] in
  (* color[n] = c is a tuple of node to register color *)
  let color : (operand * operand) list ref = ref [] in

  (* add to this when we do actual spills in RewriteProgram *)
  let num_already_spilled = ref 0 in
  (* maps a spilled temporary to an offset off the frame pointer. The first spilled temp will live at -8, the second at -12, etc. *)
  let varToStackPos : (operand * int) list ref = ref [] in

  (* get color[n] *)
  let retrieve_color node : operand =
    let rec color_helper n colorlist =
      match colorlist with
      | [] -> raise FatalError
      | (a,b)::tl -> if a = n then b else color_helper n tl
    in
    color_helper node !color
  in
  (* set color[n] = c *)
  let set_color node chosen_color =
    let rec set_helper n c colorlist : (operand * operand) list =
      match colorlist with
      | [] -> [(n, c)]
      | (a,b)::tl -> if a = n then (a,c)::tl else (a,b)::(set_helper n c tl)
    in
    let newcolors = set_helper node chosen_color !color in
    color := newcolors;
  in
  (* adjList[n] - returns the op set for the node n *)
  let retrieve_adjlist node : OperandSet.t=
    let rec adjlist_helper n adj =
      match adj with
      | [] -> OperandSet.empty
      | (op,set)::tl -> if op = n then set else adjlist_helper n tl
    in
    adjlist_helper node !adjList
  in
  (* adjList[u] = adjList[u] U {v} *)
  let unionadd_adjlist u v =
    let rec set_adjlist_helper u_look v_add nodelist : (operand * OperandSet.t) list =
      match nodelist with
      | [] -> [(u_look, OperandSet.singleton v_add)] (* this case is hit during setup_initial *)
      | (op,set)::tl -> if op = u_look then (op,(OperandSet.add v_add set))::tl else (op,set)::(set_adjlist_helper u_look v_add tl)
    in
    adjList := set_adjlist_helper u v !adjList
  in
  (* get moveList[n] *)
  let retrieve_movelist node : TupleSet.t =
    let rec movelist_helper n moves =
      match moves with
	[] -> TupleSet.empty (* this case is hit during setup_initial's add_move_to_movelist helper *)
      | (op,set)::tl -> if op = n then set else movelist_helper n tl
    in
    movelist_helper node !moveList
  in
  (* set moveList[n] := newlist *)
  let set_movelist n newlist =
    let rec update_movelist node movelist new_list : (operand * TupleSet.t) list =
      match movelist with
      | [] -> [(node, new_list)]
      | (hd,tupset)::tl -> if (hd = node) then (hd,new_list)::tl else (hd,tupset)::(update_movelist node tl new_list)
    in
    moveList := update_movelist n !moveList newlist
  in
  (* Adjacent(n): should return adjList[n] - selectStack - coalescedNodes *)
  let adjacent node : OperandSet.t =
    let selectStackSet = list_to_operandset !selectStack in
    let onion = OperandSet.union selectStackSet !coalescedNodes in
    let adjList_n_set = retrieve_adjlist node in
    OperandSet.diff adjList_n_set onion
  in
  (* NodeMoves(n): get moveList[n] intersect with union of activeMoves and worklistMoves *)
  let node_moves node : TupleSet.t =
    let onion = TupleSet.union !activeMoves !worklistMoves in
    TupleSet.inter (retrieve_movelist node) onion
  in
  (* get degree[n] *)
  let retrieve_degree node : int =
    let rec retrieve_helper n nodelist : int =
      match nodelist with
      | [] -> 0 (* if a node had degree 0, we never put it into the list so the base case will be hit *)
      | (hd,count)::tl -> if hd = n then count else retrieve_helper n tl
    in
    retrieve_helper node !degree
  in
  (* degree[n] = degree[n] + 1 *)
  let increment_degree node =
    let rec increment_helper n nodelist : (operand * int) list =
      match nodelist with
      | [] -> [(n, 1)] (* this case is hit during setup_initial *)
      | (op,count)::tl -> if op = n then (op,count+1)::tl else (op,count)::(increment_helper n tl)
    in 
    degree := increment_helper node !degree;
  in
  (* AddEdge(u,v) *)
  let add_edge u v =
    (* if the u and v are the same or the edge existed already, ignore *)
    if (u <> v) && ((TupleSet.mem (u,v) !adjSet) = false) 
    then
      (adjSet := TupleSet.add (u,v) !adjSet;
       adjSet := TupleSet.add (v,u) !adjSet;
       (if (OperandSet.mem u !precolored) = false then
           (unionadd_adjlist u v;
            increment_degree u));
       (if (OperandSet.mem v !precolored) = false then
           (unionadd_adjlist v u;
            increment_degree v)))
  in 
  (* MoveRelated(n) *)
  let move_related node : bool =
    let tupset = node_moves node in
    if TupleSet.is_empty tupset then false else true
  in
  (* EnableMoves(nodes) *)
  let enable_moves (nodes : OperandSet.t) =
    let inner_iterator single_node =
      (* inner loop updater *)
      let rec update_moves tuplist =
        match tuplist with
        | [] -> ()
        | hd::tl -> (if TupleSet.mem hd !activeMoves 
          then (activeMoves := TupleSet.remove hd !activeMoves;
                worklistMoves := TupleSet.add hd !worklistMoves));
          update_moves tl
      in
      update_moves (TupleSet.elements (node_moves single_node))
    in
    (* outer loop *)
    let rec nodes_iterator nodelist =
      match nodelist with
      | [] -> ()
      | hd::tl -> inner_iterator hd; nodes_iterator tl
    in
    nodes_iterator (OperandSet.elements nodes)
  in
  (* DecrementDegree(m) *)
  let decrement_degree (node : operand) =
    let m_deg = retrieve_degree node in
    (* make a new list with updated degree *)
    let rec dec_deg_for_node n nodelist : (operand * int) list =
      match nodelist with
      | [] -> []
      | (hd,count)::tl -> if hd = n then (hd,count-1)::tl else (hd,count)::(dec_deg_for_node n tl)
    in
    (* save the decremented degree... slow but ok *)
    let new_degree_list = dec_deg_for_node node !degree in 
    degree := new_degree_list;
    if m_deg = k_reg 
    then
      (let abunchofnodes = OperandSet.add node (adjacent node) in 
       enable_moves abunchofnodes;
       spillWorklist := OperandSet.remove node !spillWorklist;
       if (move_related node) then freezeWorklist := OperandSet.add node !freezeWorklist
       else simplifyWorklist := OperandSet.add node !simplifyWorklist)
  in
  (* SIMPLIFY *)
  let simplify () = 
    let node = OperandSet.choose !simplifyWorklist in 
    (* remove node from the worklist *)
    simplifyWorklist := OperandSet.remove node !simplifyWorklist;
    (* push the node into selectStack *)
    list_push selectStack node;
    (* get neighbor nodes decremented *)
    let rec dec_degree_loop nodelist =
      match nodelist with
      | [] -> ()
      | hd::tl -> (decrement_degree hd; dec_degree_loop tl)
    in
    dec_degree_loop (OperandSet.elements (adjacent node));
    ()
  in
  (* access alias[u] *)
  let retrieve_alias node : operand = 
    let rec retrieve_helper n aliaslist =
      match aliaslist with
      | [] -> raise FatalError (* if we reached end of list, we missed what we were looking for. *)
      | (a,b)::tl -> if a = n then b else retrieve_helper n tl
    in
    retrieve_helper node !alias
  in
  (* GetAlias(n) - returns the alias of some node n *)
  let rec get_alias node : operand = 
    if OperandSet.mem node !coalescedNodes then (get_alias (retrieve_alias node)) else node
  in
  (* alias[u] = v - this sets a new list by creating a new one *)
  let set_alias u v =
    let rec new_alias_list u_node v_rename aliaslist : (operand * operand) list =
      match aliaslist with
      | [] -> [(u_node, v_rename)]
      | (a,b)::tl -> if a = u_node then (a,v_rename)::tl else (a,b)::(new_alias_list u_node v_rename tl)
    in
    let updated_aliases = new_alias_list u v !alias in
    alias := updated_aliases;
  in
  (* AddWorkList(u) - adds a node to the simplify worklist *)
  let add_worklist node = 
    if (OperandSet.mem node !precolored = false && (move_related node) = false && (retrieve_degree node) < k_reg) then
      (freezeWorklist := OperandSet.remove node !freezeWorklist;
       simplifyWorklist := OperandSet.add node !simplifyWorklist)
  in
  let ok t r = 
    ((retrieve_degree t) < k_reg) || (OperandSet.mem t !precolored) || (TupleSet.mem (t,r) !adjSet)
  in
  (* briggs strategy *)
  let conservative nodes =
    let k = OperandSet.fold (fun x a -> if retrieve_degree x >= k_reg then a + 1 else a) nodes 0 in
    k < k_reg
  in
  (* combines v into u for node coalescing *)
  let combine u v =
    (if OperandSet.mem v !freezeWorklist then
	freezeWorklist := OperandSet.remove v !freezeWorklist
     else
	spillWorklist := OperandSet.remove v !spillWorklist);
    coalescedNodes := OperandSet.add v !coalescedNodes;
    set_alias v u;
    let onion = TupleSet.union (retrieve_movelist u) (retrieve_movelist v) in
    let _ = set_movelist u onion in
    let _ = enable_moves (OperandSet.singleton v) in
    let rec update_adjacents node_u nodelist =
      (match nodelist with
      | [] -> ()
      | hd::tl -> (add_edge hd node_u; decrement_degree hd; update_adjacents node_u tl))
    in
    update_adjacents u (OperandSet.elements (adjacent v));
    (if ((retrieve_degree u) >= k_reg) && (OperandSet.mem u !freezeWorklist) then
	(freezeWorklist := OperandSet.remove u !freezeWorklist;
	 spillWorklist := OperandSet.add u !spillWorklist))
  in
  (* COALESCE *)
  let coalesce () =
    let m = TupleSet.choose !worklistMoves in
    let (x, y) = m in
    let x_alias = get_alias x in
    let y_alias = get_alias y in
    let is_r0 op =
      match op with
	Reg Mips.R0 -> true
      | _ -> false
    in
    let (u, v) = (if OperandSet.mem y_alias !precolored then (y_alias, x_alias) else (x_alias, y_alias)) in
    worklistMoves := TupleSet.remove m !worklistMoves;
    if (u = v)
    then (coalescedMoves := TupleSet.add m !coalescedMoves; add_worklist u)
    else if ((OperandSet.mem v !precolored) || (TupleSet.mem (u, v) !adjSet) || is_r0 u || is_r0 v)
    then
      (constrainedMoves := TupleSet.add m !constrainedMoves;
       add_worklist u;
       add_worklist v)
    else if ((OperandSet.mem u !precolored) && (OperandSet.for_all (fun t -> ok t u) (adjacent v))
	     || (OperandSet.mem u !precolored = false) && (conservative (OperandSet.union (adjacent u) (adjacent v))))
    then
      (coalescedMoves := TupleSet.add m !coalescedMoves;
       combine u v;
       add_worklist u)
    else
      activeMoves := TupleSet.add m !activeMoves
  in
  let freeze_moves (node : operand) =
    let rec freeze_moves_helper moves =
      if TupleSet.is_empty moves = false then
	let m = TupleSet.choose moves in
	activeMoves := TupleSet.remove m !activeMoves;
	frozenMoves := TupleSet.add m !frozenMoves;
	let (x, y) = m in
	let v = if (get_alias y) = (get_alias node) then get_alias x else get_alias y in
	(if (TupleSet.is_empty (node_moves v)) && (retrieve_degree v < k_reg) then
	    (freezeWorklist := OperandSet.remove v !freezeWorklist;
	     simplifyWorklist := OperandSet.add v !simplifyWorklist));
	freeze_moves_helper (TupleSet.remove m moves)
    in
    freeze_moves_helper (node_moves node)
  in
  (* FREEZE *)
  let freeze () = 
    let u = OperandSet.choose !freezeWorklist in
    freezeWorklist := OperandSet.remove u !freezeWorklist;
    simplifyWorklist := OperandSet.add u !simplifyWorklist;
    let _ = freeze_moves u in ()
  in
  (* SELECT SPILL *)
  let select_spill (current_func : func) =
    let count_map : (operand * int) list ref = ref [] in 
    (* look for op in list and increment; if its not there, push (node,1) *)
    let increment_variable_list op =
      let rec inc_helper node (lst : (operand*int) list) : (operand * int) list =
        match lst with
        | [] -> [(node,1)]
        | (hd,c)::tl -> if hd = node then ((hd,c+1)::tl) else (hd,c)::inc_helper node tl
      in
      count_map := inc_helper op !count_map
    in
    let inc_counts (op : operand) =
      match op with
      | Var(v) -> increment_variable_list op
      | _ -> ()
    in
    (* go through function and increment all vars - both defs (which produce stores) and uses (which produce loads) *)
    let rec op_counter insts =
      match insts with
      | [] -> ()
      | hd::tl ->
        (match hd with
        | Label _ | Jump _ | Return -> op_counter tl 
        | Move (o1, o2) -> inc_counts o1; inc_counts o2; op_counter tl
        | Arith (o1, o2, _, o3) -> inc_counts o1; inc_counts o2; inc_counts o3; op_counter tl
        | Load (o1, o2, _) -> inc_counts o1; inc_counts o2; op_counter tl
        | Store (o1, _, o2) -> inc_counts o1; inc_counts o2; op_counter tl
        | Call op -> inc_counts op; op_counter tl
        | If (o1, _, o2, _, _) -> inc_counts o1; inc_counts o2; op_counter tl)
    in
    op_counter (List.flatten current_func);
    (* count_map[n] *)
    let retrieve_countmap op : int =
      let rec retrieve_helper node (lst : (operand*int) list) : int =
        match lst with
        | [] -> 1 (* should never happen *)
        | (hd,c)::tl -> if hd = node then c else retrieve_helper node tl
      in 
      retrieve_helper op !count_map
    in
    (* for all nodes in spillWorklist, do degree[n]/count_map[n] *)
    let spillList = OperandSet.elements !spillWorklist in
    let best_node : operand ref = ref (List.hd spillList) in
    let best_ratio : float ref = ref ((float_of_int (retrieve_degree !best_node)) /. (float_of_int (retrieve_countmap !best_node))) in
    let find_best_node nodes =
      let rec find_helper nodelist =
        match nodelist with
        | [] -> () (* didn't find anything better *)
        | hd::tl -> 
          let ratio = (float_of_int (retrieve_degree hd)) /. (float_of_int (retrieve_countmap hd)) in
          (if ratio > !best_ratio then (best_node := hd; best_ratio := ratio));
	  find_helper tl
      in
      find_helper nodes
    in
    find_best_node spillList;
    let m = !best_node in
    spillWorklist := OperandSet.remove m !spillWorklist;
    simplifyWorklist := OperandSet.add m !simplifyWorklist;
    freeze_moves m
  in
  (* ASSIGN COLORS *)
  let assign_colors () =
    let selectstack_loopbody node =
      let okColors = ref usable_regs in
      let w = retrieve_adjlist node in
      let rec loop_over_adjlist nodelist =
        match nodelist with
        | [] -> ()
        | hd::tl ->
          let onion = OperandSet.union !coloredNodes !precolored in
          (if OperandSet.mem (get_alias hd) onion 
           then
              let used = retrieve_color (get_alias hd) in
              let rec remove_okcolor c colorlist : operand list=
                match colorlist with
                | [] -> []
                | hd2::tl2 -> if hd2 = c then tl2 else hd2::(remove_okcolor c tl2)
              in okColors := remove_okcolor used !okColors);
	  loop_over_adjlist tl
      in
      let _ = loop_over_adjlist (OperandSet.elements w) in
      (if List.length !okColors = 0 then spilledNodes := OperandSet.add node !spilledNodes
       else 
          (coloredNodes := OperandSet.add node !coloredNodes;
	   let c = List.hd !okColors in set_color node c))
    in
    (* stack popping loop. EJ: this doesn't actually pop them, so add a line selectStack := [] *)
    let rec selectstack_loop_driver stacklist =
      match stacklist with
      | [] -> ()
      | hd::tl -> selectstack_loopbody hd; selectstack_loop_driver tl
    in
    let _ = selectstack_loop_driver !selectStack in
    let _ = selectStack := [] in
    let rec update_coalesced_colors nodelist =
      match nodelist with
      | [] -> ()
      | hd::tl ->
	set_color hd (retrieve_color (get_alias hd));
	update_coalesced_colors tl
    in
    update_coalesced_colors (OperandSet.elements !coalescedNodes)
  in
  (* for a spilled node, lookup its stack position (offset from fp) in varToStackPos *)
  let retrieve_var_offset node : int =
    let rec offset_helper n offsetlist =
      match offsetlist with
	[] -> raise FatalError
      | (a,b)::tl -> if a = n then b else offset_helper n tl
    in
    offset_helper node !varToStackPos
  in
  (* assign a spilled node to the next available stack position *)
  let set_var_offset node =
    let rec set_helper n o offsetlist : (operand * int) list =
      match offsetlist with
	[] -> [(n, o)]
      (* once we spill a node it should disappear from the code so shouldn't ever try to give it a new position on the stack *)
      | (a,b)::tl -> if a = n then (raise FatalError) else (a,b)::(set_helper n o tl)
    in
    varToStackPos := set_helper node (!num_already_spilled * (-4) - 8) !varToStackPos;
    num_already_spilled := !num_already_spilled + 1
  in
  (* REWRITE_PROGRAM *)
  let rewrite_func () =
    let sp = Reg Mips.R29 in
    let fp = Reg Mips.R30 in
    let old_func = !current_func in
    let rec assign_offsets (nodes:operand list) =
      match nodes with
	[] -> ()
      | hd::tl ->
	set_var_offset hd;
	assign_offsets tl
    in
    assign_offsets (OperandSet.elements !spilledNodes);
    (* allocate space by modifying two instructions emitted in cfg_ast.ml: the sixth one from the top (including the label) and the fifth one from the bottom *)
    let modify_space_alloc () =
      let first_block : block ref = ref [] in
      let last_block : block ref = ref [] in
      let other_blocks : block list ref = ref [] in
      first_block := List.hd old_func;
      let rec alloc_helper fblocks =
	(match fblocks with
	  [] -> raise FatalError
	| [b] -> last_block := b
	| hd::tl ->
	  other_blocks := !other_blocks @ [hd];
	  alloc_helper tl) in
      alloc_helper (List.tl old_func);
      let modify_first_block b =
	let new_sixth_inst =
	  match List.nth b 5 with
	    Move (Reg Mips.R29, Reg Mips.R29) | Arith (Reg Mips.R29, Reg Mips.R29, Minus, Int _) -> Arith (sp, sp, Minus, Int (!num_already_spilled * 4))
	  | _ -> raise FatalError (* couldn't find the allocating instruction *)
	in
	let rec modify_helper instructions n =
	  match instructions with
	    [] -> []
	  | hd::tl -> if n = 5 then new_sixth_inst::tl else hd::(modify_helper tl (n+1))
	in
	modify_helper b 0
      in
      let new_first_block = modify_first_block !first_block in
      let modify_last_block rev_b =
	let new_fifth_inst =
	  match List.nth rev_b 4 with
	    Move (Reg Mips.R29, Reg Mips.R29) | Arith (Reg Mips.R29, Reg Mips.R29, Plus, Int _) -> Arith (sp, sp, Plus, Int (!num_already_spilled * 4))
	  | _ -> raise FatalError (* couldn't find the deallocating instruction *)
	in
	let rec modify_helper instructions n =
	  match instructions with
	    [] -> []
	  | hd::tl -> if n = 4 then new_fifth_inst::tl else hd::(modify_helper tl (n+1))
	in
	modify_helper rev_b 0
      in
      let new_last_block = List.rev (modify_last_block (List.rev !last_block)) in
      current_func := new_first_block::(!other_blocks @ [new_last_block])
    in
    modify_space_alloc ();
    let middle_func = !current_func in
    (* replace defs and uses of each spilled node with a new temporary and insert stores/loads *)
    let rec modify_inst_2 (i:inst) : inst list =
      match i with
	Label _ -> [i]
      | Move (op1, op2) ->
	if OperandSet.mem op2 !spilledNodes then
	  (let t1 = Var (new_temp ()) in
	   (Load (t1, fp, retrieve_var_offset op2)) :: modify_inst_2 (Move (op1, t1)))
	else if OperandSet.mem op1 !spilledNodes then
	  (let t1 = Var (new_temp ()) in
	   [Move (t1, op2); Store (fp, retrieve_var_offset op1, t1)])
	else [i]
      | Arith (op1, op2, arith_op, op3) ->
	if OperandSet.mem op2 !spilledNodes then
	  (let t1 = Var (new_temp ()) in
	   (Load (t1, fp, retrieve_var_offset op2)) :: modify_inst_2 (Arith (op1, t1, arith_op, op3)))
	else if OperandSet.mem op3 !spilledNodes then
	  (let t1 = Var (new_temp ()) in
	   (Load (t1, fp, retrieve_var_offset op3)) :: modify_inst_2 (Arith (op1, op2, arith_op, t1)))
	else if OperandSet.mem op1 !spilledNodes then
	  (let t1 = Var (new_temp ()) in
	   [Arith (t1, op2, arith_op, op3); Store (fp, retrieve_var_offset op1, t1)])
	else [i]
      | Load (op1, op2, x) ->
	if OperandSet.mem op2 !spilledNodes then
	  (let t1 = Var (new_temp ()) in
	   (Load (t1, fp, retrieve_var_offset op2)) :: modify_inst_2 (Load (op1, t1, x)))
	else if OperandSet.mem op1 !spilledNodes then
	  (let t1 = Var (new_temp ()) in
	   [Load (t1, op2, x); Store (fp, retrieve_var_offset op1, t1)])
	else [i]
      | Store (op1, x, op2) ->
	if OperandSet.mem op2 !spilledNodes then
	  (let t1 = Var (new_temp ()) in
	   (Load (t1, fp, retrieve_var_offset op2)) :: modify_inst_2 (Store (op1, x, t1)))
	else if OperandSet.mem op1 !spilledNodes then
	  (let t1 = Var (new_temp ()) in
	   [Load (t1, fp, retrieve_var_offset op1); Store (t1, x, op2)])
	else [i]
      | Call op ->
	if OperandSet.mem op !spilledNodes then
	  (let t1 = Var (new_temp ()) in
	   [Load (t1, fp, retrieve_var_offset op); Call t1])
	else [i]
      | Jump _ -> [i]
      | If (op1, c, op2, l1, l2) ->
	if OperandSet.mem op2 !spilledNodes then
	  (let t1 = Var (new_temp ()) in
	   (Load (t1, fp, retrieve_var_offset op2)) :: modify_inst_2 (If (op1, c, t1, l1, l2)))
	else if OperandSet.mem op1 !spilledNodes then
	  (let t1 = Var (new_temp ()) in
	   [Load (t1, fp, retrieve_var_offset op1); If (t1, c, op2, l1, l2)])
	else [i]
      | Return -> [i]
    in
    let modify_inst (i:inst) : inst list =
      match i with
	Move (Var x, Var y) -> (if x = y then [] else modify_inst_2 i) (* redundant move check *)
      | _ -> modify_inst_2 i
    in
    let rec modify_insts b =
      match b with
	[] -> []
      | hd::tl -> (modify_inst hd) @ (modify_insts tl)
    in
    let rec modify_blocks blocks =
      match blocks with
	[] -> []
      | hd::tl -> (modify_insts hd)::(modify_blocks tl)
    in
    let new_func = modify_blocks middle_func in
    current_func := new_func
  in
  let rec make_worklist () =
    (match (OperandSet.elements !initial) with
      [] -> ()
    | hd::tl ->
      (initial := OperandSet.remove hd !initial;
       if retrieve_degree hd >= k_reg then spillWorklist := OperandSet.add hd !spillWorklist
       else if move_related hd then freezeWorklist := OperandSet.add hd !freezeWorklist
       else simplifyWorklist := OperandSet.add hd !simplifyWorklist);
      make_worklist ())
  in
  (* Initialize Appel data structures from the graph we made for PS7 *)
  let setup_initial graph =
    let allnodes = graph.InterfereGraph.nodes in
    let interfere_edges = graph.InterfereGraph.non_move_edges in
    let rec filter_nodes nodelist =
      match nodelist with
      | [] -> ()
      | hd::tl -> (if is_machine_register hd then precolored := OperandSet.add hd !precolored
        else initial := OperandSet.add hd !initial); filter_nodes tl;
    in
    let add_move_to_movelists (u,v) =
      set_movelist u (TupleSet.add (u,v) (retrieve_movelist u));
      set_movelist v (TupleSet.add (u,v) (retrieve_movelist v))
    in
    worklistMoves := list_to_moveset graph.InterfereGraph.move_edges;
    coalescedMoves := TupleSet.empty;
    constrainedMoves := TupleSet.empty;
    frozenMoves := TupleSet.empty;
    activeMoves := TupleSet.empty;
    initial := OperandSet.empty;
    precolored := OperandSet.empty;
    filter_nodes allnodes;
    simplifyWorklist := OperandSet.empty;
    freezeWorklist := OperandSet.empty;
    spillWorklist := OperandSet.empty;
    spilledNodes := OperandSet.empty;
    coalescedNodes := OperandSet.empty;
    coloredNodes := OperandSet.empty;
    selectStack := [];
    adjSet := TupleSet.empty;
    adjList := [];
    degree := [];
    moveList := [];
    alias := [];
    color := [];
    List.iter (fun (u,v) -> add_edge u v) interfere_edges;
    OperandSet.iter (fun reg -> set_color reg reg) !precolored;
    List.iter add_move_to_movelists graph.InterfereGraph.move_edges;
    make_worklist ()
  in
  let rec main_loop () =
    (* Appel procedures LivenessAnalysis, Build, MakeWorklist *)
    let graph = build_interfere_graph !current_func in
    setup_initial graph;
    let rec inner_loop () =
      let _ = if OperandSet.is_empty !simplifyWorklist = false then simplify ()
        else if TupleSet.is_empty !worklistMoves = false then coalesce ()
        else if OperandSet.is_empty !freezeWorklist = false then freeze ()
        else if OperandSet.is_empty !spillWorklist = false then select_spill !current_func
      in
      (if (((OperandSet.is_empty !simplifyWorklist) && 
	       (TupleSet.is_empty !worklistMoves) &&
	       (OperandSet.is_empty !freezeWorklist) &&
	       (OperandSet.is_empty !spillWorklist)) = false) then inner_loop ())
    in
    inner_loop ();
    assign_colors ();
    if OperandSet.is_empty !spilledNodes = false then (rewrite_func (); main_loop ());
    ()
  in
  main_loop ();
  (* now need to go through and modify current_func to replace vars with their colors *)
  let to_color_func = !current_func in
  let color_op op =
    match op with
      Var _ -> retrieve_color op
    | _ -> op
  in
  let color_inst i =
    match i with
      Label _ -> i
    | Move (op1, op2) -> Move (color_op op1, color_op op2)
    | Arith (op1, op2, aop, op3) -> Arith (color_op op1, color_op op2, aop, color_op op3)
    | Load (op1, op2, x) -> Load (color_op op1, color_op op2, x)
    | Store (op1, x, op2) -> Store (color_op op1, x, color_op op2)
    | Call op -> Call (color_op op)
    | Jump _ -> i
    | If (op1, c, op2, l1, l2) -> If (color_op op1, c, color_op op2, l1, l2)
    | Return -> i
  in
  let rec color_insts b =
    match b with
      [] -> []
    | hd::tl -> (color_inst hd)::(color_insts tl) in
  let rec color_blocks bs =
    match bs with
      [] -> []
    | hd::tl -> (color_insts hd)::(color_blocks tl) in
  color_blocks to_color_func

(* mangle function names to prevent conflicts with mips instructions *)
(* but don't mangle internal labels like .L0 *)
let mangle x = if x.[0] = '.' then x else "_sdej_" ^ x

(* helpers for instruction translation *)
let to_mips_reg (op : operand) : Mips.reg =
  match op with
  | Reg(r) -> r
  | _ -> raise FatalError

let to_mips_label (op : operand) : Mips.label =
  match op with
  | Lab(a) -> (mangle a)
  | _ -> raise FatalError

let to_mips_op (op : operand) : Mips.operand =
  match op with
  | Reg(r) -> Mips.Reg(r)
  | Int(i) -> Mips.Immed(Int32.of_int i)
  | _ -> raise FatalError

(* translate a single CFG inst into one or more Mips insts *)
let cfgi2mipsi (i:inst) : Mips.inst list =
  match i with
    Label lbl -> [Mips.Label (mangle lbl)]
  | Move(o1,o2) ->
    (if o1 <> o2 then
        (match (o1,o2) with
        | Reg(r1), Reg(r2) -> [Mips.Add(r1,r2,Mips.Immed(0l))]
        | Reg(r1), Int(i) -> [Mips.Li(r1,(Int32.of_int i))]
        | _ -> raise IllegalCFG) 
     else [])
  | Arith(o1,o2,a,o3) -> 
    let get_operation_inst (r1 : Mips.reg) (r2 : Mips.reg) (dest : Mips.reg) : Mips.inst =
      match a with
      | Plus -> Mips.Add(dest,r1,Mips.Reg(r2)) (* this takes an operand .. *)
      | Minus -> Mips.Sub(dest, r1, r2)
      | Times -> Mips.Mul(dest, r1, r2)
      | Div -> Mips.Div(dest, r1, r2)
    in
    let o1reg = to_mips_reg o1 in
    (match (o2,o3) with
    | Reg(r1), Reg(r2) -> [(get_operation_inst r1 r2 o1reg)]
    | Reg(r), Int(i) -> [Mips.Li(Mips.R3, (Int32.of_int i)); (get_operation_inst r Mips.R3 o1reg)]
    | Int(i), Reg(r) -> [Mips.Li(Mips.R3, (Int32.of_int i)); (get_operation_inst Mips.R3 r o1reg)]
    | Int(i1), Int(i2) -> 
      (* we can optimize this! *)
      let calc =
        (match a with
        | Plus -> i1 + i2
        | Minus -> i1 - i2
        | Times -> i1 * i2
        | Div -> i1 / i2) (* don't worry about div by zero - if both operands are constants we might as well raise a compile time error if the second is zero *)
      in [Mips.Li((to_mips_reg o1), (Int32.of_int calc))]
    | _ -> raise IllegalCFG)
  | Load(o1,o2,i) ->
    (match (o1, o2) with
      Reg r1, Reg r2 -> [Mips.Lw((to_mips_reg o1),(to_mips_reg o2),(Int32.of_int i))]
    | _ -> raise IllegalCFG)
  | Store(o1,i,o2) ->
    (match (o1, o2) with
      Reg r1, Reg r2 -> [Mips.Sw((to_mips_reg o2),(to_mips_reg o1),(Int32.of_int i))]
    | Reg r1, Int x -> [Mips.Li(Mips.R3, (Int32.of_int x)); Mips.Sw(Mips.R3, to_mips_reg o1, Int32.of_int i)]
    | _ -> raise IllegalCFG)
  | Call foo ->
    (match foo with
      Lab _ -> [Mips.Jal (to_mips_label foo)]
    | Reg r1 -> [Mips.Jalr(r1, Mips.R31)]
    | _ -> raise IllegalCFG)
  | Jump lbl -> [Mips.J (mangle lbl)]
  | If(o1,co1,o2,l1,l2) -> 
    let get_branch_inst (r1 : Mips.reg) (r2 : Mips.reg) : Mips.inst =
      (match co1 with
      | Eq ->  Mips.Beq(r1,r2,mangle l1)
      | Neq -> Mips.Bne(r1,r2,mangle l1)
      | Lt ->  Mips.Blt(r1,r2,mangle l1)
      | Lte -> Mips.Ble(r1,r2,mangle l1)
      | Gt ->  Mips.Bgt(r1,r2,mangle l1)
      | Gte -> Mips.Bge(r1,r2,mangle l1)
      )
    in
    (match (o1, o2) with
    | Reg(r1), Reg(r2) -> [(get_branch_inst r1 r2); Mips.J(mangle l2)]
    | Reg(r), Int(i) -> [Mips.Li(Mips.R3, (Int32.of_int i));(get_branch_inst r Mips.R3);Mips.J(mangle l2)]
    | Int(i), Reg(r) -> [Mips.Li(Mips.R3, (Int32.of_int i));(get_branch_inst Mips.R3 r);Mips.J(mangle l2)]
    | Int(i1), Int(i2) ->
      let calc =
        (* we can optimize this! *)
        (match co1 with 
        | Eq -> if i1 = i2 then Mips.J(l1) else Mips.J(l2)
        | Neq ->if i1 <>i2 then Mips.J(l1) else Mips.J(l2)
        | Lt -> if i1 < i2 then Mips.J(l1) else Mips.J(l2)
        | Lte ->if i1 <=i2 then Mips.J(l1) else Mips.J(l2)
        | Gt -> if i1 > i2 then Mips.J(l1) else Mips.J(l2)
        | Gte ->if i1 >=i2 then Mips.J(l1) else Mips.J(l2)
        )
      in [calc]
    | _ -> raise IllegalCFG
    )
  | Return -> [Mips.Jr Mips.R31]

(* Finally, translate the output of reg_alloc to Mips instructions *)
let cfg_to_mips (f : func) : Mips.inst list = 
  let insts = List.flatten f in
  let rec cfg2mips_loop (instructions:inst list) : Mips.inst list =
    (match instructions with
      [] -> []
    | hd::tl -> cfgi2mipsi hd @ cfg2mips_loop tl)
  in
  cfg2mips_loop insts

let compile_func (f:C.func) : Mips.inst list =
  let cfg = fn2blocks f in
  cfg_to_mips (reg_alloc cfg)

type result = { code : Mips.inst list;
                data : Mips.label list }

let compile_prog (prog:C.func list) : result (*Mips.inst list*) =
  let rec compile_code (p:C.func list) : Mips.inst list =
    match p with
    | [] -> []
    | hd::tl ->
        compile_func hd @ compile_code tl
  in
  {code=(Mips.Label "main" :: (Mips.J (mangle "main")) :: compile_code prog); data=[] }

let result2string (res : result) : string =
  let code = res.code in
  let data = res.data in
  let strs = List.map (fun x -> (Mips.inst2string x) ^ "\n") code in
  let vaR8decl x = x ^ ":\t.word 0\n" in
  "\t.text\n" ^
  "\t.align\t2\n" ^
  "\t.globl main\n" ^
  (String.concat "" strs) ^
  "\n\n" ^
  "\t.data\n" ^
  "\t.align 0\n"^
  (String.concat "" (List.map vaR8decl data)) ^
  "\n"

(*******************************************************************)
(* Command-Line Interface for printing CFG. You probably will not 
    need to modify this for PS7, but will definitely need to for 
    PS8. Feel free to add additional command-line options as you
    see fit (e.g. -printmips, -evalmips, -printcfg, etc...). 
    Please make sure to document any changes you make.
*)

let usage_string = "usage: " ^ Sys.argv.(0) ^ " [option] [file-to-parse]\nfor option, choose exactly one of:" ^
  " -pig -pcfg -pigd -pcolor -pm\n" ^
  "-pig => print interference graph\n" ^
  "-pcfg => print control flow graph representation\n" ^
  "-pigd => print interference graph with live-in sets next to instructions as debug info\n" ^
  "-pcolor => print final control flow graph representation after register allocation\n" ^
  "-pm => print compiled MIPS\n"

let parse_file() =
  let argv = Sys.argv in
  let _ = 
    if Array.length argv != 3
    then (prerr_string usage_string;
    exit 1) in
  let ch = open_in argv.(2) in
  let option = argv.(1) in
  (Cish_parse.program Cish_lex.lexer (Lexing.from_channel ch), option)

let parse_stdin() = 
  Cish_parse.program Cish_lex.lexer (Lexing.from_channel stdin)

let print_interference_graph (():unit) (f : C.func) : unit =
  let graph = build_interfere_graph (fn2blocks f) in
  Printf.printf "%s\n%s\n\n" (C.fn2string f) (str_of_interfere_graph graph)

let print_cfg () (f:C.func) : unit =
  Printf.printf "%s\n%s\n\n" (C.fn2string f) (fun2string (fn2blocks f))

let print_colored_cfg () (f:C.func) : unit =
  Printf.printf "%s\n%s\n\n" (C.fn2string f) (fun2string (reg_alloc (fn2blocks f)))

let _ =
  let cish_prog, option = parse_file() in
  if option = "-pig" then List.fold_left print_interference_graph () cish_prog
  else if option = "-pcfg" then List.fold_left print_cfg () cish_prog
  else if option = "-pigd" then (pig_debug := true; List.fold_left print_interference_graph () cish_prog)
  else if option = "-pcolor" then List.fold_left print_colored_cfg () cish_prog
  else if option = "-pm" then print_string (result2string (compile_prog cish_prog))
  else (prerr_string usage_string; exit 1)
