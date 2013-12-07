(* Saagar Deshpande and Emmet Jao *)
open Cfg_ast
module C = Cish_ast
exception Implement_Me
exception FatalError

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
    if (edge_mem g v1 v2 move_related) || (node_mem g v1 = false) || (node_mem g v2 = false) then g else
    (let (vv1, vv2) = if v1 < v2 then (v1, v2) else (v2, v1) in
     if move_related then { nodes = g.nodes; move_edges = (vv1, vv2) :: g.move_edges; non_move_edges = g.non_move_edges }
     else { nodes = g.nodes; move_edges = g.move_edges; non_move_edges = (vv1, vv2) :: g.non_move_edges })

  let rec count_node_in_edges edges node =
    match edges with
    | [] -> 0
    | (a, b)::tl -> if (a = node) || (b = node) then (count_node_in_edges tl node) + 1
                    else (count_node_in_edges tl node)

  let get_nonmove_degree g v1 =
    if (node_mem g v1) then count_node_in_edges g.non_move_edges v1
    else 0

  let get_move_degree g v1 =
    if (node_mem g v1) then count_node_in_edges g.move_edges v1
    else 0


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
  let opset = OperandSet.empty in
  match inst with
  | Label _ | Jump _ | Return -> opset
  | Move (o1, o2) -> OperandSet.add o2 opset
  | Arith (o1, o2, _, o3) -> OperandSet.add o2 (OperandSet.add o3 opset)
  | Load (o1, o2, _) -> OperandSet.add o2 opset
  | Store (o1, _, o2) -> OperandSet.add o1 (OperandSet.add o2 opset)
  | Call op -> OperandSet.add op opset
  | If (o1, _, o2, _, _) -> OperandSet.add o1 (OperandSet.add o2 opset)

(* Kill for instructions. Returns operand set containing all Kills required for
 * one instruction *)
let inst_kill inst : OperandSet.t =
  let killset = OperandSet.empty in
  match inst with
  | Move (o1, _)
  | Arith (o1, _, _, _) 
  | Load (o1, _, _) -> OperandSet.add o1 killset
  | _ -> killset

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

(* given a function (i.e., list of basic blocks), construct the
 * interference graph for that function.  This will require that
 * you build a dataflow analysis for calculating what set of variables
 * are live-in and live-out for each program point. *)
let build_interfere_graph (f : func) : interfere_graph =
  (* flatten the blocks into a pure list of instructions. we will do livein and
   * liveout for each instruction *)
  (*print_string (fun2string f);*)
  let insts = List.flatten f in
  let rec live_in_init (instructions : inst list) : OperandSet.t list =
    match instructions with
      [] -> []
    | hd :: tl -> inst_gen hd :: live_in_init tl in
  let rec live_out_init (instructions : inst list) : OperandSet.t list =
    match instructions with
      [] -> []
    | hd :: tl -> OperandSet.empty :: live_out_init tl in
  (* all live in sets are Gen(instruction) at start *)
  let live_in_full = live_in_init insts in
  (* all live out sets are empty at start.*)
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
	  else (let new_in = OperandSet.union (inst_gen hd) (OperandSet.diff out (inst_kill hd)) in
		change (update_lives tl tl2 tl3 (live_in_rest @ [new_in], live_out_rest @ [out]))))) in
  let rec loop live_in live_out =
    if (!changed) then
      (let _ = changed := false in
       let new_live_in, new_live_out = update_lives insts live_in live_out ([], []) in
       loop new_live_in new_live_out)
    else (live_in, live_out) in
  let (final_live_in, final_live_out) = changed := true; loop live_in_full live_out_full in
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
      | hd::tl -> add_edges_for_item item tl (InterfereGraph.add_edge graph item hd false)) in 
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
                      [Mips.R8;Mips.R9;Mips.R10;Mips.R11;Mips.R12;Mips.R13;Mips.R14;Mips.R15;Mips.R24;Mips.R25] in
    let rec add_rest_caller_saves item caller_saves graph : interfere_graph =
      (match caller_saves with
      | [] -> graph
      | hd::tl -> add_rest_caller_saves item tl (InterfereGraph.add_edge graph item hd false)) in 
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
      | hd::tl -> add_rest_edges item tl (InterfereGraph.add_edge graph item hd false)) in
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

(* helper for adjList[n] *)
let rec get_edge_set edges node : OperandSet.t =
  match edges with
  | [] -> OperandSet.empty
  | (a,b)::tl -> 
      if (a = node) then OperandSet.add b (get_edge_set tl node)
      else if (b = node) then OperandSet.add a (get_edge_set tl node)
      else get_edge_set tl node

(* adjList[n] should return set of nodes that interfere with n *)
let get_adj_nodes graph node : OperandSet.t =
  get_edge_set graph.InterfereGraph.non_move_edges node
 
(* moveList[n] should return set of moves involving n as a source or destination *)
let get_node_moves graph node : TupleSet.t =
  let move_related_edges = graph.InterfereGraph.move_edges in
  let rec get_moves_set mr_edges node : TupleSet.t =
    match mr_edges with
    | [] -> TupleSet.empty
    | (a,b)::tl ->
        if (a = node) || (b = node) then TupleSet.add (a, b) (get_moves_set tl node)
        else get_moves_set tl node
  in
  get_moves_set move_related_edges node 

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
  ref_list := deref_list

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
  let machine_regs : operand list = [Reg Mips.R0; Reg Mips.R1; Reg Mips.R26; 
                                    Reg Mips.R27; Reg Mips.R29; Reg Mips.R30; Reg Mips.R31] in
  (* Number of registers, used to distinguish low- from high-degree nodes *)
  let k_reg = 32 - List.length machine_regs in
  let is_machine_register oper = List.mem oper machine_regs in

  let precolored = ref OperandSet.empty in
  let initial = ref OperandSet.empty in
  let simplifyWorklist = ref OperandSet.empty in
  let freezeWorklist = ref OperandSet.empty in
  let spillWorklist = ref OperandSet.empty in
  let spilledNodes = ref OperandSet.empty in
  let coalescedNodes = ref OperandSet.empty in
  let coloredNodes = ref OperandSet.empty in
  let selectStack : operand list ref = ref [] in

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

  (* Adjacent(n): should return adjList[n] - selectStack - coalescedNodes *)
  let adjacent node : OperandSet.t =
    (*let adjList_n = get_adj_nodes graph node in
    let selectStackSet = list_to_operandset !selectStack in    
    let onion = OperandSet.union selectStackSet !coalescedNodes in
    OperandSet.diff adjList_n onion*)
    let deref_adjList = !adjList in
    let rec get_nth_list node deref_list : OperandSet.t =
      match deref_list with
      | [] -> raise FatalError
      | (op,set)::tl -> if op = node then set else get_nth_list node tl
    in
    let selectStackSet = list_to_operandset !selectStack in
    let onion = OperandSet.union selectStackSet !coalescedNodes in
    let adjList_n_set = get_nth_list node deref_adjList in
    OperandSet.diff adjList_n_set onion
  in
  (* NodeMoves(n): get moveList[n] intersect with union of activeMoves and worklistMoves *)
  let node_moves node : TupleSet.t =
    let rec get_nth_list node deref_list : TupleSet.t =
      match deref_list with
      | [] -> raise FatalError
      | (op,tupset)::tl -> if op = node then tupset else get_nth_list node tl
    in
    let deref_movelist = !moveList in
    let move_nth_list = get_nth_list node deref_movelist in
    let onion = TupleSet.union !activeMoves !worklistMoves in
    TupleSet.inter move_nth_list onion
  in
  (* MoveRelated(n) *)
  let move_related node : bool =
    let tupset = node_moves node in
    if TupleSet.is_empty tupset then false else true
  in
  let setup_initial graph = 
    let allnodes = graph.InterfereGraph.nodes in
    let rec filter_nodes nodelist =
      match nodelist with
      | [] -> ()
      | hd::tl -> (if is_machine_register hd then precolored := OperandSet.add hd !precolored
        else initial := OperandSet.add hd !initial); filter_nodes tl;
    in 
    filter_nodes allnodes in
  let rec make_worklist graph =
    (match (OperandSet.elements !initial) with
      [] -> ()
    | hd::tl ->
      (initial := OperandSet.remove hd !initial;
       let hd_deg = InterfereGraph.get_nonmove_degree graph hd in
       if hd_deg >= k_reg then spillWorklist := OperandSet.add hd !spillWorklist
       else if (InterfereGraph.get_move_degree graph hd) > 0 then freezeWorklist := OperandSet.add hd !freezeWorklist
       else simplifyWorklist := OperandSet.add hd !simplifyWorklist);
      make_worklist graph)
  in
  (* EnableMoves(n) *)
  let enable_moves (nodes : OperandSet.t) =
    let inner_iterator single_node =
      (* inner loop updater *)
      let rec update_moves tuplist =
        match tuplist with
        | [] -> ()
        | hd::tl -> (if TupleSet.exists (fun x -> x = hd) !activeMoves 
                    then activeMoves := TupleSet.remove hd !activeMoves;
                        worklistMoves := TupleSet.add hd !worklistMoves);
                    update_moves tl
      in
      update_moves (TupleSet.elements (node_moves single_node))
    in
    (* outer loop *)
    let rec nodes_iterator nodelist =
      match nodelist with
      | [] -> ()
      | hd::tl -> inner_iterator hd; nodes_iterator tl;
    in
    nodes_iterator (OperandSet.elements nodes)
  in
  (* helper to get degree of a node *)
  let retrieve_degree node : int =
    let rec retrieve_helper n nodelist : int =
      match nodelist with
      | [] -> raise FatalError
      | (hd,count)::tl -> if hd = n then count else retrieve_helper n tl
    in
    retrieve_helper node !degree
  in
  (* DecrementDegree(m) *)
  let decrement_degree (node : operand) =
    (* SHOULD DELETE - get the degree *)
(*    let rec get_degree n nodelist : int =
      match nodelist with
      | [] -> raise FatalError
      | (hd,count)::tl -> if hd = n then count else get_degree n tl
    in*)
(*     let m_deg = get_degree node deref_degree in *)
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
      let abunchofnodes = OperandSet.add node (adjacent node) in 
      enable_moves abunchofnodes;
      spillWorklist := OperandSet.remove node !spillWorklist;
      if (move_related node) then freezeWorklist := OperandSet.add node !freezeWorklist
      else simplifyWorklist := OperandSet.add node !simplifyWorklist;
    else ()
  in
  (* SIMPLIFY *)
  let simplify () = 
    let node = OperandSet.choose !simplifyWorklist in 
    (* remove node from the worklist *)
    simplifyWorklist := OperandSet.remove node !simplifyWorklist;
    (* push the node into selectStack *)
    let _ = list_push selectStack node in
    let neighbors = adjacent node in
    (* get neighbor nodes decremented *)
    let rec dec_degree_loop nodelist =
      match nodelist with
      | [] -> ()
      | hd::tl -> let _ = decrement_degree hd in dec_degree_loop tl
    in
    (* OLD CODE - should probably delete *)
    (*let neighbors = adjacent graph node in
    let rec simplify_helper nodelist old_graph : InterfereGraph.t =
      match nodelist with
      | [] -> old_graph
      | hd::tl -> simplify_helper tl (decrement_degree graph hd)
    in*)
    ()
  in
  (* GetAlias(n) *)
  let get_alias node = raise Implement_Me in
  (* AddWorkList(u) *)
  let add_worklist node = 
    if ((OperandSet.for_all (fun x -> node = x) !precolored) = false && (move_related node) = false && (retrieve_degree node) < k_reg) then
      freezeWorklist := OperandSet.remove node !freezeWorklist;
      simplifyWorklist := OperandSet.add node !simplifyWorklist;
  in
  (* COALESCE *)
  let coalesce () =
    let m = TupleSet.choose !worklistMoves in
    let (x, y) = m in
    let x_alias = get_alias x in
    let y_alias = get_alias y in
    let (u, v) = (if OperandSet.mem y_alias !precolored then (y_alias, x_alias) else (x_alias, y_alias)) in
    worklistMoves := TupleSet.remove m !worklistMoves;
    if (u = v)
    then (coalescedMoves := TupleSet.add m !coalescedMoves; (add_worklist u))
    (* TODO - fix this ocaml block. i don't know why it doesn't compile :( *)
    (* TODO - need ordering invariant for edges *)
    else if ((OperandSet.mem v !precolored) || (TupleSet.mem (u, v) !adjSet))
    then
      (constrainedMoves := TupleSet.add m !constrainedMoves;
       add_worklist u;
       add_worklist v);
    raise Implement_Me
  in
  let freeze () = raise Implement_Me in
  let select_spill () = raise Implement_Me in
  let assign_colors () = raise Implement_Me in
  let rewrite_program () = raise Implement_Me in

  let rec main_loop () =
    (* Appel procedures LivenessAnalysis and Build *)
    let graph = build_interfere_graph !current_func in
    worklistMoves := list_to_moveset graph.InterfereGraph.move_edges;
    coalescedMoves := TupleSet.empty;
    constrainedMoves := TupleSet.empty;
    frozenMoves := TupleSet.empty;
    activeMoves := TupleSet.empty;
    (* setup node worklists *)
    setup_initial graph;
    simplifyWorklist := OperandSet.empty;
    freezeWorklist := OperandSet.empty;
    spillWorklist := OperandSet.empty;
    spilledNodes := OperandSet.empty;
    coalescedNodes := OperandSet.empty;
    coloredNodes := OperandSet.empty;
    selectStack := [];
    make_worklist graph;
    let rec inner_loop () =
      let _ = if OperandSet.is_empty !simplifyWorklist = false then simplify ()
        else if TupleSet.is_empty !worklistMoves = false then coalesce ()
        else if OperandSet.is_empty !freezeWorklist = false then freeze ()
        else if OperandSet.is_empty !spillWorklist = false then select_spill ()
      in
      (if (((OperandSet.is_empty !simplifyWorklist) && 
	       (TupleSet.is_empty !worklistMoves) &&
	       (OperandSet.is_empty !freezeWorklist) &&
	       (OperandSet.is_empty !spillWorklist)) = false) then inner_loop ())
    in
    inner_loop ();
    assign_colors ();
    if OperandSet.is_empty !spilledNodes = false then (rewrite_program (); main_loop ());
    ()
  in
  main_loop ();
  !current_func

(* Finally, translate the output of reg_alloc to Mips instructions *)
let cfg_to_mips (f : func) : Mips.inst list = 
    raise Implement_Me

let compile_func (f:C.func) : Mips.inst list =
  let cfg = fn2blocks f in
  cfg_to_mips (reg_alloc cfg)

let compile_prog (prog:C.func list) : Mips.inst list =
  raise Implement_Me

let result2string (res:Mips.inst list) : string =
  raise Implement_Me


(*******************************************************************)
(* Command-Line Interface for printing CFG. You probably will not 
    need to modify this for PS7, but will definitely need to for 
    PS8. Feel free to add additional command-line options as you
    see fit (e.g. -printmips, -evalmips, -printcfg, etc...). 
    Please make sure to document any changes you make.
*)

let usage_string = "usage: " ^ Sys.argv.(0) ^ " [option] [file-to-parse]\nfor option, choose exactly one of:" ^
  " -pig -pm -pcfg\n" ^
  "-pig => print interference graph\n" ^
  "-pm => print compiled MIPS\n" ^
  "-pcfg => print control flow graph representation\n"

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

let _ =
  let cish_prog, option = parse_file() in
  if option = "-pig" then List.fold_left print_interference_graph () cish_prog
  else if option = "-pm" then print_string (result2string (compile_prog cish_prog))
  else if option = "-pcfg" then List.fold_left print_cfg () cish_prog
  else (prerr_string usage_string; exit 1)
