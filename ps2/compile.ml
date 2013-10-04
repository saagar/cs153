(* Compile Fish AST to MIPS AST *)
(* Emmet Jao and Saagar Deshpande *)
open Mips

exception IMPLEMENT_ME

type result = { code : Mips.inst list;
                data : Mips.label list }

(* generate fresh labels *)
let label_counter = ref 0
let new_int() = (label_counter := (!label_counter) + 1; !label_counter)
let new_label() = "L" ^ (string_of_int (new_int()))

(* sets of variables -- Ocaml Set and Set.S *)
module VarSet = Set.Make(struct
                           type t = Ast.var
                           let compare = String.compare
                         end)

(* a table of variables that we need for the code segment *)
let variables : VarSet.t ref = ref (VarSet.empty)

(* generate a fresh temporary variable and store it in the variables set. *)
let rec new_temp() = 
    let t = "T" ^ (string_of_int (new_int())) in
    (* make sure we don't already have a variable with the same name! *)
    if VarSet.mem t (!variables) then new_temp()
    else (variables := VarSet.add t (!variables); t)

(* reset internal state *)
let reset() = (label_counter := 0; variables := VarSet.empty)

(* prefix that will be added to all variable names to avoid conflicts with MIPS instructions *)
let unique_prefix = "_sdej_"

(* wrapper for VarSet.add that prefixes the variable name and adds it to the variables set *)
let mangle_add v : unit =
  let mangled_v = String.concat "" [unique_prefix; v] in
  variables := VarSet.add mangled_v !variables

(* find all of the variables in a program and add them to
 * the set variables *)
let rec collect_vars (p : Ast.program) : unit = 
    (*************************************************************)
    (*raise IMPLEMENT_ME*)
    (*************************************************************)
  let rec collect_vars_exp (e : Ast.exp) : unit =
    let (r, _) = e in
    match r with
      Ast.Int _ -> ()
    | Ast.Var x -> mangle_add x
    | Ast.Binop (e1, _, e2) -> collect_vars_exp e1; collect_vars_exp e2
    | Ast.Not e1 -> collect_vars_exp e1
    | Ast.And (e1, e2) -> collect_vars_exp e1; collect_vars_exp e2
    | Ast.Or (e1, e2) -> collect_vars_exp e1; collect_vars_exp e2
    | Ast.Assign (x, e1) -> mangle_add x; collect_vars_exp e1 in
  let (s, _) = p in
  match s with
  | Ast.Exp e -> collect_vars_exp e
  | Ast.Seq (s1, s2) -> collect_vars s1; collect_vars s2
  | Ast.If (e, s1, s2) -> collect_vars_exp e; collect_vars s1; collect_vars s2
  | Ast.While (e, s1) -> collect_vars_exp e; collect_vars s1
  | Ast.For (e1, e2, e3, s1) -> collect_vars_exp e1; collect_vars_exp e2; collect_vars_exp e3; collect_vars s1
  | Ast.Return e -> collect_vars_exp e

(* compiles a Fish statement down to a list of MIPS instructions.
 * Note that a "Return" is accomplished by placing the resulting
 * value in R2 and then doing a Jr R31.
 *)
let rec compile_stmt ((s,_):Ast.stmt) : inst list = 
    (*************************************************************)
    (*raise IMPLEMENT_ME*)
    (*************************************************************)
  let rec exp2mips ((e,_):Ast.exp) : inst list =
    (match e with
      Ast.Int x -> [Li(R2, Word32.fromInt x)]
    | Ast.Var x -> [La(R2, x); Lw(R2, R2, Int32.zero)]
    | Ast.Binop (e1, b, e2) ->
      (let t = new_temp() in
       (exp2mips e1) @ [La(R1,t); Sw(R2, R1, Int32.zero)] @
         (exp2mips e2) @ [La(R1, t); Lw(R1, R1, Int32.zero)] @
         (match b with
	 | Ast.Plus -> [Add(R2,R2,Reg R1)]
	 | _ -> []
	 )
      )
    | Ast.Not e1 -> []
    | Ast.And (e1, e2) -> []
    | Ast.Or (e1, e2) -> []
    | Ast.Assign (x, e1) -> []) in
  match s with
  | Ast.Exp e -> exp2mips e
  | Ast.Seq (s1, s2) -> (compile_stmt s1) @ (compile_stmt s2)
  | Ast.If (e, s1, s2) ->
    (let else_label = new_label() in
     let end_label = new_label() in
     (exp2mips e) @ [Beq(R2, R0, else_label)] @
       (compile_stmt s1) @ [J end_label; Label else_label] @
       (compile_stmt s2) @ [Label end_label])
  | Ast.While (e, s1) -> []
  | Ast.For (e1, e2, e3, s1) -> []
  | Ast.Return e -> []

(* compiles Fish AST down to MIPS instructions and a list of global vars *)
let compile (p : Ast.program) : result = 
    let _ = reset() in
    let _ = collect_vars(p) in
    let insts = (Label "main") :: (compile_stmt p) in
    { code = insts; data = VarSet.elements (!variables) }

(* converts the output of the compiler to a big string which can be 
 * dumped into a file, assembled, and run within the SPIM simulator
 * (hopefully). *)
let result2string ({code;data}:result) : string = 
    let strs = List.map (fun x -> (Mips.inst2string x) ^ "\n") code in
    let var2decl x = x ^ ":\t.word 0\n" in
    "\t.text\n" ^
    "\t.align\t2\n" ^
    "\t.globl main\n" ^
    (String.concat "" strs) ^
    "\n\n" ^
    "\t.data\n" ^
    "\t.align 0\n"^
    (String.concat "" (List.map var2decl data)) ^
    "\n"

