(* Compile Cish AST to MIPS AST *)
(* Saagar Deshpande and Emmet Jao *)
open Mips

exception IMPLEMENT_ME

type result = { code : Mips.inst list;
                data : Mips.label list }

(* generate fresh labels *)
let label_counter = ref 0
let new_int() = (label_counter := (!label_counter) + 1; !label_counter)
let new_label() = "L" ^ (string_of_int (new_int()))

module type VARMAP =
sig
  type varmap
  val empty_varmap : unit -> varmap
  val insert_var : varmap -> Ast.var -> int -> varmap
  val lookup_var : varmap -> Ast.var -> int
  val member : varmap -> Ast.var -> bool
end

module Varmap : VARMAP =
struct
  type varmap = Ast.var -> int
  exception NotFound
  let empty_varmap () = fun y -> raise NotFound
  let insert_var vm x i = fun y -> if (y = x) then i else vm y
  let lookup_var vm x = vm x
  let member vm x = (try (lookup_var vm x; true) with NotFound -> false)
end

(* prefix that will be added to all function names to avoid conflict with MIPS instructions *)
(* this is also used to resolve variable name conflicts (shadowing) *)
let mangle funcname = "_sdej_" ^ funcname

let exp2mips vm ((e,_):Ast.exp) : Mips.inst list =
  raise IMPLEMENT_ME

let rec compile_func_body vm funcname ((body,_):Ast.stmt) : Mips.inst list =
  match body with
    Ast.Exp e -> exp2mips vm e
  | Ast.Seq (s1, s2) -> (compile_func_body vm funcname s1) @ (compile_func_body vm funcname s2)
  | Ast.If (e, s1, s2) ->
    (let else_label = new_label() in
     let end_label = new_label() in
     (exp2mips vm e) @ [Beq(R2, R0, else_label)] @
       (compile_func_body vm funcname s1) @ [J end_label; Label else_label] @
       (compile_func_body vm funcname s2) @ [Label end_label])
  | Ast.While (e, s1) ->
    (let test_label = new_label() in
     let top_label = new_label() in
     [J test_label; Label top_label] @ (compile_func_body vm funcname s1) @
       [Label test_label] @ (exp2mips vm e) @ [Bne(R2, R0, top_label)])
  | Ast.For (e1, e2, e3, s1) ->
    compile_func_body vm funcname (Ast.Seq ((Ast.Exp e1, 0), (Ast.While (e2, (Ast.Seq (s1, (Ast.Exp e3, 0)), 0)), 0)), 0)
  | Ast.Return e -> (exp2mips vm e) @ [J (funcname ^ "epilogue")]
  | _ -> raise IMPLEMENT_ME

(* mangle all occurrences of v in a stmt *)
let rec var_rename ((s,pos):Ast.stmt) v =
  let rec var_rename_exp (e:Ast.exp) =
    let (exp, pos) = e in
    match exp with
      Ast.Assign (x, e1) -> (Ast.Assign((if (x = v) then mangle x else x), var_rename_exp e1), pos)
    | Ast.Int _ -> e
    | Ast.Var x -> if (x = v) then (Ast.Var (mangle x), pos) else e
    | Ast.Binop (e1, op, e2) -> (Ast.Binop (var_rename_exp e1, op, var_rename_exp e2), pos)
    | Ast.Not e -> var_rename_exp e
    | Ast.And (e1, e2) -> (Ast.And (var_rename_exp e1, var_rename_exp e2), pos)
    | Ast.Or (e1, e2) -> (Ast.Or (var_rename_exp e1, var_rename_exp e2), pos)
    | Ast.Call (f, arglist) -> (Ast.Call (f, List.map var_rename_exp arglist), pos) in
  match s with
    Ast.Exp e -> (Ast.Exp(var_rename_exp e), pos)
  | Ast.Seq (s1, s2) -> (Ast.Seq(var_rename s1 v, var_rename s2 v), pos)
  | Ast.If (e, s1, s2) -> (Ast.If(var_rename_exp e, var_rename s1 v, var_rename s2 v), pos)
  | Ast.While (e, s1) -> (Ast.While(var_rename_exp e, var_rename s1 v), pos)
  | Ast.For (e1, e2, e3, s1) -> (Ast.For(var_rename_exp e1, var_rename_exp e2, var_rename_exp e3, var_rename s1 v), pos)
  | Ast.Return e1 -> (Ast.Return(var_rename_exp e1), pos)
  | Ast.Let (x, e, s1) -> (Ast.Let((if (x = v) then mangle v else v), var_rename_exp e, var_rename s1 v), pos)

let compile_func (f:Ast.funcsig) : Mips.inst list =
  let name = mangle f.Ast.name in
  let args = f.Ast.args in
  let body = f.Ast.body in
  (* varmap will hold offsets of args and locals relative to the fp *)
  let vm = Varmap.empty_varmap () in
  let rec map_args args vm offset =
    match args with
      [] -> vm
    | hd::tl -> map_args tl (Varmap.insert_var vm hd offset) (offset + 4) in
  (* put args in the varmap, starting above the saved ra and fp *)
  let vm2 = map_args args vm 4 in
  (* framesize is number of words the stack frame will hold *)
  let framesize = ref 2 in
  (* map_locals resolves variable name shadowing by mangling *)
  let rec map_locals (s:Ast.stmt) vm offset : (Varmap.varmap * int * Ast.stmt) =
    let (body, pos) = s in
    match body with
      Ast.Exp _ -> (vm, offset, s)
    | Ast.Let (v, _, s) -> (framesize := !framesize + 1;
			    if Varmap.member vm v
			    then (map_locals (var_rename s v) (Varmap.insert_var vm (mangle v) offset) (offset - 4))
			    else (map_locals s (Varmap.insert_var vm v offset) (offset - 4)))
    | Ast.For (_, _, _, s) -> map_locals s vm offset
    | Ast.While (_, s) -> map_locals s vm offset
    | Ast.If (e, s1, s2) -> (let (v1, o1, renamed_s1) = map_locals s1 vm offset in
			     let (v2, o2, renamed_s2) = map_locals s2 v1 o1 in
			     (v2, o2, (Ast.If(e, renamed_s1, renamed_s2), pos)))
    | Ast.Seq (s1, s2) -> (let (v1, o1, renamed_s1) = map_locals s1 vm offset in
			     let (v2, o2, renamed_s2) = map_locals s2 v1 o1 in
			     (v2, o2, (Ast.Seq(renamed_s1, renamed_s2), pos)))
    | Ast.Return _ -> (vm, offset, s) in
  (* put locals in the varmap, starting under the saved ra and fp *)
  let (vm3, _, new_body) = map_locals body vm2 (- 8) in
  let prologue = [Label name;
		  Add (R29, R29, Immed (Word32.fromInt (!framesize * (- 4))));
		  Sw (R31, R29, (Word32.fromInt ((!framesize * 4) - 4)));
		  Sw (R30, R29, (Word32.fromInt ((!framesize * 4) - 8)));
		  Add (R30, R29, Immed (Word32.fromInt ((!framesize * 4) - 4)))] in
  let epilogue = [Label (name ^ "epilogue");
		  Lw (R31, R30, (Word32.fromInt 0));
		  Lw (R30, R30, (Word32.fromInt (- 4)));
		  Add (R29, R29, Immed (Word32.fromInt (!framesize * 4)));
		  Jr R31] in
  let func_body = compile_func_body vm3 name new_body in
  prologue @ func_body @ epilogue

let rec compile (p:Ast.program) : result =
    (*raise IMPLEMENT_ME*)
  let rec compile_code (prog:Ast.program) : Mips.inst list =
    match prog with
      [] -> []
    | (Ast.Fn(f))::tl -> compile_func f @ compile_code tl in
  { code=((Mips.J (mangle "main")) :: compile_code p); data=[] }

let result2string (res:result) : string = 
    let code = res.code in
    let data = res.data in
    let strs = List.map (fun x -> (Mips.inst2string x) ^ "\n") code in
    let vaR8decl x = x ^ ":\t.word 0\n" in
    let readfile f =
      let stream = open_in f in
      let size = in_channel_length stream in
      let text = String.create size in
      let _ = really_input stream text 0 size in
		  let _ = close_in stream in 
      text in
	  let debugcode = readfile "print.asm" in
	    "\t.text\n" ^
	    "\t.align\t2\n" ^
	    "\t.globl main\n" ^
	    (String.concat "" strs) ^
	    "\n\n" ^
	    "\t.data\n" ^
	    "\t.align 0\n"^
	    (String.concat "" (List.map vaR8decl data)) ^
	    "\n" ^
	    debugcode
