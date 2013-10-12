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
end

module Varmap : VARMAP =
struct
  type varmap = Ast.var -> int
  exception NotFound
  let empty_varmap () = fun y -> raise NotFound
  let insert_var vm x i = fun y -> if (y = x) then i else vm y
  let lookup_var vm x = vm x
end

(* prefix that will be added to all function names to avoid conflict with MIPS instructions *)
let mangle funcname = "_sdej_" ^ funcname

let compile_func_body vm (body:Ast.stmt) : Mips.inst list =
  [] (* TODO *)

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
  let rec map_locals ((body,_):Ast.stmt) vm offset : (Varmap.varmap * int) =
    match body with
    | Ast.Exp _ -> (vm, offset)
    | Ast.Let (v, _, s) -> framesize := !framesize + 1; map_locals s (Varmap.insert_var vm v offset) (offset - 4)
    | Ast.For (_, _, _, s) -> map_locals s vm offset
    | Ast.While (_, s) -> map_locals s vm offset
    | Ast.If (_, s1, s2) -> (let (v, o) = map_locals s1 vm offset in map_locals s2 v o)
    | Ast.Seq (s1, s2) -> (let (v, o) = map_locals s1 vm offset in map_locals s2 v o)
    | Ast.Return _ -> (vm, offset) in
  (* put locals in the varmap, starting under the saved ra and fp *)
  let vm3 = map_locals body vm2 (- 8) in
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
  let func_body = compile_func_body vm3 body in
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
