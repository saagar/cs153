(* Saagar Deshpande and Emmet Jao *)
(* TODO:  your job is to map ScishAst expressions to CishAst functions. 
   The file sample_input.scish shows a sample Scish expression and the
   file sample_output.cish shows the output I get from my compiler.
   You will want to do your own test cases...
 *)

exception Unimplemented

exception Error
let error s = (print_string s; print_string "\n"; raise Error)

exception UnboundVariable

module Varmap =
struct
  type varmap = Cish_ast.var -> int
  exception NotFound
  let empty_varmap () = fun y -> raise NotFound
  let insert_var vm x i = fun y -> if (y = x) then i else vm y
  let lookup_var vm x = vm x
  let member vm x = (try (lookup_var vm x; true) with NotFound -> false)
end

(*let indices : (Cish_ast.var -> int) ref = ref (fun y -> raise UnboundVariable)
let *)

(* generate fresh labels *)
let label_counter = ref 0
let new_int() = (label_counter := (!label_counter) + 1; !label_counter)
let new_label() = "t" ^ (string_of_int (new_int()))

let function_bodies : Cish_ast.func list ref = ref []

let rec generate_function (x:Scish_ast.var) (e:Scish_ast.exp) =
  let evalexp = compile_helper e in
  let funcbody = (Cish_ast.Let("result", (Cish_ast.Int 0, 0), (Cish_ast.Seq(evalexp, (Cish_ast.Return((Cish_ast.Var("result"), 0)), 0)), 0)), 0) in
  let name = new_label () in
  let generatedfunc = { Cish_ast.name=name; Cish_ast.args=["dynenv"]; Cish_ast.body=funcbody; Cish_ast.pos=0 } in
  function_bodies := (Cish_ast.Fn generatedfunc) :: (!function_bodies); name

and compile_helper (e:Scish_ast.exp) : Cish_ast.stmt =
  let plus4 (x:Cish_ast.var) : Cish_ast.exp = (Cish_ast.Binop((Cish_ast.Var(x), 0), Cish_ast.Plus, (Cish_ast.Int(4), 0)), 0) in
  let expstmt (expression:Cish_ast.exp) : Cish_ast.stmt = (Cish_ast.Exp(expression), 0) in
  let rec stmtconcat (stmts:Cish_ast.stmt list) : Cish_ast.stmt =
    (match stmts with
      [] -> (Cish_ast.skip, 0)
    | hd::[] -> hd
    | hd::tl -> (Cish_ast.Seq(hd, stmtconcat tl), 0)) in
  match e with
    Scish_ast.App (e1, e2) ->
      let t0 = new_label () in
      let t1 = new_label () in
      let t2 = new_label () in
      let evalclosure = compile_helper e1 in
      let storefunc = (Cish_ast.Assign(t0, (Cish_ast.Load((Cish_ast.Var("result"), 0)), 0)), 0) in
      let storeenv = (Cish_ast.Assign(t1, (Cish_ast.Load(plus4 "result"), 0)), 0) in
      let evalarg = compile_helper e2 in
      let storearg = (Cish_ast.Assign(t2, (Cish_ast.Var("result"), 0)), 0) in
      let mlc = (Cish_ast.Assign("result", (Cish_ast.Malloc((Cish_ast.Int 8, 0)), 0)), 0) in
      let newval = (Cish_ast.Store((Cish_ast.Var("result"), 0), (Cish_ast.Var(t2), 0)), 0) in
      let oldenv = (Cish_ast.Store((plus4 "result"), (Cish_ast.Var(t1), 0)), 0) in
      let call = (Cish_ast.Assign("result", (Cish_ast.Call((Cish_ast.Var(t0), 0), [(Cish_ast.Var("result"), 0)]), 0)), 0) in
      let stmts = stmtconcat [evalclosure; expstmt storefunc; expstmt storeenv; evalarg; expstmt storearg; expstmt mlc; expstmt newval; expstmt oldenv; expstmt call] in
      (Cish_ast.Let(t0, (Cish_ast.Int 0, 0), (Cish_ast.Let(t1, (Cish_ast.Int 0, 0), (Cish_ast.Let(t2, (Cish_ast.Int 0, 0), stmts), 0)), 0)), 0)
  | Scish_ast.Lambda (x, e1) ->
    let label = generate_function x e1 in
    let mlc = (Cish_ast.Assign("result", (Cish_ast.Malloc((Cish_ast.Int 8, 0)), 0)), 0) in
    let newval = (Cish_ast.Store((Cish_ast.Var("result"), 0), (Cish_ast.Var(label), 0)), 0) in
    let oldenv = (Cish_ast.Store((plus4 "result"), (Cish_ast.Var("dynenv"), 0)), 0) in
    stmtconcat [expstmt mlc; expstmt newval; expstmt oldenv]

let rec compile_exp (e:Scish_ast.exp) : Cish_ast.program =
(*  match e with
    App (e1, e2) ->
*) raise Unimplemented
