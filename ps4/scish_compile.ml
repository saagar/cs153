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
exception InvalidArgCount

(* generate fresh labels *)
let label_counter = ref 0
let new_int() = (label_counter := (!label_counter) + 1; !label_counter)
let new_label() = "t" ^ (string_of_int (new_int()))

let function_bodies : Cish_ast.func list ref = ref []

let rec generate_function (x:Scish_ast.var) (e:Scish_ast.exp) (env:Cish_ast.var -> int) =
  let evalexp = compile_helper e env in
  let funcbody = (Cish_ast.Let("result", (Cish_ast.Int 0, 0), (Cish_ast.Seq(evalexp, (Cish_ast.Return((Cish_ast.Var("result"), 0)), 0)), 0)), 0) in
  let name = new_label () in
  let generatedfunc = { Cish_ast.name=name; Cish_ast.args=["dynenv"]; Cish_ast.body=funcbody; Cish_ast.pos=0 } in
  function_bodies := (Cish_ast.Fn generatedfunc) :: (!function_bodies); name

and compile_helper (e:Scish_ast.exp) (env:Cish_ast.var -> int) : Cish_ast.stmt =
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
      let evalclosure = compile_helper e1 env in
      let storefunc = (Cish_ast.Assign(t0, (Cish_ast.Load((Cish_ast.Var("result"), 0)), 0)), 0) in
      let storeenv = (Cish_ast.Assign(t1, (Cish_ast.Load(plus4 "result"), 0)), 0) in
      let evalarg = compile_helper e2 env in
      let storearg = (Cish_ast.Assign(t2, (Cish_ast.Var("result"), 0)), 0) in
      let mlc = (Cish_ast.Assign("result", (Cish_ast.Malloc((Cish_ast.Int 8, 0)), 0)), 0) in
      let newval = (Cish_ast.Store((Cish_ast.Var("result"), 0), (Cish_ast.Var(t2), 0)), 0) in
      let oldenv = (Cish_ast.Store((plus4 "result"), (Cish_ast.Var(t1), 0)), 0) in
      let call = (Cish_ast.Assign("result", (Cish_ast.Call((Cish_ast.Var(t0), 0), [(Cish_ast.Var("result"), 0)]), 0)), 0) in
      let stmts = stmtconcat [evalclosure; expstmt storefunc; expstmt storeenv; evalarg; expstmt storearg; expstmt mlc; expstmt newval; expstmt oldenv; expstmt call] in
      (Cish_ast.Let(t0, (Cish_ast.Int 0, 0), (Cish_ast.Let(t1, (Cish_ast.Int 0, 0), (Cish_ast.Let(t2, (Cish_ast.Int 0, 0), stmts), 0)), 0)), 0)
  | Scish_ast.Lambda (x, e1) ->
    let new_env (y:Cish_ast.var) = if (x = y) then 0 else (env y) + 1 in
    let label = generate_function x e1 new_env in
    let mlc = (Cish_ast.Assign("result", (Cish_ast.Malloc((Cish_ast.Int 8, 0)), 0)), 0) in
    let newval = (Cish_ast.Store((Cish_ast.Var("result"), 0), (Cish_ast.Var(label), 0)), 0) in
    let oldenv = (Cish_ast.Store((plus4 "result"), (Cish_ast.Var("dynenv"), 0)), 0) in
    stmtconcat [expstmt mlc; expstmt newval; expstmt oldenv]
  | Scish_ast.Var x ->
    let n = env x in
    let rec var_lookup_helper index (accum:Cish_ast.exp) : Cish_ast.exp =
      (if (index <= 0) then (Cish_ast.Load(accum), 0)
      else var_lookup_helper (index - 1) (Cish_ast.Load((Cish_ast.Binop(accum, Cish_ast.Plus, (Cish_ast.Int(4), 0)), 0)), 0)) in
    let var_lookup index = var_lookup_helper index (Cish_ast.Var("dynenv"), 0) in
    (Cish_ast.Exp((Cish_ast.Assign("result", var_lookup n), 0)), 0)
  | Scish_ast.Int i -> expstmt (Cish_ast.Assign("result", (Cish_ast.Int(i), 0)), 0)
  | Scish_ast.PrimApp (op, exps) ->
    (match op with
    | Scish_ast.Plus ->
      (match exps with
      | e1::e2::[] -> 
        let tmp1 = new_label () in
        let evale1 = compile_helper e1 env in
        let storee1 = (Cish_ast.Assign(tmp1, (Cish_ast.Var("result"), 0)), 0) in
        let evale2 = compile_helper e2 env in
        let storee2 = 
          (Cish_ast.Assign("result", (Cish_ast.Binop((Cish_ast.Var(tmp1),0), Cish_ast.Plus,(Cish_ast.Var("result"),0)),0)),0)
        in
        let stmts = stmtconcat [evale1; expstmt storee1; evale2; expstmt storee2] in
	(Cish_ast.Let(tmp1, (Cish_ast.Int 0, 0), stmts), 0)
      | _ -> raise InvalidArgCount)
      (*| Minus ->
	| Times ->
	| Div ->
	| Cons ->
	| Fst ->
	| Snd ->
	| Eq ->
	| Lt ->*)
    | _ -> raise Unimplemented)
  | Scish_ast.If (e1, e2, e3) ->
    let evalcond = compile_helper e1 env in
    let evale2 = compile_helper e2 env in
    let evale3 = compile_helper e3 env in
    let ifstmt = (Cish_ast.If((Cish_ast.Binop((Cish_ast.Var("result"), 0), Cish_ast.Eq, (Cish_ast.Int 0, 0)), 0), evale3, evale2), 0) in
    stmtconcat [evalcond; ifstmt]

let rec compile_exp (e:Scish_ast.exp) : Cish_ast.program =
  let empty_env = fun x -> raise UnboundVariable in
  let evalexp =
    (try (compile_helper e empty_env) with
      UnboundVariable -> error "Unbound variable"
    | InvalidArgCount -> error "Incorrect number of args for primitive operation") in
  let stmts = (Cish_ast.Let("result", (Cish_ast.Int 0, 0), (Cish_ast.Seq(evalexp, (Cish_ast.Return((Cish_ast.Var("result"), 0)), 0)), 0)), 0) in
  let body = (Cish_ast.Let("dynenv", (Cish_ast.Int 0, 0), stmts), 0) in
  let main = Cish_ast.Fn({ Cish_ast.name="main"; Cish_ast.args=([]); Cish_ast.body=body; Cish_ast.pos=0 }) in
  main :: (!function_bodies)
