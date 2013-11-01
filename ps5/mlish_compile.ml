(* Saagar Deshpande and Emmet Jao *)
module ML = Mlish_ast
module S = Scish_ast

exception ImplementMe
exception MlishCompileError
let compile_error(s:string) = (print_string s; raise MlishCompileError)

let rec compile_exp_rec ((e,_):ML.exp) : S.exp = 
  let compile_binop op e1 e2 =
    let e1_c = compile_exp_rec e1 in
    let e2_c = compile_exp_rec e2 in
    S.PrimApp(op, [e1_c; e2_c])
  in
  match e with
  | ML.Var(v) -> S.Var(v)
  | ML.PrimApp(p, xs) -> 
    (match p, xs with
    | ML.Int i, [] -> S.Int i
    | ML.Bool b, [] -> if b then (S.Int 1) else (S.Int 0)
    | ML.Unit, [] -> S.Int(1)
    | ML.Plus, [e1;e2] -> compile_binop S.Plus e1 e2
    | ML.Minus, [e1;e2] -> compile_binop S.Minus e1 e2
    | ML.Times, [e1;e2] -> compile_binop S.Times e1 e2
    | ML.Div, [e1;e2] -> compile_binop S.Div e1 e2
    | ML.Eq, [e1;e2] -> compile_binop S.Eq e1 e2
    | ML.Lt, [e1;e2] -> compile_binop S.Lt e1 e2
    | ML.Pair, [e1;e2] -> compile_binop S.Cons e1 e2
    | ML.Fst, [e1] -> S.PrimApp(S.Fst, [compile_exp_rec e1])
    | ML.Snd, [e1] -> S.PrimApp(S.Snd, [compile_exp_rec e1])
    | ML.Nil, [] -> S.Int 0
    | ML.Cons, [e1;e2] -> compile_binop S.Cons e1 e2
    | ML.IsNil, [e1] -> S.If (compile_exp_rec e1, S.Int 0, S.Int 1)
    | ML.Hd, [e1] -> S.PrimApp(S.Fst, [compile_exp_rec e1])
    | ML.Tl, [e1] -> S.PrimApp(S.Snd, [compile_exp_rec e1])
    | ML.Int _, _
    | ML.Bool _, _
    | ML.Unit, _
    | ML.Plus, _
    | ML.Minus, _
    | ML.Times, _
    | ML.Div, _
    | ML.Eq, _
    | ML.Lt, _
    | ML.Pair, _
    | ML.Fst, _
    | ML.Snd, _
    | ML.Nil, _
    | ML.Cons, _
    | ML.IsNil, _
    | ML.Hd, _
    | ML.Tl, _ -> compile_error "Wrong number of arguments")
  | ML.Fn(v, e1) -> S.Lambda(v, (compile_exp_rec e1))
  | ML.App(e1, e2) -> S.App((compile_exp_rec e1), (compile_exp_rec e2))
  | ML.If(e1, e2, e3) -> S.If((compile_exp_rec e1), 
                              (compile_exp_rec e2),
                              (compile_exp_rec e3))
  | ML.Let(v, e1, e2) -> S.sLet v (compile_exp_rec e1) (compile_exp_rec e2) 

let rec compile_exp ((e,p):ML.exp) : S.exp =
  compile_exp_rec (e,p)
