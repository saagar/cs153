(* Saagar Deshpande and Emmet Jao *)
module ML = Mlish_ast
module S = Scish_ast

exception ImplementMe
exception MlishCompileError
exception TODO

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
      | ML.Unit, [] -> raise TODO (* how do we do this? *)
      | ML.Plus, [e1;e2] -> compile_binop S.Plus e1 e2
      | ML.Minus, [e1;e2] -> compile_binop S.Minus e1 e2
      | ML.Times, [e1;e2] -> compile_binop S.Times e1 e2
      | ML.Div, [e1;e2] -> compile_binop S.Div e1 e2
      | ML.Eq, [e1;e2] -> compile_binop S.Eq e1 e2
      | ML.Lt, [e1;e2] -> compile_binop S.Lt e1 e2
      | ML.Pair, [e1;e2] -> compile_binop S.Cons e1 e2
      | ML.Fst, [e1] -> S.PrimApp(S.Fst, [compile_exp_rec e1])
      | ML.Snd, [e2] -> S.PrimApp(S.Snd, [compile_exp_rec e2])
      (* Wrap 0 with 1. The 2nd item is 1 because IsNil is true (1) *)
      | ML.Nil, [] -> S.PrimApp(S.Cons, [S.Int(0); S.Int(1)])
      | ML.Cons, [e1;e2] -> 
          let pair = compile_binop S.Cons e1 e2 in
          (* wrap our pair in a Cons of pair::0. 
           * the 0 indicates that this is not Nil *)
          S.PrimApp(S.Cons, [pair; S.Int(0)])
      (* get the 2nd item of a wrap and return that *)
      | ML.IsNil, [e1] -> S.PrimApp(S.Snd, [compile_exp_rec e1])
      (* for Hd, get the first of a wrap, then get the fst elt of the pair *)
      | ML.Hd, [e1] -> S.PrimApp(S.Fst,[S.PrimApp(S.Fst, [compile_exp_rec e1])])
      (* for Tl, get the first of a wrap, then get the snd elt of the pair *)
      | ML.Tl, [e1] -> S.PrimApp(S.Snd,[S.PrimApp(S.Snd, [compile_exp_rec e1])])
      | _ -> raise MlishCompileError)
  | ML.Fn(v, e1) -> S.Lambda(v, (compile_exp_rec e1))
  | ML.App(e1, e2) -> S.App((compile_exp_rec e1), (compile_exp_rec e2))
  | ML.If(e1, e2, e3) -> S.If((compile_exp_rec e1), 
                              (compile_exp_rec e2),
                              (compile_exp_rec e3))
  | ML.Let(v, e1, e2) -> S.sLet v (compile_exp_rec e1) (compile_exp_rec e2) 
  


let rec compile_exp ((e,_):ML.exp) : S.exp = raise ImplementMe
