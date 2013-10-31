open Mlish_ast

exception TypeError
let type_error(s:string) = (print_string s; raise TypeError)

let extend (e:(var*tipe_scheme) list) (x:var) (s:tipe_scheme) : (var*tipe_scheme) list = raise TypeError

let lookup (e:(var*tipe_scheme) list) (x:var) : tipe_scheme = raise TypeError

let guess () : tipe = raise TypeError

let unify (t1:tipe) (t2:tipe) : bool = raise TypeError

let instantiate (s:tipe_scheme) : tipe = raise TypeError

let generalize (e:(var*tipe_scheme) list) (t:tipe) : tipe_scheme = raise TypeError

let rec tc (env:(var*tipe_scheme) list) ((e,_):exp) : tipe =
  match e with
    Let (x, e1, e2) -> let s = generalize env (tc env e1) in tc (extend env x s) e2
  | Var x -> instantiate (lookup env x)
  | Fn (x, e1) -> let g = guess () in Fn_t (g, tc (extend env x (Forall ([], g))) e1)
  | App (e1, e2) ->
    let (t1, t2, t) = (tc env e1, tc env e2, guess ()) in
    if unify t1 (Fn_t (t2, t)) then t else type_error "Wrong argument type"
  | _ -> raise TypeError

let type_check_exp (e:Mlish_ast.exp) : tipe = raise TypeError
