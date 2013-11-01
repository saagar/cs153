(* Saagar Deshpande and Emmet Jao *)
open Mlish_ast

exception TypeError
exception TODO (* remove including \n *)
let type_error(s:string) = (print_string s; raise TypeError)

let extend (e:(var*tipe_scheme) list) (x:var) (s:tipe_scheme) : (var*tipe_scheme) list = raise TypeError

let lookup (e:(var*tipe_scheme) list) (x:var) : tipe_scheme = raise TypeError

(* Check if a Guess appears in a tipe. If so, there's some recursion to avoid *)
let rec occurs (guess:tipe option ref) (t:tipe) : bool =
  match t with
  | Guess_t(t1) -> guess == t1 ||
    (match !t1 with
    | None -> false
    | Some inner_t -> occurs guess inner_t)
  | Fn_t (t1, t2) -> occurs guess t1 || occurs guess t2
  | Pair_t (t1, t2) -> occurs guess t1 || occurs guess t2
  | List_t t1 -> occurs guess t1
  | _ -> false

(* Generate a new Guess_t *)
let guess () : tipe = Guess_t(ref None)

let rec unify (t1:tipe) (t2:tipe) : bool =
  if (t1 == t2) then true
  else
    match (t1, t2) with
    | Guess_t(t1_guess), _ ->
      (match !t1_guess with
      | None ->
        if (occurs t1_guess t2)
        then type_error "Infinite data type detected"
        else (t1_guess := Some t2; true)
      | Some(t1_g) -> unify t1_g t2)
    (* flip the guess and run again *)
    | _, Guess_t(_) -> unify t2 t1
    (* Functions, Pairs, Lists *)
    | Fn_t(t1a,t1b), Fn_t(t2a,t2b) -> (unify t1a t2a) && (unify t1b t2b)
    | Pair_t(t1a,t1b), Pair_t(t2a,t2b) -> (unify t1a t2a) && (unify t1b t2b)
    | List_t(t1a), List_t(t2a) -> unify t1a t2a
    (* Probably can combine this - do we even get to these cases? *)
    (*| Tvar_t t1a, _ -> true
    | _, Tvar_t t2a -> true
    | Int_t, Int_t -> true
    | Bool_t, Bool_t -> true
    | Unit_t, Unit_t -> true*)
    | _ -> type_error("Unable to unify types")

(* substitute all vars in the tipe t with the guesses provided *)
let rec substitute (lst: (var*tipe) list) (t:tipe) : tipe = 
  match t with
  (* handles guesses. unclear if we have guesses in the tipes *)
  | Guess_t(t1_guess) ->
      (match !t1_guess with
      | None -> Guess_t(t1_guess)
      | Some(t1_g) -> t1_guess := Some (substitute lst t1_g); Guess_t(t1_guess))
  | Fn_t (t1, t2) -> Fn_t ((substitute lst t1), (substitute lst t2) )
  | Pair_t (t1, t2) -> Pair_t ((substitute lst t1), (substitute lst t2))
  | List_t (t1) -> List_t (substitute lst t1)
  | Tvar_t t1 -> (try List.assoc t1 lst with Not_found -> t) (* just return t? *)
  | _ -> t

(* give all tvars a new Guess *)
let instantiate (s:tipe_scheme) : tipe = 
  (* vs is a tvar list, t is the tipe *)
  let Forall(vs, t) = s in
  (* vs_and_ts is a list of tuples (var, tipe) *)
  (* for every tvar in vs, create a tuple containing a tvar and a new guess *)
  let vs_and_ts : (var*tipe) list = List.map (fun a -> (a, guess())) vs
  in
    substitute vs_and_ts t

let generalize (e:(var*tipe_scheme) list) (t:tipe) : tipe_scheme = raise TypeError

let rec tc (env:(var*tipe_scheme) list) ((e,_):exp) : tipe =
  match e with
    Let (x, e1, e2) -> let s = generalize env (tc env e1) in tc (extend env x s) e2
  | Var x -> instantiate (lookup env x)
  | Fn (x, e1) -> let g = guess () in Fn_t (g, tc (extend env x (Forall ([], g))) e1)
  | App (e1, e2) ->
    let (t1, t2, t) = (tc env e1, tc env e2, guess ()) in
    if unify t1 (Fn_t (t2, t)) then t else type_error "Wrong argument type"
  | If (e1, e2, e3) ->
    let (t1, t2, t3) = (tc env e1, tc env e2, tc env e3) in
    if unify t1 Bool_t then
      (if unify t2 t3 then t2 else type_error "Mismatched conditional branch types")
    else type_error "Condition not of bool type"
  | PrimApp (p, es) -> raise TypeError

let type_check_exp (e:Mlish_ast.exp) : tipe = raise TypeError

