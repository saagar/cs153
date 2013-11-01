(* Saagar Deshpande and Emmet Jao *)
open Mlish_ast

exception TypeError
let type_error(s:string) = (print_string s; raise TypeError)

(* generate fresh type variables *)
let label_counter = ref 0
let new_int() = (label_counter := (!label_counter) + 1; !label_counter)
let freshvar() : tvar = "typevar" ^ (string_of_int (new_int()))

(* add the variable x and its tipe_scheme s to the env *)
let extend (e:(var*tipe_scheme) list) (x:var) (s:tipe_scheme) :
  (var*tipe_scheme) list = (x,s)::e

(* return the tipe_scheme for x that is found in the env e *)
let rec lookup (e:(var*tipe_scheme) list) (x:var) : tipe_scheme = 
  match e with
  | (v, t)::tl -> if v = x then t else lookup tl x
  | [] -> type_error ("Unbound variable " ^ x)

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
    | _ -> false
    (*| _ -> type_error("Unable to unify types")*)

(* substitute all vars in the tipe t with the guesses provided *)
let rec substitute (lst: (tvar*tipe) list) (t:tipe) : tipe = 
  match t with
  (* handles guesses. unclear if we have guesses in the tipes *)
  | Guess_t(t1_guess) ->
      (match !t1_guess with
      | None -> Guess_t(t1_guess)
      | Some t1_g -> Guess_t (ref (Some (substitute lst t1_g))))
      (*| Some(t1_g) -> t1_guess := Some (substitute lst t1_g); Guess_t(t1_guess))*)
  | Fn_t (t1, t2) -> Fn_t ((substitute lst t1), (substitute lst t2))
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
  let vs_and_ts : (tvar*tipe) list = List.map (fun a -> (a, guess())) vs
  in
    substitute vs_and_ts t

let generalize (e:(var*tipe_scheme) list) (t:tipe) : tipe_scheme =
  let setadd elt s = if List.memq elt s then s else elt::s in
  let rec union s1 s2 =
    (match s1 with
      [] -> s2
    | hd::tl -> union tl (setadd hd s2)) in
  let minus s1 s2 =
    let rec minus_helper s1 s2 accum =
      (match s1 with
	[] -> accum
      | hd::tl -> if List.memq hd s2 then minus_helper tl s2 accum else minus_helper tl s2 (hd::accum)) in
    minus_helper s1 s2 [] in
  let guesses_of_tipe tt =
    let rec guesses_of_tipe_helper ttt accum =
      (match ttt with
        Guess_t g1 ->
          (match !g1 with
            None -> setadd g1 accum
          | Some tttt -> guesses_of_tipe_helper tttt (setadd g1 accum))
      | List_t tttt -> guesses_of_tipe_helper tttt accum
      | Pair_t (t1, t2) -> union (guesses_of_tipe_helper t1 accum) (guesses_of_tipe_helper t2 accum)
      | Fn_t (t1, t2) -> union (guesses_of_tipe_helper t1 accum) (guesses_of_tipe_helper t2 accum)
      | _ -> accum) in
    guesses_of_tipe_helper tt [] in
  let guesses_of ss = (match ss with Forall (_,tt) -> guesses_of_tipe tt) in
  let rec subst_guess (gs_vs, tt) =
    (match tt with
      Guess_t tt_guess ->
	(match gs_vs with
	  [] -> tt
	| hd::tl -> let (g, v) = hd in if g == tt_guess then Tvar_t v else subst_guess (tl, tt))
    | Fn_t (t1, t2) -> Fn_t ((subst_guess (gs_vs, t1), subst_guess (gs_vs, t2)))
    | Pair_t (t1, t2) -> Pair_t ((subst_guess (gs_vs, t1), subst_guess (gs_vs, t2)))
    | List_t (t1) -> List_t (subst_guess (gs_vs, t1))
    | _ -> tt) in
  let t_gs = guesses_of_tipe t in
  let env_list_gs = List.map (fun (x, s) -> guesses_of s) e in
  let env_gs = List.fold_left union [] env_list_gs in
  let diff = minus t_gs env_gs in
  let gs_vs = List.map (fun g -> (g, freshvar ())) diff in
  let tc = subst_guess (gs_vs, t) in
  Forall (List.map snd gs_vs, tc)

let rec tc (env:(var*tipe_scheme) list) ((e,_):exp) : tipe =
  let zero_args elist : unit =
    (match elist with
      [] -> ()
    | _ -> type_error "Expected zero arguments") in
  (*let one_arg elist : unit =
    (match elist with
      [x] -> ()
    | _ -> type_error "Expected one argument") in
  let two_args elist : unit =
    (match elist with
      x1::x2::[] -> ()
    | _ -> type_error "Expected two arguments") in*)
  let int_binop_check elist : unit =
    (match elist with
      e1::e2::[] ->
	let (t1, t2) = (tc env e1, tc env e2) in
	if (unify t1 Int_t && unify t2 Int_t) then () else type_error "Expected int type"
    | _ -> type_error "Expected two arguments") in
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
  | PrimApp (p, es) ->
    (match p with
      Int _ -> zero_args es; Int_t
    | Bool _ -> zero_args es; Bool_t
    | Unit -> zero_args es; Unit_t
    | Plus -> int_binop_check es; Int_t
    | Minus -> int_binop_check es; Int_t
    | Times -> int_binop_check es; Int_t
    | Div -> int_binop_check es; Int_t
    | Eq -> int_binop_check es; Bool_t
    | Lt -> int_binop_check es; Bool_t
    | Pair ->
      (match es with
	e1::e2::[] -> let (t1, t2) = (tc env e1, tc env e2) in Pair_t (t1, t2)
      | _ -> type_error "Expected two arguments")
    | Fst ->
      (match es with
	[e1] ->
	  let t1 = tc env e1 in
	  let g1 = guess () in
	  let g2 = guess () in
	  if unify t1 (Pair_t (g1, g2)) then g1 else type_error "Expected pair type"
      | _ -> type_error "Expected one argument")
    | Snd ->
      (match es with
	[e1] ->
	  let t1 = tc env e1 in
	  let g1 = guess () in
	  let g2 = guess () in
	  if unify t1 (Pair_t (g1, g2)) then g2 else type_error "Expected pair type"
      | _ -> type_error "Expected one argument")
    | Nil -> zero_args es; let g = guess () in List_t g
    | Cons ->
      (match es with
	e1::e2::[] ->
	  let t1 = tc env e1 in
	  let t2 = tc env e2 in
	  if unify t2 (List_t t1) then List_t t1 else type_error "Mismatched types in list"
      | _ -> type_error "Expected two arguments")
    | IsNil ->
      (match es with
	[e1] ->
	  let t1 = tc env e1 in
	  let g = guess () in
	  if unify t1 (List_t g) then Bool_t else type_error "Expected list type"
      | _ -> type_error "Expected one argument")
    | Hd ->
      (match es with
	[e1] ->
	  let t1 = tc env e1 in
	  let g = guess () in
	  if unify t1 (List_t g) then g else type_error "Expected list type"
      | _ -> type_error "Expected one argument")
    | Tl ->
      (match es with
	[e1] ->
	  let t1 = tc env e1 in
	  let g = guess () in
	  if unify t1 (List_t g) then t1 else type_error "Expected list type"
      | _ -> type_error "Expected one argument"))

let type_check_exp (e:Mlish_ast.exp) : tipe = tc [] e
