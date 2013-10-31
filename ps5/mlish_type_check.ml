open Mlish_ast

exception TypeError
let type_error(s:string) = (print_string s; raise TypeError)

let type_check_exp (e:Mlish_ast.exp) : tipe = raise TypeError

(* Generate a new Guess_t *)
let guess () =
  Guess_t(ref None)

let rec unify (t1:tipe) (t2:tipe) : bool =
  if (t1 = t2) then true
  else
    match (t1, t2) with
    | Guess_t(t1_guess), t2 -> 
        (
          match !t1_guess with
          | None ->
              if (occurs
          | Some(t1_g) -> unify t1_g t2
        )
    | (t1, 
