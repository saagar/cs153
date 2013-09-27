(* This file should be extended to implement the Fish parser using the 
 * parsing combinator library, and the combinator-based lexer. *)
open Lcombinators.GenericParsing
open Comblexer
open Ast

let dummy_pos : pos = 0

(*let rec make_exp_parser (():unit) : (token, exp) parser =
  let int_parser = satisfy_opt (function INT i -> Some (Int i, dummy_pos) | _ -> None) in
  let sub_parser = seq (satisfy (fun t -> t == LPAREN), 
    lazy_seq (lazy (make_exp_parser ()), lazy (satisfy (fun t -> t == RPAREN)))) in 
  let sub_exp_parser = map (fun (_, (e, _)) -> e) sub_parser in
  let first_parser = alt (int_parser, sub_exp_parser) in
  let rest_parser = seq (first_parser, make_binop_rest ()) in
  let binop_parser = map (fun (e1, (op, e2)) -> (Binop (e1, op, e2), dummy_pos)) rest_parser in
  alts [binop_parser; first_parser]
and make_binop_rest (():unit) : (token, (binop * exp)) parser =
  let binop_op_parser = satisfy_opt (function 
    PLUS -> Some Plus | MINUS -> Some Minus | STAR -> Some Times | SLASH -> Some Div | _ -> None) in
  lazy_seq (lazy binop_op_parser, lazy (make_exp_parser ()))*)

let mkbinop = fun (e1, (op, e2)) -> (Binop (e1, op, e2), dummy_pos)

let rec make_aexp_parser () : (token, exp) parser =
  let int_parser = satisfy_opt (function INT i -> Some (Int i, dummy_pos) | _ -> None) in
  let var_parser = satisfy_opt (function VAR s -> Some (Var s, dummy_pos) | _ -> None) in
  let sub_parser = seq (satisfy (fun t -> t == LPAREN), 
    lazy_seq (lazy (make_exp_parser ()), lazy (satisfy (fun t -> t == RPAREN)))) in 
  let sub_exp_parser = map (fun (_, (e, _)) -> e) sub_parser in
  alts [int_parser; sub_exp_parser; var_parser]
and make_bexp_parser () : (token, exp) parser =
  let neg_op_parser = satisfy_opt (function MINUS -> Some Minus | _ -> None) in
  let helper = lazy_seq (lazy neg_op_parser, lazy (make_aexp_parser ())) in
  let mkneg = fun (op, e) -> (Binop ((Int 0, dummy_pos), op, e), dummy_pos) in
  let neg_parser = map mkneg helper in
  let not_op_parser = satisfy (function NOT -> true | _ -> false) in
  let not_helper = lazy_seq (lazy not_op_parser, lazy (make_aexp_parser ())) in
  let mknot = fun (_, e) -> (Not e, dummy_pos) in
  let not_parser = map mknot not_helper in
  alts [make_aexp_parser (); neg_parser; not_parser]
and make_cexp_parser () : (token, exp) parser =
  let op_parser = satisfy_opt (function TIMES -> Some Times | DIV -> Some Div | _ -> None) in
  let helper = lazy_seq (lazy (make_bexp_parser ()), lazy (lazy_seq (lazy op_parser, lazy (make_cexp_parser ())))) in
  let binop_parser = map mkbinop helper in
  alt (make_bexp_parser (), binop_parser)
and make_dexp_parser () : (token, exp) parser =
  let op_parser = satisfy_opt (function PLUS -> Some Plus | MINUS -> Some Minus | _ -> None) in
  let helper = lazy_seq (lazy (make_cexp_parser ()), lazy (lazy_seq (lazy op_parser, lazy (make_dexp_parser ())))) in
  let binop_parser = map mkbinop helper in
  alt (make_cexp_parser (), binop_parser)
and make_eexp_parser () : (token, exp) parser =
  let token2val = function GT -> Some Gt | GTE -> Some Gte | LT -> Some Lt | LTE -> Some Lte | _ -> None in
  let op_parser = satisfy_opt token2val in
  let helper = lazy_seq (lazy (make_dexp_parser ()), lazy (lazy_seq (lazy op_parser, lazy (make_eexp_parser ())))) in
  let binop_parser = map mkbinop helper in
  alt (make_dexp_parser (), binop_parser)
and make_fexp_parser () : (token, exp) parser =
  let token2val = function EQ -> Some Eq | NEQ -> Some Neq | _ -> None in
  let op_parser = satisfy_opt token2val in
  let helper = lazy_seq (lazy (make_eexp_parser ()), lazy (lazy_seq (lazy op_parser, lazy (make_fexp_parser ())))) in
  let binop_parser = map mkbinop helper in
  alt (make_eexp_parser (), binop_parser)
and make_gexp_parser () : (token, exp) parser =
  let and_op_parser = satisfy (function AND -> true | _ -> false) in
  let and_helper = lazy_seq (lazy (make_fexp_parser ()), lazy (lazy_seq (lazy and_op_parser, lazy (make_gexp_parser ())))) in
  let mkand = fun (e1, (_, e2)) -> (And (e1, e2), dummy_pos) in
  let and_parser = map mkand and_helper in
  alt (make_fexp_parser (), and_parser)
and make_hexp_parser () : (token, exp) parser =
  let or_op_parser = satisfy (function OR -> true | _ -> false) in
  let or_helper = lazy_seq (lazy (make_gexp_parser ()), lazy (lazy_seq (lazy or_op_parser, lazy (make_hexp_parser ())))) in
  let mkor = fun (e1, (_, e2)) -> (Or (e1, e2), dummy_pos) in
  let or_parser = map mkor or_helper in
  alt (make_gexp_parser (), or_parser)
and make_exp_parser () : (token, exp) parser =
  let assign_op_parser = satisfy (function ASSIGN -> true | _ -> false) in
  let var_parser = satisfy_opt (function VAR s -> Some (s) | _ -> None) in
  let assign_helper = lazy_seq (lazy (var_parser), lazy (lazy_seq (lazy assign_op_parser, lazy (make_exp_parser ())))) in
  let mkassign = fun (e1, (_, e2)) -> (Assign(e1, e2), dummy_pos) in
  alt (make_hexp_parser (), map mkassign assign_helper)

let rec make_stmt_parser (():unit) : (token, stmt) parser =
  let return_parser = seq (satisfy (fun t -> t == RETURN), lazy_seq (lazy (make_exp_parser ()), 
    lazy (satisfy (fun t -> t == SEMI)))) in
  let return_stmt_parser = map (fun (_, (e, _)) -> ((Return e), dummy_pos)) return_parser in
  let exp_stmt_parser = map (fun e -> (Exp e, dummy_pos)) (make_exp_parser ()) in
  alts [return_stmt_parser; exp_stmt_parser]

let parse(ts:token list) : program = 
  let program_parser = make_stmt_parser () in
  match run (program_parser ts) with
   | Some stmt -> stmt
   | None -> failwith "parse error"
