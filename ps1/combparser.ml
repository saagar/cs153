(* Emmet Jao and Saagar Deshpande *)

(* This file should be extended to implement the Fish parser using the 
 * parsing combinator library, and the combinator-based lexer. *)
open Lcombinators.GenericParsing
open Comblexer
open Ast

let dummy_pos : pos = 0

let mkbinop = fun (e1, (op, e2)) -> (Binop (e1, op, e2), dummy_pos)

(* expressions *)
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

let token_parser (t:token) = satisfy (fun x -> x == t)

(* statements...see parse.mly for the grammar on which this is based *)
let rec make_stmt_parser (():unit) : (token, stmt) parser =
  let semi_parser = token_parser SEMI in
  let single_parser = lazy_seq (lazy (make_exp_parser ()), lazy (lazy_seq (lazy (semi_parser), lazy (make_stmt_parser ())))) in
  let single_stmt_parser = map (fun (e, (_, s)) -> (Seq((Exp(e), dummy_pos), s)), dummy_pos) single_parser in
  let controlexp_parser = lazy_seq (lazy (alt (make_controlexp_parser (), make_controlexp2_parser ())), lazy (make_stmt_parser ())) in
  let controlexp_stmt_parser = map (fun (e1, e2) -> (Seq(e1, e2)), dummy_pos) controlexp_parser in
  alts [single_stmt_parser; controlexp_stmt_parser; make_controlexp_parser (); make_bstmt_parser ()]
and make_bstmt_parser () : (token, stmt) parser =
  let semi_parser = token_parser SEMI in
  let semi_stmt_parser = const_map (Ast.skip, dummy_pos) semi_parser in
  let singleline_parser = lazy_seq (lazy (make_exp_parser ()), lazy semi_parser) in
  let singleline_stmt_parser = map (fun (e, _) -> (Exp(e), dummy_pos)) singleline_parser in
  let return_parser = seq (satisfy (fun t -> t == RETURN), lazy_seq (lazy (make_exp_parser ()), lazy (satisfy (fun t -> t == SEMI)))) in
  let return_stmt_parser = map (fun (_, (e, _)) -> ((Return e), dummy_pos)) return_parser in
  let lcurly_parser = token_parser LCURLY in
  let rcurly_parser = token_parser RCURLY in
  let emptycurly_stmt_parser = const_map (Ast.skip, dummy_pos) (seq (lcurly_parser, rcurly_parser)) in
  let curly_parser = seq (lcurly_parser, lazy_seq (lazy (make_stmt_parser ()), lazy rcurly_parser)) in
  let curly_stmt_parser = map (fun (_, (e, _)) -> e) curly_parser in
  alts [semi_stmt_parser; singleline_stmt_parser; return_stmt_parser; emptycurly_stmt_parser; curly_stmt_parser; make_controlexp2_parser ()]
and make_controlexp_parser () : (token, stmt) parser =
  let for_token_parser = token_parser FOR in
  let lparen_parser = token_parser LPAREN in
  let rparen_parser = token_parser RPAREN in
  let semi_parser = token_parser SEMI in
  let while_token_parser = token_parser WHILE in
  let if_token_parser = token_parser IF in
  let else_token_parser = token_parser ELSE in
  let for_parser = seq (for_token_parser, seq (lparen_parser, lazy_seq (lazy (make_exp_parser ()),
		   lazy (seq (semi_parser, lazy_seq (lazy (make_exp_parser ()), lazy (seq (semi_parser,
                   lazy_seq (lazy (make_exp_parser ()), lazy (seq (rparen_parser, make_controlexp_parser ()))))))))))) in
  let for_stmt_parser = map (fun (_, (_, (e1, (_, (e2, (_, (e3, (_, e4)))))))) -> (For(e1, e2, e3, e4), dummy_pos)) for_parser in
  let while_parser = seq (while_token_parser, seq (lparen_parser, lazy_seq (lazy (make_exp_parser ()),
                   lazy (seq (rparen_parser, make_controlexp_parser ()))))) in
  let while_stmt_parser = map (fun (_, (_, (e1, (_, e2)))) -> (While(e1, e2), dummy_pos)) while_parser in
  let if_parser = seq (if_token_parser, seq (lparen_parser, lazy_seq (lazy (make_exp_parser ()),
                   lazy (seq (rparen_parser, alt (make_controlexp_parser (), make_bstmt_parser ())))))) in
  let if_stmt_parser = map (fun (_, (_, (e1, (_, e2)))) -> (If(e1, e2, (Ast.skip, dummy_pos)), dummy_pos)) if_parser in
  let ifelse_parser = seq (if_token_parser, seq (lparen_parser, lazy_seq (lazy (make_exp_parser ()),
                   lazy (seq (rparen_parser, lazy_seq (lazy (make_bstmt_parser ()), lazy (seq (else_token_parser,
                   make_controlexp_parser ())))))))) in
  let ifelse_stmt_parser = map (fun (_, (_, (e1, (_, (e2, (_, (e3))))))) -> (If(e1, e2, e3), dummy_pos)) ifelse_parser in
  alts [for_stmt_parser; while_stmt_parser; if_stmt_parser; ifelse_stmt_parser]
and make_controlexp2_parser () : (token, stmt) parser =
  let for_token_parser = token_parser FOR in
  let lparen_parser = token_parser LPAREN in
  let rparen_parser = token_parser RPAREN in
  let semi_parser = token_parser SEMI in
  let while_token_parser = token_parser WHILE in
  let if_token_parser = token_parser IF in
  let else_token_parser = token_parser ELSE in
  let for_parser = seq (for_token_parser, seq (lparen_parser, lazy_seq (lazy (make_exp_parser ()),
		   lazy (seq (semi_parser, lazy_seq (lazy (make_exp_parser ()), lazy (seq (semi_parser,
                   lazy_seq (lazy (make_exp_parser ()), lazy (seq (rparen_parser, make_bstmt_parser ()))))))))))) in
  let for_stmt_parser = map (fun (_, (_, (e1, (_, (e2, (_, (e3, (_, e4)))))))) -> (For(e1, e2, e3, e4), dummy_pos)) for_parser in
  let while_parser = seq (while_token_parser, seq (lparen_parser, lazy_seq (lazy (make_exp_parser ()),
                   lazy (seq (rparen_parser, make_bstmt_parser ()))))) in
  let while_stmt_parser = map (fun (_, (_, (e1, (_, e2)))) -> (While(e1, e2), dummy_pos)) while_parser in
  let ifelse_parser = seq (if_token_parser, seq (lparen_parser, lazy_seq (lazy (make_exp_parser ()),
                   lazy (seq (rparen_parser, lazy_seq (lazy (make_bstmt_parser ()), lazy (seq (else_token_parser,
                   make_bstmt_parser ())))))))) in
  let ifelse_stmt_parser = map (fun (_, (_, (e1, (_, (e2, (_, (e3))))))) -> (If(e1, e2, e3), dummy_pos)) ifelse_parser in
  alts [for_stmt_parser; while_stmt_parser; ifelse_stmt_parser]

let parse(ts:token list) : program = 
  let program_parser = make_stmt_parser () in
  match run (program_parser ts) with
   | Some stmt -> stmt
   | None -> failwith "parse error"
