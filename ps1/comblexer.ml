open Lcombinators.GenericParsing
open Lcombinators.CharParsing

(* the datatype for tokens -- you will need to augment these *)
type token = 
    (* types *)
    INT of int | CHAR of string | NOT | AND | OR
    (* operators *)
  | PLUS | MINUS | TIMES | DIV | EQ | NEQ | LT | LTE | GT | GTE | ASSIGN(* | STAR | SLASH*)
    (* Parens and braces *)
  | LPAREN | RPAREN | LCURLY | RCURLY
    (* non-code critical *)
  | WHITESPACE | COMMENT 
  | SEMI
    (* control statements *)
  | IF | ELSE | WHILE | FOR
  | RETURN
  | EOF

(* removes WHITESPACE and COMMENT tokens from a token list *)
let remove_whitespace (ts: token list) : token list =
  let p = fun a t -> match t with (WHITESPACE | COMMENT) -> a | _ -> t::a in
  List.rev (List.fold_left p [] ts)

(* the tokenize function -- should convert a list of characters to a list of 
 * Fish tokens using the combinators. *)
let rec tokenize(cs:char list) : token list = 
  (* non-code critical *)
  let ws_parser = const_map WHITESPACE white in
  let comment_parser = const_map COMMENT comment in
  (* types *)
  let int_parser = map (fun i -> INT i) integer in
  let and_parser = const_map AND (str "&&") in
  let or_parser = const_map OR (str "||") in
  (* operators *)
  let plus_parser = const_map PLUS (c '+') in
  let minus_parser = const_map MINUS (c '-')  in
  let times_parser = const_map TIMES (c '*') in
  let div_parser = const_map DIV (c '/') in
  let eq_parser = const_map EQ (str "==") in
  let neq_parser = const_map NEQ (str "!=") in
  let lt_parser = const_map LT (c '<') in
  let lte_parser = const_map LTE (str "<=") in
  let gt_parser = const_map GT (c '>') in
  let gte_parser = const_map GTE (str ">=") in
  (* ASSIGN PARSER?? *)
  (*let star_parser = const_map STAR (c '*')  in
  let slash_parser = const_map SLASH (c '/')  in*)
  (* parens and braces *)
  let lparen_parser = const_map LPAREN (c '(') in
  let rparen_parser = const_map RPAREN (c ')') in
  let lcurly_parser = const_map LCURLY (c '{') in
  let rcurly_parser = const_map RCURLY (c '}') in
  (* control statements *)
  let return_parser = const_map RETURN (str "return") in
  let semi_parser = const_map SEMI (c ';') in
  let if_parser = const_map IF (str "if") in
  let else_parser = const_map ELSE (str "else") in
  let while_parser = const_map WHILE (str "while") in
  let for_parser = const_map FOR (str "for") in
  let all_tokens = [int_parser; ws_parser; comment_parser; 
    plus_parser; minus_parser; times_parser; div_parser;
    lparen_parser; rparen_parser; return_parser; semi_parser;
    eq_parser; neq_parser; gt_parser; gte_parser; lt_parser;
    lte_parser] in
  let eof_parser = map (fun _ -> EOF) eof in
  let p = seq (star (alts all_tokens), eof_parser) in
  match run (p cs) with
   | Some (tokens, EOF) -> remove_whitespace tokens
   | _ -> failwith "lex error"
