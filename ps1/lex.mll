(* Lexer for Fish --- TODO *)

(* You need to add new definition to build the
 * appropriate terminals to feed to parse.mly.
 *)

{
open Parse
open Lexing

let incr_lineno lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <- { pos with
    pos_lnum = pos.pos_lnum + 1;
    pos_bol = pos.pos_cnum;
  }
}

(* definition section *)
let cr='\013'
let nl='\010'
let eol=(cr nl|nl|cr)
let ws=('\012'|'\t'|' ')*
let digit=['0'-'9'] 
let identifier = ['a'-'z' 'A'-'Z'] (['a'-'z' 'A'-'Z' '0'-'9' '_'])*

(* rules section *)
rule lexer = parse
| eol { incr_lineno lexbuf; lexer lexbuf }
| ws+ { lexer lexbuf }
  (* comments *)
| "/*"  { comment lexbuf }
  (* keywords *)
| "for" { FOR }
| "while" { WHILE }
| "if"  { IF }
| "else"  { ELSE }
| "return"  { RETURN }
| digit+ { INT(int_of_string(Lexing.lexeme lexbuf)) }
| identifier as text  { VAR (text) }
  (* Binops *)
| "+"   { PLUS }
| "-"   { MINUS }
| "*"   { TIMES }
| "/"   { DIV }
| "=="  { EQ }
| "!="  { NEQ }
| ">="  { GTE }
| "<="  { LTE }
| "="   { ASSIGN }
| "<"   { LT }
| ">"   { GT }
| "&&"  { AND }
| "||"  { OR }  
| eof   { EOF }
| "!"   { NOT }
  (* delimiters *)
| ";"   { SEMI }
| "{"   { LCURLY}  
| "}" { RCURLY }
| "(" { LPAREN }
| ")" { RPAREN }

and comment = parse
  | "*/"  { comment lexbuf } (* NOTE: is this correct? *)
  | eof { raise (Failure "missing comment terminator") }
  | _   { comment lexbuf }
