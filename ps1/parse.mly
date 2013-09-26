/* Parser for Fish --- TODO */

%{
open Ast
open Lexing
(* use this to get the line number for the n'th token *)
let rhs n =
  let pos = Parsing.rhs_start_pos n in
  pos.pos_lnum
let parse_error s =
  let pos = Parsing.symbol_end_pos () in
  let l = pos.pos_lnum in
  print_string ("line "^(string_of_int l)^": "^s^"\n") 
  %}



/* Tells us which non-terminal to start the grammar with. */
%start program

/* This specifies the non-terminals of the grammar and specifies the
* types of the values they build. Don't forget to add any new non-
* terminals here.
*/
%type <Ast.program> program
%type <Ast.stmt> stmt

/* The %token directive gives a definition of all of the terminals
* (i.e., tokens) in the grammar. This will be used to generate the
* tokens definition used by the lexer. So this is effectively the
* interface between the lexer and the parser --- the lexer must
* build values using this datatype constructor to pass to the parser.
* You will need to augment this with your own tokens...
*/
/* SAAGAR TODO - add remaining tokens */
%token <int> INT 
%token <string> VAR
%token EOF
%token LPAREN RPAREN ASSIGN EQ EOF PLUS MINUS TIMES DIV SEMI

/* Here's where the real grammar starts -- you'll need to add 
* more rules here... Do not remove the 2%'s!! */
%%

program:
  stmt EOF { $1 }

  stmt :
    /* empty */ /*{ (Ast.skip, 0) } */
    stmt:
      | controlexp stmt
      |


      controlexp:
            | FOR LPAREN exp SEMI exp SEMI exp RPAREN <something>
            | WHILE LPAREN exp RPAREN <something>
            | IF LPAREN exp RPAREN <something>
            | IF LPAREN exp RPAREN <something> ELSE <something>

            exp:
                      | INT         { Ast.Int($1), rhs 1 }
                      | VAR ASSIGN exp
                      | VAR         { Ast.Var($1) }
                      | LPAREN exp RPAREN { ($2) }
                      | exp PLUS exp    { Ast.Binop($1, Plus, $3), rhs
                      2}
                                | exp MINUS exp   { Ast.Binop($1, Minus, $3),
                                rhs 2}
                                  | exp TIMES exp   { Ast.Binop($1, Times, $3),
                                  rhs 2}
                                    | exp DIV exp   { Ast.Binop($1, Div, $3),
                                    rhs 2}
                                      | exp EQ exp    { Ast.Binop($1, Eq, $3),
                                      rhs 2}
                                        | exp NEQ exp   { Ast.Binop($1, Neq,
                                        $3), rhs 2}
                                          | exp LTE exp   { Ast.Binop($1, Lte,
                                          $3), rhs 2}
                                            | exp GTE exp   { Ast.Binop($1, Gte,
                                            $3), rhs 2}
                                              | exp LTE exp   { Ast.Binop($1,
                                              Lte, $3), rhs 2}
                                                | exp GT exp    { Ast.Binop($1,
                                                Gt, $3), rhs 2}
                                                  | exp LT exp    {
                                                    Ast.Binop($1, Lt, $3), rhs
                                                    2}
