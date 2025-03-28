{
  open Lexing
  open Parser
  open Lang
  exception Lexerror

  (* Pour enlever les guillemets de début et de fin des chaînes *)
  let clean_string s = String.sub s 1 (String.length s - 2) ;;

  let pos lexbuf = (lexeme_start lexbuf, lexeme_end lexbuf)

  let advance_line_pos pos =
    { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum; }

  let advance_line lexbuf =
    lexbuf.lex_curr_p <- advance_line_pos lexbuf.lex_curr_p
}

(* Déclaration des motifs AVANT leur utilisation *)
let alph = ['a'-'z' 'A'-'Z']
let num  = ['0'-'9'] 
let decimal = '0' | ['1'-'9']['0'-'9']*
let comment = "(*" [^ '*']* ('*' ([^ ')'] [^ '*']*)*)* "*)"
let stringchar = alph | num | ' '
let string = '"' stringchar* '"'     

rule token = parse
  | [' ' '\t'] { token lexbuf }    (* Ignorer les espaces blancs *)
  | '\n' { advance_line lexbuf; token lexbuf } 
  | comment { token lexbuf }  (* Ignorer les commentaires *)
  | decimal as i { INTCONSTANT (int_of_string i) }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | '[' { LBRACKET }
  | ']' { RBRACKET }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '.' { DOT }
  | ',' { COMMA }
  | ':' { COLON }
  | "true" { BCONSTANT true }
  | "false" { BCONSTANT false }
  | "create" { CREATE }
  | "delete" { DELETE }
  | "match" { MATCH }
  | "return" { RETURN }
  | "set" { SET }
  | "where" { WHERE }
  | "->" { ARROW }
  | '+' { ADD }
  | '-' { SUB }
  | '*' { MUL }
  | '/' { DIV }
  | "mod" { MOD }
  | '=' { EQ }
  | ">=" { GE }
  | '>' { GT }
  | "<=" { LE }
  | '<' { LT }
  | "<>" { NE }
  | "and" { BLAND }
  | "or" { BLOR }
  | eof { EOF }
  | "bool" { TP(BoolT) }
  | "int" { TP(IntT) }
  | "string" { TP(StringT) }
  | alph (alph | num)* as i { IDENTIFIER i }
  | string as s { STRINGCONSTANT (clean_string s) }
  | _ { Printf.printf "ERROR: unrecognized symbol '%s'\n" (Lexing.lexeme lexbuf);
        raise Lexerror }
