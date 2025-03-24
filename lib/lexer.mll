let comment = 
  "(*" 
  ^ (".*?") 
  ^ "*)"  (* Non-greedy matching of comments *)

let stringchar = 
  alph | num | (' ' | '\"' | '\\')

let string = '"' stringchar* '"'  (* Strings with escape sequences *)

rule token = parse
  | [' ' '\t'] { token lexbuf }  (* Skip whitespace *)
  | '\n' { advance_line lexbuf; token lexbuf }  (* Advance line on newline *)
  | comment { token lexbuf }  (* Ignore comments *)
  | decimal as i { INTCONSTANT (int_of_string i) }  (* Integer constant *)
  | "true" { BCONSTANT true }
  | "false" { BCONSTANT false }
  | "create" { CREATE }
  | "delete" { DELETE }
  | "match" { MATCH }
  | "return" { RETURN }
  | "set" { SET }
  | "where" { WHERE }
  | "->" { ARROW }
  | "+" { ADD }
  | "-" { SUB }
  | "*" { MUL }
  | "/" { DIV }
  | "mod" { MOD }
  | "=" { EQ }
  | ">=" { GE }
  | ">" { GT }
  | "<=" { LE }
  | "<" { LT }
  | "<>" { NE }
  | "and" { BLAND }
  | "or" { BLOR }
  | eof { EOF }
  | "bool" { TP(BoolT) }
  | "int" { TP(IntT) }
  | "string" { TP(StringT) }
  | alph (alph | num)* as id { IDENTIFIER id }
  | string as s { STRINGCONSTANT (clean_string s) }
  | _ { Printf.printf "ERROR: Unrecognized symbol '%s'\n" (Lexing.lexeme lexbuf); raise Lexerror }

