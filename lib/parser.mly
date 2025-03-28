%token <string> IDENTIFIER
%token <Lang.attrib_tp> TP
%token <bool> BCONSTANT
%token <int> INTCONSTANT
%token <string> STRINGCONSTANT
%token BLAND BLOR
%token EQ GE GT LE LT NE
%token ADD SUB MUL DIV MOD
%token LBRACE RBRACE LBRACKET RBRACKET LPAREN RPAREN 
%token DOT COMMA COLON
%token CREATE DELETE MATCH RETURN SET WHERE
%token ARROW
%token EOF
%token AND OR

%start<Lang.prog> main

%left BLOR
%left BLAND
%left EQ GE GT LE LT NE
%left ADD SUB
%left MUL DIV MOD

%{ open Lang %}

%%

main: prog EOF { $1 }

prog: td = list(tpDecl);  q = query 
     { let (nts, rts) = List.partition_map Fun.id td in Prog (DBG(nts, rts), q) }

tpDecl:
| n = nodeTpDecl { Either.Left n }
| r = relTpDecl { Either.Right r }

query: cls = list(clause) { Query cls }

clause: 
| CREATE pts = separated_list(COMMA, pattern) { Create pts }
| DELETE pts = separated_list(COMMA, pattern) { Delete pts }
| MATCH pts = separated_list(COMMA, pattern) { Match pts }
| RETURN vs = separated_list(COMMA, IDENTIFIER) { Return vs }
| SET v = IDENTIFIER; DOT; fn = IDENTIFIER; EQ; e = expr { Set (v, fn, e) }
| WHERE e = expr { Where e }

pattern: 
| np = npattern { SimpPattern np }
| np = npattern; relspec = relspec; p = pattern { CompPattern (np, relspec, p) }

relspec: 
| SUB LBRACKET COLON RBRACKET ARROW label = IDENTIFIER { RelSpec label }  (* Modifié pour accepter un string *)

npattern: 
| LPAREN; v = IDENTIFIER; COLON; t = IDENTIFIER; RPAREN { DeclPattern(v, t) }
| LPAREN; v = IDENTIFIER; RPAREN { VarRefPattern(v) }

primary_expr:
| vn = IDENTIFIER; DOT; fn = IDENTIFIER { AttribAcc(vn, fn) }
| c = BCONSTANT { Const(BoolV(c)) }
| c = INTCONSTANT { Const(IntV(c)) }
| c = STRINGCONSTANT { Const(StringV(c)) }
| LPAREN e = expr RPAREN { e }

expr:
| a = primary_expr { a }
| e1 = expr; ADD; e2 = expr { Add(e1, e2) }
| e1 = expr; SUB; e2 = expr { Sub(e1, e2) }
| e1 = expr; MUL; e2 = expr { Mul(e1, e2) }
| e1 = expr; DIV; e2 = expr { Div(e1, e2) }
| e1 = expr; EQ; e2 = expr { Eq(e1, e2) }
| e1 = expr; LT; e2 = expr { Lt(e1, e2) }
| e1 = expr; GT; e2 = expr { Gt(e1, e2) }
| e1 = expr; LE; e2 = expr { Le(e1, e2) }
| e1 = expr; GE; e2 = expr { Ge(e1, e2) }
| e1 = expr; AND; e2 = expr { And(e1, e2) }
| e1 = expr; OR; e2 = expr { Or(e1, e2) }

nodeTpDecl: 
| LPAREN; COLON; i = IDENTIFIER; a = attrib_declList; RPAREN { DBN (i, a) }

attrib_decl: 
| i = IDENTIFIER; t = TP { (i, t) }

attrib_declList: 
| LBRACE; ads = separated_list(COMMA, attrib_decl); RBRACE { ads }

relTpDecl:
| si = nodeTpRef; SUB; LBRACKET; COLON; rlab = IDENTIFIER; RBRACKET; ARROW; ti = nodeTpRef
  { Graphstruct.DBR (si, rlab, ti) }

nodeTpRef: 
| LPAREN; COLON; si = IDENTIFIER; RPAREN { si }
