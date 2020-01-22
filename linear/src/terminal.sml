(* Terminal symbols *)
(* Interface between lexer and parser *)

signature TERMINAL =
sig

datatype terminal =
         LBRACE | RBRACE | LPAREN | RPAREN
       | LBRACKET | RBRACKET | LANGLE | RANGLE
       | COLON | COMMA | SEMICOLON | PERIOD
       | BACKQUOTE | PLUS | MINUS | STAR | AMPERSAND | QUESTION | EXCLAMATION | LOLLI
       | BAR | DOUBLEBAR | EQ | RARROW | LRARROW | LARROW
       | LEQ | GEQ | NEQ | AND | OR | SLASH | BACKSLASH
       | CASE | CLOSE | WAIT | SEND | RECV
       | TICK | DELAY | WHEN | NOW
       | WORK | PAY | GET
       | ASSERT | ASSUME | IMPOSSIBLE
       | TURNSTILE
       | TYPE | EQTYPE | PROC | EXEC | DECL
       | IDENT of string | NAT of int
       | EOF | LEX_ERROR
       | PRAGMA of string * string (* pragma and rest of line *)

val toString : terminal -> string

end

structure Terminal :> TERMINAL =
struct

datatype terminal =
         LBRACE | RBRACE | LPAREN | RPAREN
       | LBRACKET | RBRACKET | LANGLE | RANGLE
       | COLON | COMMA | SEMICOLON | PERIOD
       | BACKQUOTE | PLUS | MINUS | STAR | AMPERSAND | QUESTION | EXCLAMATION | LOLLI
       | BAR | DOUBLEBAR | EQ | RARROW | LRARROW | LARROW
       | LEQ | GEQ | NEQ | AND | OR | SLASH | BACKSLASH
       | CASE | CLOSE | WAIT | SEND | RECV
       | TICK | DELAY | WHEN | NOW
       | WORK | PAY | GET
       | ASSERT | ASSUME | IMPOSSIBLE
       | TURNSTILE
       | TYPE | EQTYPE | PROC | EXEC | DECL
       | IDENT of string | NAT of int
       | EOF | LEX_ERROR
       | PRAGMA of string * string (* pragma and rest of line *)

fun toString t =
    case t
     of LBRACE => "{" | RBRACE => "}" | LPAREN => "(" | RPAREN => ")"
      | LBRACKET => "[" | RBRACKET => "]" | LANGLE => "<" | RANGLE => ">"
      | COLON => ":" | COMMA => "," | SEMICOLON => ";" | PERIOD => "."
      | BACKQUOTE => "`" | PLUS => "+" | MINUS => "-" | STAR => "*"
      | AMPERSAND => "&" | QUESTION => "?" | EXCLAMATION => "!" | LOLLI => "-o"
      | BAR => "|" | DOUBLEBAR => "||" | EQ => "=" | RARROW => "=>" | LRARROW => "<->" | LARROW => "<-"
      | LEQ => "<=" | GEQ => ">=" | NEQ => "<>" | AND => "/\\" | OR => "\\/" | SLASH => "/" | BACKSLASH => "\\"
      | CASE => "case"
      | SEND => "send" | RECV => "recv"
      | CLOSE => "close" | WAIT => "wait"
      | TICK => "tick" | DELAY => "delay"
      | WHEN => "when?" | NOW => "now!"
      | WORK => "work" | PAY => "pay" | GET => "get"
      | TURNSTILE => "|-"
      | TYPE => "type" | EQTYPE => "eqtype" | PROC => "proc" | EXEC => "exec" | DECL => "decl"
      | IDENT(s) => s | NAT(n) => Int.toString n
      | EOF => "<eof>" | LEX_ERROR => "<lex error>"
      | PRAGMA(pragma,line) => pragma ^ line

end (* structure Terminal *)
