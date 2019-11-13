(* Terminal symbols *)
(* Interface between lexer and parser *)

signature TERMINAL =
sig

datatype terminal =
         LBRACE | RBRACE | LPAREN | RPAREN
       | LBRACKET | RBRACKET | LANGLE | RANGLE
       | COLON | COMMA | SEMICOLON | PERIOD
       | BACKQUOTE | PLUS | MINUS | STAR | AMPERSAND | QUESTION | EXCLAMATION
       | BAR | DOUBLEBAR | EQ | RARROW | LRARROW | LARROW
       | LEQ | GEQ
       | CASER | CASEL | R | L | CLOSER | WAITL
       | TICK | DELAY | WHENR | WHENL | NOWR | NOWL
       | WORK | PAYL | PAYR | GETL | GETR
       | ASSERTR | ASSERTL | ASSUMER | ASSUMEL | IMPOSSIBLER | IMPOSSIBLEL
       | TURNSTILE
       | TYPE | EQTYPE | PROC | EXEC
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
       | BACKQUOTE | PLUS | MINUS | STAR | AMPERSAND | QUESTION | EXCLAMATION
       | BAR | DOUBLEBAR | EQ | RARROW | LRARROW | LARROW
       | LEQ | GEQ
       | CASE | CLOSE | WAIT
       | TICK | DELAY | WHEN | NOW`
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
      | BACKQUOTE => "`" | PLUS => "+" | MINUS => "-" | STAR => "*" | AMPERSAND => "&" | QUESTION => "?" | EXCLAMATION => "!"
      | BAR => "|" | DOUBLEBAR => "||" | EQ => "=" | RARROW => "=>" | LRARROW => "<->" | LARROW => "<-"
      | LEQ => "<=" | GEQ => ">="
      | CASER => "case"
      | CLOSE => "close" | WAITL => "wait"
      | TICK => "tick" | DELAY => "delay"
      | WHEN => "when?" | NOW => "now!"
      | WORK => "work" | PAY => "pay" | GET => "get"
      | TURNSTILE => "|-"
      | TYPE => "type" | EQTYPE => "eqtype" | PROC => "proc" | EXEC => "exec" | DECL => "decl"
      | IDENT(s) => s | NAT(n) => Int.toString n
      | EOF => "<eof>" | LEX_ERROR => "<lex error>"
      | PRAGMA(pragma,line) => pragma ^ line

end (* structure Terminal *)
