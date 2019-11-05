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
       | CASER | CASEL | R | L | CLOSER | WAITL
       | TICK | DELAY | WHENR | WHENL | NOWR | NOWL
       | WORK | PAYL | PAYR | GETL | GETR
       | ASSERTR | ASSERTL | ASSUMER | ASSUMEL | IMPOSSIBLER | IMPOSSIBLEL
       | TURNSTILE
       | TYPE | EQTYPE | PROC | EXEC
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
      | CASER => "caseR" | CASEL => "caseL" | R => "R" | L => "L"
      | CLOSER => "closeR" | WAITL => "waitL"
      | TICK => "tick" | DELAY => "delay"
      | WHENR => "whenR" | WHENL => "whenL" | NOWR => "nowR" | NOWL => "nowL"
      | WORK => "work" | PAYL => "payL" | PAYR => "payR" | GETL => "getL" | GETR => "getR"
      | TURNSTILE => "|-"
      | TYPE => "type" | EQTYPE => "eqtype" | PROC => "proc" | EXEC => "exec"
      | IDENT(s) => s | NAT(n) => Int.toString n
      | EOF => "<eof>" | LEX_ERROR => "<lex error>"
      | PRAGMA(pragma,line) => pragma ^ line

end (* structure Terminal *)
