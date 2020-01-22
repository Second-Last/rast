(* Lexer *)

signature LEX =
sig
    type lexresult = Terminal.terminal * (int * int)
    val makeLexer : (int -> string) -> lexresult Stream.stream
end

structure Lex :> LEX =
struct

structure PS = ParseState
structure M = Stream
structure T = Terminal

fun error (lpos,rpos) msg = ( ErrorMsg.error (PS.ext(lpos,rpos)) msg
                            ; raise ErrorMsg.Error )

fun id_start_char c =
    Char.isAlpha c
    orelse c = #"$" orelse c = #"_"
    orelse c = #"'"

fun id_char c =
    id_start_char c
    orelse Char.isDigit c

(* run_cond cond (n, accum, cs) = (string, n', cs')
 * accumulate characters in character stream 'cs' satisfying 'cond' in
 * 'accum' and return string, number of characters, and remaining
 * character stream
 *)
fun run_cond cond (n, accum, cs) =
    case M.force cs
     of M.Nil => (String.implode (rev accum), n, cs)
      | M.Cons (c, cs') =>
        if cond c
        then run_cond cond (n+1, c::accum, cs')
        else (String.implode (rev accum), n, cs)

(* lex_code (pos, charstream) = (token, lpos, rpos, cs') *)
(* token is the lexed token, [lpos,rpos) is the source region,
 * and cs' is the remaining character stream
 *)
fun lex_code (pos, charstream) =
    case M.force charstream
     of M.Nil => (T.EOF, pos, pos, charstream)
      (* Pragma *)
      | M.Cons (#"#", cs) => lex_pragma (pos+1, cs)
      (* Whitespace *)
      | M.Cons (#" ", cs) => lex_code (pos+1, cs)
      | M.Cons (#"\t", cs) => lex_code (pos+1, cs)
      | M.Cons (#"\011", cs) => lex_code (pos+1, cs)
      | M.Cons (#"\r", cs) => lex_code (pos+1, cs)
      | M.Cons (#"\n", cs) =>
        ( PS.newline pos        (* track newlines for error messages *)
        ; lex_code (pos+1, cs) )
      (* Separators *)
      | M.Cons (#"{", cs) => (T.LBRACE, pos, pos+1, cs)
      | M.Cons (#"}", cs) => (T.RBRACE, pos, pos+1, cs)
      | M.Cons (#"[", cs) => (T.LBRACKET, pos, pos+1, cs)
      | M.Cons (#"]", cs) => (T.RBRACKET, pos, pos+1, cs)
      | M.Cons (#":", cs) => (T.COLON, pos, pos+1, cs)
      | M.Cons (#",", cs) => (T.COMMA, pos, pos+1, cs)
      | M.Cons (#";", cs) => (T.SEMICOLON, pos, pos+1, cs)
      | M.Cons (#".", cs) => (T.PERIOD, pos, pos+1, cs)
      | M.Cons (#"`", cs) => (T.BACKQUOTE, pos, pos+1, cs)
      | M.Cons (#"+", cs) => (T.PLUS, pos, pos+1, cs)
      | M.Cons (#"-", cs) =>
        (case M.force cs
          of M.Cons(#"o", cs) => (T.LOLLI, pos, pos+2, cs)
          | _ => (T.MINUS, pos, pos+1, cs))
      | M.Cons (#"*", cs) => (T.STAR, pos, pos+1, cs)
      | M.Cons (#"&", cs) => (T.AMPERSAND, pos, pos+1, cs)
      | M.Cons (#"?", cs) => (T.QUESTION, pos, pos+1, cs)
      | M.Cons (#"!", cs) => (T.EXCLAMATION, pos, pos+1, cs)
      (* Short sequences *)
      | M.Cons (#"=", cs) =>
        (case M.force cs
          of M.Cons(#">", cs) => (T.RARROW, pos, pos+2, cs)
           | _ => (T.EQ, pos, pos+1, cs))
      | M.Cons (#"<", cs) =>
        (case M.force cs
          of M.Cons(#"-", cs) =>
             (case M.force cs
               of M.Cons(#">", cs) => (T.LRARROW, pos, pos+3, cs)
                | _ => (T.LARROW, pos, pos+2, cs))
           | M.Cons(#"=", cs) => (T.LEQ, pos, pos+2, cs)
           | M.Cons(#">", cs) => (T.NEQ, pos, pos+2, cs)
           | _ => (T.LANGLE, pos, pos+1, cs))
      | M.Cons (#">", cs) =>
        (case M.force cs
          of M.Cons(#"=", cs) => (T.GEQ, pos, pos+2, cs)
           | _ => (T.RANGLE, pos, pos+1, cs))
      | M.Cons (#"|", cs) =>
        (case M.force cs
          of M.Cons(#"|", cs) => (T.DOUBLEBAR, pos, pos+2, cs)
           | M.Cons(#"-", cs) => (T.TURNSTILE, pos, pos+2, cs)
           | _ => (T.BAR, pos, pos+1, cs))
      | M.Cons (#"%", cs) => lex_comment_line (pos+1, cs)
      | M.Cons (#"(", cs) =>
        (case M.force cs
          of M.Cons(#"*", cs) => lex_comment (pos+2, cs, 1)
           | _ => (T.LPAREN, pos, pos+1, cs))
      | M.Cons (#")", cs) => (T.RPAREN, pos, pos+1, cs)
      | M.Cons (#"/", cs) =>
        (case M.force cs
          of M.Cons(#"\\", cs) => (T.AND, pos, pos+2, cs)
           | _ => (T.SLASH, pos, pos+1, cs) )
      | M.Cons (#"\\", cs) =>
        (case M.force cs
          of M.Cons(#"/", cs) => (T.OR, pos, pos+2, cs)
           | _ => (T.BACKSLASH, pos, pos+1, cs) )
      | M.Cons (c, cs') =>
        if Char.isDigit c
        then let val (num_string, n, cs) = run_cond Char.isDigit (0, [], charstream)
                 val num = Option.valOf(Int.fromString(num_string)) (* need to account for overflow! *)
             in (T.NAT(num), pos, pos+n, cs) end
        else if id_start_char c
        then (case run_cond id_char (0, [], charstream)
               of ("case", n, cs) => (T.CASE, pos, pos+n, cs)
                | ("close", n, cs) => (T.CLOSE, pos, pos+n, cs)
                | ("wait", n, cs) => (T.WAIT, pos, pos+n, cs)
                | ("recv", n, cs) => (T.RECV, pos, pos+n, cs)
                | ("send", n, cs) => (T.SEND, pos, pos+n, cs)
                | ("tick", n, cs) => (T.TICK, pos, pos+n, cs)
                | ("delay", n, cs) => (T.DELAY, pos, pos+n, cs)
                | ("when", n, cs) => (T.WHEN, pos, pos+n, cs)
                | ("now", n, cs) => (T.NOW, pos, pos+n, cs)
                | ("work", n, cs) => (T.WORK, pos, pos+n, cs)
                | ("pay", n, cs) => (T.PAY, pos, pos+n, cs)
                | ("get", n, cs) => (T.GET, pos, pos+n, cs)
                | ("assert", n, cs) => (T.ASSERT, pos, pos+n, cs)
                | ("assume", n, cs) => (T.ASSUME, pos, pos+n, cs)
                | ("impossible", n, cs) => (T.IMPOSSIBLE, pos, pos+n, cs)
                | ("type", n, cs) => (T.TYPE, pos, pos+n, cs)
                | ("eqtype", n, cs) => (T.EQTYPE, pos, pos+n, cs)
                | ("proc", n, cs) => (T.PROC, pos, pos+n, cs)
                | ("exec", n, cs) => (T.EXEC, pos, pos+n, cs)
                | ("decl", n, cs) => (T.DECL, pos, pos+n, cs)
                | (ident, n, cs) => (T.IDENT(ident), pos, pos+n, cs))
        else error (pos, pos+1) ("illegal character: '" ^ Char.toString c ^ "'")

(* single-line comment % ... \n *)
and lex_comment_line (pos, charstream) =
    case M.force charstream
     of M.Nil => (T.EOF, pos, pos, charstream)
      | M.Cons (#"\n", cs) =>
        ( PS.newline pos
        ; lex_code (pos+1, cs) )
      | M.Cons (_, cs) => lex_comment_line (pos+1, cs)

(* single-line pragma #<pragma> ... *)
and lex_pragma (pos, charstream) =
    case run_cond id_char (1, [#"#"], charstream)
      of ("#options", n, cs) =>
         (case run_cond (fn c => c <> #"\n") (0, [], cs)
           (* do not process newline *)
           of (line, m, cs) => (T.PRAGMA("#options", line), pos-1, pos-1+n+m, cs))
       | ("#test", n, cs) =>
         (case run_cond (fn c => c <> #"\n") (0, [], cs)
           of (line, m, cs) => (T.PRAGMA("#test", line), pos-1, pos-1+n+m, cs))
       | (s, n, cs) => error (pos-1, pos-1+n) ("unrecognized pragma: " ^ s)

(* delimited comment (* ... *) *)
and lex_comment (pos, charstream, depth) = (* depth >= 1 *)
    case M.force charstream
     of M.Nil => error (pos, pos) ("unclosed delimited comment: reached end of file")
      | M.Cons(#"\n", cs) =>
        ( PS.newline pos
        ; lex_comment (pos+1, cs, depth) )
      | M.Cons(#"*", cs) =>
        (case M.force cs
          of M.Cons(#")", cs) =>
             (if depth = 1 then lex_code (pos+2, cs)
              else lex_comment (pos+2, cs, depth-1))
           | _ => lex_comment (pos+1, cs, depth))
      | M.Cons(#"(", cs) =>
        (case M.force cs
          of M.Cons(#"*", cs) => lex_comment (pos+2, cs, depth+1)
           | _ => lex_comment (pos+1, cs, depth))
      | M.Cons(_, cs) => lex_comment (pos+1, cs, depth)

(* some infrastructure to allow strings, files, and
 * interactive streams to be lexed
 *)
fun buffered_stream source = 
    let
        fun use_buf (str, len, i) = 
            if i = len 
            then refill_buf ()
            else fn () => M.Cons (String.sub (str, i), use_buf (str, len, i+1))

        and refill_buf () =
            let
                val memo = ref (fn () => raise Match)
                fun read () =
                    let val ans = 
                            case source 1024 of 
                                "" => M.Nil
                              | s => M.Cons (String.sub (s, 0), use_buf (s, size s, 1))
                    in memo := (fn () => ans); ans end
            in memo := read; (fn () => (!memo) ()) end
    in refill_buf () end

fun str_stream str = 
    let val r = ref false
    in buffered_stream (fn _ => if !r then "" else (r := true; str)) end

(* lexresult = (token, (lpos, rpos)) *)
type lexresult = T.terminal * (int * int)

fun lexer (pos, charstream) =
    let val (token, left_pos, right_pos, charstream) = lex_code (pos, charstream)
    in M.Cons ((token, (left_pos, right_pos)), fn () => lexer (right_pos, charstream)) end

(* start counting at pos = 1 for error messages *)
fun makeLexer source = fn () => lexer (1, buffered_stream source)

end (* struct Lex *)
