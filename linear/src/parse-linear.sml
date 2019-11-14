(* Parser *)
(* Handwritten shift/reduce parser to support
 * best possible error messages
 *)

signature PARSE =
sig

    val parse : string -> Ast.env
    val parse_preamble : string -> Ast.env (* may raise IO.Io _ *)

end  (* signature PARSE *)

structure Parse :> PARSE =
struct

structure R = Arith
structure A = Ast
structure PS = ParseState
structure M = Stream
structure T = Terminal
structure L = Lex

(******************)
(* Error Messages *)
(******************)
              
fun pp_tok t = "'" ^ T.toString t ^ "'"

fun pp_toks (nil) = ""
  | pp_toks (t::nil) = " or " ^ pp_tok t
  | pp_toks (t::ts) = pp_tok t ^ ", " ^ pp_toks ts

fun ^^(s1,s2) = s1 ^ "\n[Hint: " ^ s2 ^ "]"
infix ^^

fun parse_error (region, s) =
    ( ErrorMsg.error (PS.ext region) s
    ; raise ErrorMsg.Error )

fun msg_expected t' t =
    ("expected " ^ pp_tok t' ^ ", found: " ^ pp_tok t)

fun error_expected (region, t', t) =
    ( ErrorMsg.error (PS.ext region) (msg_expected t' t)
    ; raise ErrorMsg.Error) 

fun error_expected_h (region, t', t, error_hint) =
    ( ErrorMsg.error (PS.ext region) (msg_expected t' t ^^ error_hint)
    ; raise ErrorMsg.Error )

fun msg_expected_list ts t =
    "expected one of " ^ pp_toks ts ^ ", found: " ^ pp_tok t

fun error_expected_list (region, ts, t) =
    ( ErrorMsg.error (PS.ext region) (msg_expected_list ts t)
    ; raise ErrorMsg.Error )

fun error_expected_list_h (region, ts, t, error_hint) =
    ( ErrorMsg.error (PS.ext region) (msg_expected_list ts t ^^ error_hint)
    ; raise ErrorMsg.Error )
 
fun location (NONE) = "_"
  | location (SOME(mark)) = Mark.show(mark)

(****************************)
(* Building abstract syntax *)
(****************************)
fun vars ((x,phi)::l) = x::(vars l)
  | vars nil = nil

fun conjoin (R.True) phi' = phi'
  | conjoin phi (R.True) = phi
  | conjoin phi phi' = R.And(phi, phi')

fun phis ((x,phi)::l) = conjoin phi (phis l)
  | phis nil = R.True

fun mark_exp (exp, (left, right)) = A.Marked (Mark.mark' (exp, PS.ext (left, right)))

(*******************)
(* Data structures *)
(*******************)

type region = int * int

datatype infix_item =
   Cut of A.pot * A.tp
 | Spawn

(* operator precedence, for arithmetic *)
type prec = int

(* stack items for shift/reduce parsing *)
datatype stack_item =
   Tok of T.terminal * region   (* lexer token *)
 | ArithInfix of prec * (R.arith * R.arith -> R.arith) * region (* arithmetic infix operator and constructor *)
 | Arith of R.arith * region                                    (* arithmetic expression *)
 | Prop of R.prop * region                                      (* proposition *)
 | Vars of (R.varname * R.prop) list * region                   (* list of variables with constraints *)
 | Indices of R.arith list * region                             (* list of index expressions *)
 | Tp of A.tp * region                                          (* types *)
 | Alts of A.choices                                            (* list of alternatives in types *)
 | Action of (A.exp -> A.exp) * region                          (* prefix process action *)
 | Infix of infix_item * region                                 (* infix process expression *)
 | Args of (A.chan list) * region                               (* arguments for spawn *)
 | Exp of A.exp * region                                        (* process expression *)
 | Branches of A.branches                                       (* list of branches *)
 | Context of (A.chan * A.tp) list * region                     (* context *)
 | Decl of A.decl                                               (* top-level declaration *)


datatype stack
  = Bot
  | $ of stack * stack_item

infix 2 $

(* This is a hand-written shift/reduce parser
 * I have tried to resist the temptation to optimize or transform,
 * since it is very easy to make mistakes.
 *
 * Parsing functions are named p_<nonterminal>, possibly with a suffix
 * for intermediate parsing states.  Reducing functions are named
 * r_<nonterminal>, possibly with a suffix for intermediate states.
 * With few exceptions, a parsing functions have type
 *
 * p_<nonterminal> : stack * L.lexresult M.Front -> stack * L.lexresult M.Front
 * r_<nonterminal> : stack -> stack
 *
 * Note that in input and output of the parsing function, the first
 * token of the lexer stream is exposed (type L.lexresult M.Front) which
 * make for easy matching and composition of these functions.
 *
 * Generally p_<nt> will consume terminals for an <nt> from the lexresult
 * stream and return with the resulting abstract syntax for <nt> on the stack.
 * Generally r_<nt> will consume a mix of terminal and nonterminals on
 * the stack and push the abstract syntax for an <nt> onto the stack.
 *
 * While parsing expression with infix, prefix, and postfix operators
 * we continue parsing, extending the expression until we encounter
 * a terminal that completes that is not part of an expression.
 *
 * p_<nt> is a function that parses nonterminal <nt>
 * r_<nt> is a function that reduces nonterminal <nt>
 * c_<cond> is a function that checks condition <cond>
 * e_<error> is a function that reports error <error>
 * m_<nt> is a function that marks nonterminal <nt> with region information
 *)

(***********************)
(* Parsing Combinators *)
(***********************)

(* Always call 'first ST' to extract the first token for examination *)
fun first (S, M.Cons((t, r), ts')) = t

fun shift (S, M.Cons((t, r), ts')) = (S $ Tok(t, r), M.force ts')
fun reduce reduce_fun (S, ft) = (reduce_fun S, ft)

fun drop (S, M.Cons((t, r), ts')) = (S, M.force ts') (* use sparingly *)
fun push item (S, ft) = (S $ item, ft)

fun >>(f,g) = fn x => g(f(x))
fun |>(x,f) = f x

infixr 2 >>
infix 1 |>

(* region manipulation *)
fun join (left1, right1) (left2, right2) = (left1, right2)
fun here (S, M.Cons((t, r), ts')) = r
val nowhere = (0,0)

(***********)
(* Parsing *)
(***********)

(*
 * Refer to the grammar in readme.txt
 * Comments refer to the nonterminals shown there in <angle brackets>
 *)

(* <decl> *)
fun p_decl ST = case first ST of
    T.TYPE => ST |> shift >> p_id_var_seq >> p_eq_type >> reduce r_decl
  | T.EQTYPE => ST |> shift >> p_eqtype >> reduce r_decl
  | T.PROC => ST |> shift >> p_exp_def >> reduce r_decl
  | T.DECL => ST |> shift >> p_id_var_seq >> p_exp_decl >> reduce r_decl
  | T.EXEC => ST |> shift >> p_id >> reduce r_decl
  | T.PRAGMA _ => ST |> shift >> reduce r_decl
  | T.EOF => ST
  | t => parse_error (here ST, "unexpected token " ^ pp_tok t ^ " at top level")

(* <id> <var_seq> *)
(* Vars(_,r) accumulates the ast for <var_seq> *)
and p_id_var_seq ST = ST |> p_id >> push (Vars(nil, here ST)) >> p_var_seq

(* <var_seq> *)
and p_var_seq ST = case first ST of
    T.LBRACE => ST |> p_terminal T.LBRACE >> p_var_prop >> p_terminal T.RBRACE >> reduce r_var_seq >> p_var_seq
  | t => ST

(* <var> |  <var> '|' <prop> *) 
and p_var_prop ST = ST |> p_id >> p_bar_prop_opt

(* ['|' <prop>] *)
and p_bar_prop_opt ST = case first ST of
    T.BAR => ST |> drop >> p_prop
  | _ => ST

(* accumulate (v,phi) for every variable v and constraint phi (defaults to 'true') *)
and r_var_seq (S $ Vars(l,r1) $ Tok(T.LBRACE,_) $ Tok(T.IDENT(v),_) $ Prop(phi,_) $ Tok(T.RBRACE,r2)) =
    S $ Vars(l @ [(v,phi)], join r1 r2)
  | r_var_seq (S $ Vars(l,r1) $ Tok(T.LBRACE,_) $ Tok(T.IDENT(v),_) $ Tok(T.RBRACE,r2)) =
    S $ Vars(l @ [(v,R.True)], join r1 r2)

(* <id> <idx_seq> *)
(* Indices(_,r) accumulates the ast for <idx_seq> *)
and p_id_idx_seq ST = ST |> p_id >> push (Indices(nil, here ST)) >> p_idx_seq

(* <idx_seq> *)
and p_idx_seq ST = case first ST of
    T.LBRACE => ST |> p_idx >> reduce r_idx_seq >> p_idx_seq
  | t => ST

(* accumulate e into sequence of indices *)
and r_idx_seq (S $ Indices(l,r1) $ Arith(e,r2)) = S $ Indices(l @ [e], join r1 r2)

(* '=' <type> *)
and p_eq_type ST = case first ST of
    T.EQ => ST |> shift >> p_type
  | t => error_expected (here ST, T.EQ, t)
(* check S = empty here? *)

(* <id> <idx_seq> '=' <id> <idx_seq> *)
and p_eqtype ST = ST |> p_id_idx_seq >> p_terminal T.EQ >> p_id_idx_seq

(* ':' [ <type_opt> <turnstile> ] <type> | '=' <exp> *)
and p_exp_decl ST = case first ST of
    T.COLON => ST |> shift >> p_context_opt >> p_turnstile_id_tp
  | t => error_expected (here ST, T.COLON, t)

and p_context_opt ST = case first ST of
    T.PERIOD => ST |> drop >> push (Context([], here ST))
  | T.LPAREN => ST |> push (Context([], here ST)) >> p_context
  | t => error_expected_list (here ST, [T.PERIOD, T.LPAREN], t)
  
and p_context ST = ST |> p_terminal T.LPAREN >> p_id >> p_terminal T.COLON >> p_type >> p_terminal T.RPAREN >> reduce r_chan_tp >> p_context2

and p_context2 ST = case first ST of
    T.LPAREN => ST |> p_context
  | T.TURNSTILE => ST
  | T.BAR => ST
  | t => error_expected_list (here ST, [T.LPAREN, T.TURNSTILE, T.BAR], t)

and r_chan_tp (S $ Context(ctx, r) $ Tok(T.LPAREN, _) $ Tok(T.IDENT(id), _) $ Tok(T.COLON,_) $ Tp(tp,_) $ Tok(T.RPAREN, r2)) = S $ Context(ctx @ [(id,tp)], join r r2)

(* <turnstile> <id> : <type> *)
and p_turnstile_id_tp ST = case first ST of
    T.TURNSTILE => ST |> shift >> p_id_tp
  | T.BAR => ST |> shift >> p_idx >> p_terminal T.MINUS >> p_id_tp
  | t => error_expected_list (here ST, [T.TURNSTILE, T.BAR], t)

and p_id_tp ST = ST |> p_terminal T.LPAREN >> p_id >> p_terminal T.COLON >> p_type >> p_terminal T.RPAREN

and p_exp_def ST = ST |> p_id >> p_terminal T.LARROW >> p_id_var_seq >> p_terminal T.LARROW >> push (Args ([], here ST)) >> p_id_list_opt_decl

and p_id_list_opt_decl ST = case first ST of
    T.IDENT(_) => ST |> p_id >> reduce r_arg >> p_id_list_opt_decl
  | T.EQ => ST |> shift >> p_exp
  | t => parse_error (here ST, "expected = or identifier, found: " ^ pp_tok t)

and r_arg (S $ Args(args, r1) $ Tok(T.IDENT(id), r2)) = S $ Args(args @ [id], join r1 r2)

(* reduce top-level declaration *)
and r_decl (S $ Tok(T.TYPE,r1) $ Tok(T.IDENT(id),_) $ Vars(l,_) $ Tok(T.EQ,_) $ Tp(tp,r2)) =
    (* 'type' <id> <var_seq> = <type> *)
    S $ Decl(A.TpDef(id,vars l,phis l,tp,PS.ext(join r1 r2)))
  | r_decl (S $ Tok(T.EQTYPE,r1) $ Tok(T.IDENT(id1),_) $ Indices(l1,_) $ Tok(T.EQ,_) $ Tok(T.IDENT(id2),_) $ Indices(l2, r2)) =
    (* 'eqtype' <id> <idx_seq> = <id> <idx_seq> *)
    S $ Decl(A.TpEq([],R.True,A.TpName(id1,l1),A.TpName(id2,l2),PS.ext(join r1 r2)))
  | r_decl (S $ Tok(T.DECL,r1) $ Tok(T.IDENT(id),_) $ Vars(l,_) $ Tok(T.COLON,_) $ Context(context,_) $ Tok(T.TURNSTILE,_) $ Tok(T.LPAREN,_) $ Tok(T.IDENT(c),_) $ Tok(T.COLON,_) $ Tp(tp,_) $ Tok(T.RPAREN,r2)) =
    (* 'decl' <id> <var_seq> : <context> |- <id> : <type> *)
    S $ Decl(A.ExpDec(id,vars l,phis l,(context,R.Int(0),(c,tp)), PS.ext(join r1 r2)))
  | r_decl (S $ Tok(T.DECL,r1) $ Tok(T.IDENT(id),_) $ Vars(l,_) $ Tok(T.COLON,_) $ Context(context,_) $ Tok(T.BAR,_) $ Arith(pot,_) $ Tok(T.MINUS,_) $ Tok(T.LPAREN,_) $ Tok(T.IDENT(c),_) $ Tok(T.COLON,_) $ Tp(tp,_) $ Tok(T.RPAREN,r2)) =
    (* 'decl' <id> <var_seq> : <context> '|{' <arith> '}-' <id> : <type> *)
    S $ Decl(A.ExpDec(id,vars l,phis l,(context,pot,(c,tp)), PS.ext(join r1 r2)))
  | r_decl (S $ Tok(T.PROC,r1) $ Tok(T.IDENT(x),_) $ Tok(T.LARROW,_) $ Tok(T.IDENT(id),_) $ Vars(l,r) $ Tok(T.LARROW,_) $ Args(xs,_) $ Tok(T.EQ,_) $ Exp(exp,r2)) =
    (* 'proc' <id> '<-' <id> <var_seq> '<-' <id_list> = <exp> *)
    (case (phis l)
     of R.True => S $ Decl(A.ExpDef(id,vars l,(xs, exp, x),PS.ext(join r1 r2)))
      | _ => parse_error (r, "constraint found in process definition"))
  | r_decl (S $ Tok(T.EXEC,r1) $ Tok(T.IDENT(id),r2)) =
    (* 'exec' <id> *)
    S $ Decl(A.Exec(id, PS.ext(join r1 r2)))
  | r_decl (S $ Tok(T.PRAGMA(p,line),r)) =
    (* '#' <line> '\n' *)
    S $ Decl(A.Pragma(p,line,PS.ext(r)))
  (* should be the only possibilities *)

(* <idx> ::= '{' <arith> '}' *)
and p_idx ST = case first ST of
    T.LBRACE => ST |> shift >> p_arith >> p_terminal T.RBRACE >> reduce r_idx
  | t => error_expected (here ST, T.LBRACE, t)

(* <arith> *)
and p_arith ST = case first ST of
    T.NAT(n) => ST |> shift >> reduce r_arith >> p_arith
  | T.IDENT(v) => ST |> shift >> reduce r_arith >> p_arith
  | T.LPAREN => ST |> shift >> p_arith >> p_terminal T.RPAREN >> reduce r_arith >> p_arith
  | T.PLUS => ST |> drop >> push (ArithInfix(1, R.Add, here ST)) >> p_arith_prec
  | T.MINUS => ST |> drop >> push (ArithInfix(1, R.Sub, here ST)) >> p_arith_prec
  | T.STAR => ST |> drop >> push (ArithInfix(2, R.Mult, here ST)) >> p_arith_prec
  | t => ST |> reduce r_arith

(* <arith> *)
(* shift/reduce decision based on operator precedence *)
and p_arith_prec (ST as (S $ Arith(e1, r1) $ ArithInfix(prec1, con1, _) $ Arith(e2, r2) $ ArithInfix(prec, con, r), ft)) =
    if prec1 >= prec (* all operators are left associative *)
    then p_arith_prec (S $ Arith(con1(e1,e2), join r1 r2) $ ArithInfix(prec, con, r), ft) (* reduce *)
    else p_arith ST          (* shift *)
  | p_arith_prec (ST as (S $ Arith(e,r) $ ArithInfix(prec, con, _), ft)) = p_arith ST (* shift *)
  | p_arith_prec (ST as (S $ ArithInfix(_,_,r1) $ ArithInfix(_,_,r2), ft)) = parse_error (join r1 r2, "consecutive infix operators")
  | p_arith_prec (ST as (S $ ArithInfix(_,_,r), ft)) = parse_error (r, "leading infix operator")

(* reduce <arith> *)
and r_arith (S $ Tok(T.NAT(n),r)) = S $ Arith(R.Int(n), r)
  | r_arith (S $ Tok(T.IDENT(v),r)) = S $ Arith(R.Var(v), r)
  | r_arith (S $ Tok(T.LPAREN, r1) $ Arith(e, _) $ Tok(T.RPAREN, r2)) = S $ Arith(e, join r1 r2)
  | r_arith (S $ Arith(e1, r1) $ ArithInfix(_, con, _) $ Arith(e2, r2)) = r_arith (S $ Arith(con(e1,e2), join r1 r2))
  | r_arith (S $ Arith(e1, r1) $ Arith(e2, r2)) = parse_error (join r1 r2, "consecutive arithmetic expressions")
  | r_arith (S $ ArithInfix(_, _, r)) = parse_error (r, "trailing infix operator")
  | r_arith (S $ Arith(e,r)) = S $ Arith(e,r)
  | r_arith (S $ Tok(_,r)) = parse_error (r, "empty arithmetic expression")
  (* arithmetic expressions are always preceded by '{' or '(' *)

(* reduce '{' <arith> '}' *)
and r_idx (S $ Tok(T.LBRACE,r1) $ Arith(e, _) $ Tok(T.RBRACE,r2)) = S $ Arith (e, join r1 r2)

(* <tp> *)
and p_type ST = case first ST of
    T.NAT(1) => ST |> shift >> reduce r_type
  | T.PLUS => ST |> shift >> p_choices >> reduce r_type
  | T.AMPERSAND => ST |> shift >> p_choices >> reduce r_type
  | T.BACKQUOTE => ST |> shift >> p_type >> reduce r_type
  | T.LPAREN => ST |> shift >> p_tpopr_next >> p_type >> reduce r_type
  | T.LBRACKET => ST |> shift >> p_terminal T.RBRACKET >> p_type >> reduce r_type
  | T.LANGLE => ST |> shift >> p_tpopr_dia_ltri >> p_type >> reduce r_type (* maybe not shift *)
  | T.BAR => ST |> shift >> p_tpopr_rtri >> p_type >> reduce r_type    (* maybe not shift *)
  | T.QUESTION => ST |> shift >> p_con_dot >> p_type >> reduce r_type
  | T.EXCLAMATION => ST |> shift >> p_con_dot >> p_type >> reduce r_type
  | T.IDENT(id) => ST |> p_id_idx_seq >> reduce r_type
  | t => error_expected_list (here ST, [T.NAT(1), T.PLUS, T.AMPERSAND, T.BACKQUOTE,
                                        T.LPAREN, T.LBRACKET, T.LANGLE, T.BAR,
                                        T.QUESTION, T.EXCLAMATION, T.IDENT("<id>")], t)

(* ')' | <idx> ')' *)
(* follows '(' to parse circle *)
and p_tpopr_next ST = case first ST of
    T.RPAREN => ST |> shift
  | T.LBRACE => ST |> p_idx >> p_terminal T.RPAREN
  | t => error_expected_list (here ST, [T.RPAREN, T.LBRACE], t)

(* '>' | '|' | <idx> '|' *)
(* follows '<' to parse diamond or left triangle *)
and p_tpopr_dia_ltri ST = case first ST of
    T.RANGLE => ST |> shift
  | T.BAR => ST |> shift
  | T.LBRACE => ST |> p_idx >> p_terminal T.BAR
  | t => error_expected_list (here ST, [T.RANGLE, T.BAR, T.LBRACE], t)

(* '>' | <idx> '>' *)
(* follows '|' to parse right triangle *)
and p_tpopr_rtri ST = case first ST of
    T.RANGLE => ST |> shift
  | T.LBRACE => ST |> p_idx >> p_terminal T.RANGLE
  | t => error_expected_list (here ST, [T.RANGLE, T.LBRACE], t)

(* <con> '.' *)
and p_con_dot ST = case first ST of
    T.LBRACE => ST |> shift >> p_prop >> p_terminal T.RBRACE >> reduce r_con >> p_terminal T.PERIOD
  | t => error_expected (here ST, T.LBRACE, t)

(* reduce <con> ::= '{' <prop> '}' *)
and r_con (S $ Tok(T.LBRACE,r1) $ Prop(phi,_) $ Tok(T.RBRACE,r2)) = S $ Prop(phi,join r1 r2)

(* <prop> *)
and p_prop ST = ST |> p_arith >> p_rel >> p_arith >> reduce r_prop

(* reduce <prop> *)
and r_prop (S $ Arith(e1,r1) $ Tok(T.EQ,_) $ Arith(e2,r2)) = S $ Prop(R.Eq(e1,e2),join r1 r2)
  | r_prop (S $ Arith(e1,r1) $ Tok(T.RANGLE,_) $ Arith(e2,r2)) = S $ Prop(R.Gt(e1,e2),join r1 r2)
  | r_prop (S $ Arith(e1,r1) $ Tok(T.LANGLE,_) $ Arith(e2,r2)) = S $ Prop(R.Lt(e1,e2),join r1 r2)
  | r_prop (S $ Arith(e1,r1) $ Tok(T.GEQ,_) $ Arith(e2,r2)) = S $ Prop(R.Ge(e1,e2),join r1 r2)
  | r_prop (S $ Arith(e1,r1) $ Tok(T.LEQ,_) $ Arith(e2,r2)) = S $ Prop(R.Le(e1,e2),join r1 r2)
  | r_prop (S $ Arith(e1,r1) $ Tok(t,r) $ Arith(e2,r2)) = parse_error(r, "unrecognized operator, only '>' or '=' allowed ")
  | r_prop (S $ Arith(e1,r1) $ Arith(e2,r2)) = parse_error (join r1 r2, "consecutive arithmetic expressions")
  | r_prop (S $ Arith(e,r1) $ Tok(t,r2)) = parse_error (join r1 r2, "no trailing arithmetic expression")
  | r_prop (S $ Tok(t,r1) $ Arith(e,r2)) = parse_error (join r1 r2, "no leading arithmetic expression")
  | r_prop (S $ Arith(e,r)) = parse_error (r, "only one arithmetic expression")
  | r_prop (S $ Tok(_,r)) = parse_error (r, "no arithmetic expression")

(* <rel> *)
and p_rel ST = case first ST of
    T.RANGLE => ST |> shift
  | T.EQ => ST |> shift
  | T.GEQ => ST |> shift
  | T.LEQ => ST |> shift
  | T.LANGLE => ST |> shift
  | t => error_expected_list (here ST, [T.RANGLE, T.EQ, T.GEQ, T.LEQ, T.LANGLE], t)

(* <type_opt> *)
and p_type_opt ST = case first ST of
    T.PERIOD => ST |> shift >> reduce r_type
  | _ => p_type ST                              

(* reduce <type> *)
and r_type (S $ Tok(T.NAT(1),r)) = S $ Tp(A.One, r)
  | r_type (S $ Tok(T.PLUS,r1) $ Tok(T.LBRACE,_) $ Alts(alts) $ Tok(T.RBRACE,r2)) =
    S $ Tp(A.Plus(alts), join r1 r2)
  | r_type (S $ Tok(T.AMPERSAND,r1) $ Tok(T.LBRACE,_) $ Alts(alts) $ Tok(T.RBRACE,r2)) =
    S $ Tp(A.With(alts), join r1 r2)
  | r_type (S $ Tok(T.BACKQUOTE,r1) $ Tp(tp,r2)) = S $ Tp(A.Next(R.Int(1),tp), join r1 r2)
  | r_type (S $ Tok(T.LPAREN,r1) $ Tok(T.RPAREN,_) $ Tp(tp,r2)) = S $ Tp(A.Next(R.Int(1),tp), join r1 r2)
  | r_type (S $ Tok(T.LPAREN,r1) $ Arith(t,_) $ Tok(T.RPAREN,_) $ Tp(tp,r2)) = S $ Tp(A.Next(t,tp), join r1 r2)
  | r_type (S $ Tok(T.LBRACKET,r1) $ Tok(T.RBRACKET,_) $ Tp(tp,r2)) = S $ Tp(A.Box(tp), join r1 r2)
  | r_type (S $ Tok(T.LANGLE,r1) $ Tok(T.RANGLE,_) $ Tp(tp,r2)) = S $ Tp(A.Dia(tp), join r1 r2)
  | r_type (S $ Tok(T.LANGLE,r1) $ Tok(T.BAR,_) $ Tp(tp, r2)) = S $ Tp(A.GetPot(R.Int(1),tp), join r1 r2)
  | r_type (S $ Tok(T.LANGLE,r1) $ Arith(p,_) $ Tok(T.BAR,_) $ Tp(tp, r2)) = S $ Tp(A.GetPot(p,tp), join r1 r2)
  | r_type (S $ Tok(T.BAR,r1) $ Tok(T.RANGLE,_) $ Tp(tp, r2)) = S $ Tp(A.PayPot(R.Int(1),tp), join r1 r2)
  | r_type (S $ Tok(T.BAR,r1) $ Arith(p,_) $ Tok(T.RANGLE,_) $ Tp(tp, r2)) = S $ Tp(A.PayPot(p,tp), join r1 r2)
  | r_type (S $ Tok(T.QUESTION,r1) $ Prop(phi,_) $ Tok(T.PERIOD,_) $ Tp(tp,r2)) = S $ Tp(A.Exists(phi,tp), join r1 r2)
  | r_type (S $ Tok(T.EXCLAMATION,r1) $ Prop(phi,_) $ Tok(T.PERIOD,_) $ Tp(tp,r2)) = S $ Tp(A.Forall(phi,tp), join r1 r2)
  | r_type (S $ Tok(T.IDENT(id),r1) $ Indices(l,r2)) = S $ Tp(A.TpName(id,l),join r1 r2)
  | r_type (S $ Tok(T.PERIOD,r)) = S $ Tp(A.Dot,r) (* only for lhs of turnstile *)
  (* should be the only possibilities *)

(* <choices> *)
(* Alts (_) accumulates alternative choices *)
and p_choices ST =
    ST |> p_terminal T.LBRACE >> push (Alts(nil)) >> p_choices1 >> p_terminal T.RBRACE
and p_choices1 ST = ST |> p_id >> p_terminal T.COLON >> p_type >> reduce r_choices >> p_choices2
and p_choices2 ST = case first ST of
    T.RBRACE => ST (* do not shift reduce *)
  | T.COMMA => ST |> drop >> p_choices1
  | t => error_expected_list (here ST, [T.RBRACE, T.COMMA], t)

(* reduce <choices> *) 
and r_choices (S $ Alts(alts) $ Tok(T.IDENT(id),r1) $ Tok(T.COLON,_) $ Tp(tp,r2)) = S $ Alts(alts @ [(id,tp)])
    (* should be the only possibility *)

and m_exp (exp, r) = mark_exp (exp, r)

(* <exp> *)
and p_exp ST = case first ST of
    T.IDENT(id) => ST |> shift >> p_fwd_or_spawn_or_label_send_or_chan_recv_or_shared
  | T.CASE => ST |> shift >> p_id >> p_terminal T.LPAREN >> push (Branches []) >> p_branches >> p_terminal T.RPAREN >> reduce r_exp_atomic >> p_exp
  | T.CLOSE => ST |> shift >> p_id >> reduce r_exp_atomic >> p_exp
  | T.WAIT => ST |> shift >>p_id >> p_terminal T.SEMICOLON >> reduce r_action >> p_exp
  | T.LPAREN => ST |> shift >> p_exp >> p_terminal T.RPAREN >> reduce r_exp_atomic >> p_exp
  | T.DELAY => ST |> shift >> p_idx_opt >> p_exp
  (* rest needed for explicit syntax *)
  | T.TICK =>  ST |> shift >> p_terminal T.SEMICOLON >> reduce r_action >> p_exp
  | T.WHEN => ST |> shift >> p_id >> p_terminal T.SEMICOLON >> reduce r_action >> p_exp
  | T.NOW =>  ST |> shift >> p_id >> p_terminal T.SEMICOLON >> reduce r_action >> p_exp
  (* expressions for work analysis *)
  | T.WORK => ST |> shift >> p_idx_opt >> p_exp
  | T.PAY => ST |> shift >> p_id >> p_idx_opt >> p_exp
  | T.GET => ST |> shift >> p_id >> p_idx_opt >> p_exp
  (* asserts and assumes for propositions *)
  | T.ASSERT => ST |> shift >> p_id >> p_con_semi >> p_exp
  | T.ASSUME => ST |> shift >> p_id >> p_con_semi >> p_exp
  | T.IMPOSSIBLE => ST |> shift >> p_id >> p_con >> p_exp
  (* end of expression; do not consume token *)
  | t => ST |> reduce r_exp

and p_fwd_or_spawn_or_label_send_or_chan_recv_or_shared ST = case first ST of
    T.PERIOD => ST |> shift >> p_id >> p_terminal T.SEMICOLON >> reduce r_action >> p_exp
  | T.LARROW => ST |> shift >> p_fwd_or_spawn_or_recv_or_shared
  | t => error_expected_list (here ST, [T.PERIOD, T.LARROW], t)

and p_fwd_or_spawn_or_recv_or_shared ST = ST |> p_id >> p_fwd_or_spawn

and p_fwd_or_spawn ST = case first ST of
    T.LARROW => ST |> push (Indices(nil, here ST)) >> shift >> push (Args ([], here ST)) >> p_id_list_opt_exp
  | T.LBRACE => ST |> push (Indices(nil, here ST)) >> p_idx_seq >> shift >> push (Args ([], here ST)) >> p_id_list_opt_exp
  | _ => ST |> reduce r_exp_atomic >> p_exp

and p_id_list_opt_exp ST = case first ST of
    T.IDENT(_) => ST |> p_id >> reduce r_arg >> p_id_list_opt_exp
  | T.SEMICOLON => ST |> shift >> reduce r_action >> p_exp
  | _ => ST |> reduce r_exp_atomic >> p_exp

(* [<idx>] postfix of action, default is 1 *)
and p_idx_opt ST = case first ST of
    T.SEMICOLON => ST |> push (Arith(R.Int(1), here ST)) >> shift >> reduce r_action
  | T.LBRACE => ST |> p_idx >> p_terminal T.SEMICOLON >> reduce r_action
  | t => error_expected_list (here ST, [T.SEMICOLON, T.LBRACE], t)

(* <con> ';' as postfix of 'assert'<dir> and 'assume'<dir> *)
and p_con_semi ST = case first ST of
    T.LBRACE => ST |> shift >> p_prop >> p_terminal T.RBRACE >> reduce r_con >> p_terminal T.SEMICOLON >> reduce r_action
  | t => error_expected (here ST, T.LBRACE, t)

(* <con> ::= '{' <prop> '}' as postfix of 'impossible'<dir> *)
and p_con ST = case first ST of
    T.LBRACE => ST |> shift >> p_prop >> p_terminal T.RBRACE >> reduce r_con >> reduce r_exp_atomic

(* reduce <exp>, where <exp> has no continuation (atomic expressions) *)
and r_exp_atomic (S $ Tok(T.CLOSE,r1) $ Tok(T.IDENT(id),r2)) = S $ Exp(m_exp(A.Close(id),join r1 r2),join r1 r2)
  | r_exp_atomic (S $ Tok(T.IDENT(x),r1) $ Tok(T.LARROW,_) $ Tok(T.IDENT(id),_) $ Indices(l,_) $ Tok(T.LARROW,_) $ Args(xs,r2)) = S $ Exp(m_exp(A.ExpName(x,id,l,xs),join r1 r2),join r1 r2)
  | r_exp_atomic (S $ Tok(T.LPAREN,r1) $ Exp(exp,r) $ Tok(T.RPAREN,r2)) = S $ Exp(exp,join r1 r2)
  | r_exp_atomic (S $ Tok(T.CASE,r1) $ Tok(T.IDENT(id),_) $ Tok(T.LPAREN,_) $ Branches(branches) $ Tok(T.RPAREN,r2)) =
    S $ Exp(m_exp(A.Case(id,branches),join r1 r2),join r1 r2)
  | r_exp_atomic (S $ Tok(T.IMPOSSIBLE,r1) $ Tok(T.IDENT(id),_) $ Prop(phi,r2)) =
    S $ Exp(m_exp(A.Assume(id,phi,A.Imposs),join r1 r2),join r1 r2)
  | r_exp_atomic (S $ Tok(T.IDENT(id1),r1) $ Tok(T.LARROW,r) $ Tok(T.IDENT(id2),r2) ) = S $ Exp(m_exp(A.Id(id1,id2),join r1 r2), join r1 r2)
  (* should be the only atomic expressions *)

(* reduce <exp>, possibly multiple actions, cuts, or expressions *)
(* stack ends with Action, Cut, or Exp items *)
and r_exp (S $ Action(act,r1) $ Exp(exp,r2)) = r_exp (S $ Exp(act(exp), join r1 r2))
  | r_exp (S $ Action(act, r)) = parse_error (r, "incomplete action")
  | r_exp (S $ Exp(exp1,r1) $ Exp(exp2,r2)) = parse_error (join r1 r2, "consecutive expressions")
  (* done reducing *)
  | r_exp (S $ Exp(exp,r)) = S $ Exp(exp,r)

(* reduce action prefix of <exp> *)
and r_action (S $ Tok(T.IDENT(x),r1) $ Tok(T.PERIOD,_) $ Tok(T.IDENT(id),r2) $ Tok(T.SEMICOLON,r3)) =
    S $ Action((fn K => m_exp(A.Lab(x,id,K),join r1 r2)), join r1 r3)
  | r_action (S $ Tok(T.WAIT,r1) $ Tok(T.IDENT(id),_) $ Tok(T.SEMICOLON,r2)) =
    S $ Action((fn K => m_exp(A.Wait(id,K),r1)), join r1 r2)
  | r_action (S $ Tok(T.DELAY,r1) $ Arith(t,_) $ Tok(T.SEMICOLON,r2)) =
    S $ Action((fn K => m_exp(A.Delay(t,K),r1)), join r1 r2)
  | r_action (S $ Tok(T.TICK,r1) $ Tok(T.SEMICOLON,r2)) =
    S $ Action((fn K => m_exp(A.Delay(R.Int(1),K),r1)), join r1 r2)
  | r_action (S $ Tok(T.WHEN,r1) $ Tok(T.IDENT(id),_) $ Tok(T.SEMICOLON,r2)) =
    S $ Action((fn K => m_exp(A.When(id,K),r1)), join r1 r2)
  | r_action (S $ Tok(T.NOW,r1) $ Tok(T.IDENT(id),_) $ Tok(T.SEMICOLON,r2)) =
    S $ Action((fn K => m_exp(A.Now(id,K),r1)), join r1 r2)
  | r_action (S $ Tok(T.WORK,r1) $ Arith(pot,_) $ Tok(T.SEMICOLON,r2)) =
    S $ Action((fn K => m_exp(A.Work(pot,K),r1)), join r1 r2)
  | r_action (S $ Tok(T.PAY,r1) $ Tok(T.IDENT(id),_) $ Arith(pot,_) $ Tok(T.SEMICOLON,r2)) =
    S $ Action((fn K => m_exp(A.Pay(id,pot,K),r1)), join r1 r2)
  | r_action (S $ Tok(T.GET,r1) $ Tok(T.IDENT(id),_) $ Arith(pot,_) $ Tok(T.SEMICOLON,r2)) =
    S $ Action((fn K => m_exp(A.Get(id,pot,K),r1)), join r1 r2)
  | r_action (S $ Tok(T.ASSERT,r1) $ Tok(T.IDENT(id),_) $ Prop(phi,_) $ Tok(T.SEMICOLON,r2)) =
    S $ Action((fn K => m_exp(A.Assert(id,phi,K),r1)), join r1 r2)
  | r_action (S $ Tok(T.ASSUME,r1) $ Tok(T.IDENT(id),_) $ Prop(phi,_) $ Tok(T.SEMICOLON,r2)) =
    S $ Action((fn K => m_exp(A.Assume(id,phi,K),r1)), join r1 r2)
  | r_action (S $ Tok(T.IDENT(x),r1) $ Tok(T.LARROW,_) $ Tok(T.IDENT(f),_) $ Indices(es,_) $ Tok(T.LARROW,_) $ Args(xs,r2) $ Tok(T.SEMICOLON,r3)) =
    S $ Action((fn K => m_exp(A.Spawn(A.ExpName(x,f,es,xs),K), join r1 r2)), join r1 r3)

(* <branches> *)
and p_branches ST = case first ST of
    T.IDENT(id) => ST |> shift >> p_terminal T.RARROW >> p_exp >> reduce r_branch >> p_branches2
  | t => error_expected (here ST, T.IDENT("<label>"), t)
and p_branches2 ST = case first ST of
    T.RPAREN => ST (* branches complete; do not shift or reduce *)
  | T.BAR => ST |> drop >> p_branches
  | t => error_expected_list (here ST, [T.BAR,T.RPAREN], t)

(* reduce <branches> *)
and r_branch (S $ Branches(branches) $ Tok(T.IDENT(id),r1) $ Tok(T.RARROW,_) $ Exp(exp,r2)) =
    S $ Branches(branches @ [(id,PS.ext(r1),exp)])
    (* should be the only possibility *)

(* <id> *)
and p_id ST = case first ST of
    T.IDENT(id) => ST |> drop >> push (Tok(T.IDENT(id), here ST))
  | t => parse_error (here ST, "expected identifier, found " ^ pp_tok t)

(* parse any token (terminal symbol) 't_needed' *)
and p_terminal t_needed ST = case first ST of
    t => if t_needed = t
	 then ST |> shift
	 else error_expected (here ST, t_needed, t)

and p_terminal_h t_needed error_hint ST = case first ST of
    t => if t_needed = t
	 then ST |> shift
	 else error_expected_h (here ST, t_needed, t, error_hint)

(* (<pragma> | <decl>)* *)
fun parse_decls token_front =
    let val ST = p_decl (Bot, token_front)
        val () = if !ErrorMsg.anyErrors then raise ErrorMsg.Error else ()
    in
        case ST
         of (Bot, M.Cons((T.EOF, r), token_front)) => []
            (* whole file processed *)
          | (Bot $ Decl(decl), token_front) =>
            decl :: parse_decls token_front
          (* should be the only possibilities *)
    end

(* parse filename = decls
 * first apply lexer, the parser to the resulting token stream
 * raise ErrorMsg.Error if not lexically or syntactically correct
 * or if file does not exist or cannot be opened
 *)
fun parse filename =
    SafeIO.withOpenIn filename (fn instream =>
      let val () = PS.pushfile filename (* start at pos 0 in filename *)
          val token_stream = Lex.makeLexer (fn _ => TextIO.input instream)
          val decls = parse_decls (M.force token_stream)
          val () = PS.popfile ()
      in decls end)
    handle e as IO.Io _ => ( ErrorMsg.error NONE (exnMessage e)
                           ; raise ErrorMsg.Error )

(* <pragma>*, ignoring remainder of token stream *)
fun parse_preamble_decls token_front =
    let
        val ST = p_decl (Bot, token_front) (* may raise ErrorMsg.Error *)
    in
        case ST
         of (Bot $ Decl(decl as A.Pragma _), token_front) =>
            (* part of preamble *)
            decl :: parse_preamble_decls token_front
          | (Bot $ _, token_front) =>
            (* either end of file or declaration which is not a pragma *)
            nil
    end handle ErrorMsg.Error => nil (* turn error into nil *)

(* parse preamble = pragmas *)
fun parse_preamble filename =
    SafeIO.withOpenIn filename (fn instream =>
      let val () = PS.pushfile filename
          val token_stream = Lex.makeLexer (fn _ => TextIO.input instream)
          val pragmas = parse_preamble_decls (M.force token_stream)
          val () = PS.popfile ()
      in
          pragmas
      end)
    (* may raise IO.Io _, must be handled by caller *)

end (* structure Parse *)
