(* Parser *)
(* Authors: Ankush Das <ankushd@cs.cmu.edu>
 *          Frank Pfenning <fp@cs.cmu.edu>
 *)

(*
 * Handwritten shift/reduce parser to support
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

(* operator precedence, for arithmetic *)
type prec = int

(* Valid occurrences of infix operators are always preceded by
 * an expression which must have already been reduced; valid
 * occurrences of prefix operators never are.  This helps to
 * disambiguate '-' (prefix or infix)
 *)
datatype assoc = Left | Right | Non

(* Arithmetic expressions are parsed using an operator
 * precedence parser, mixing propositions and terms.
 * Therefore we create something of type 'aexp'
 *)
datatype aexp = Prop of R.prop | Arith of R.arith

(* stack items for shift/reduce parsing *)
datatype stack_item =
   Tok of T.terminal * region                                   (* lexer token *)

 | Infix of prec * assoc * T.terminal * region * (aexp * aexp -> aexp) (* arithmetic infix operator *)
 | Prefix of prec * T.terminal * region * (aexp -> aexp)        (* arithmetic prefix operator *)
 | Nonfix of T.terminal * region
 | AExp of aexp * region                                        (* arithmetic expression *)

 | Vars of (R.varname * R.prop) list * region                   (* list of variables with constraints *)
 | Indices of R.arith list * region                             (* list of index expressions *)

 | TpVars of A.tpvarname list * region                          (* list of type variables *)
 | Tps of A.tp list * region                                    (* list of types *)

 | Tp of A.tp * region                                          (* types *)
 | TpInfix of prec * (A.tp * A.tp -> A.tp) * region             (* infix tensor and lolli type operators *)

 | Alts of A.choices                                            (* list of alternatives in types *)
 | Action of (A.exp -> A.exp) * region                          (* prefix process action *)
 | Chans of (A.chan list) * region                              (* channel list *)

 | Exp of A.exp * region                                        (* process expression *)
 | Branches of A.branches                                       (* list of branches *)

 | Context of (A.chan * A.tp) list * region                     (* context *)
 | Decl of A.decl                                               (* top-level declaration *)

datatype stack
  = Bot
  | $ of stack * stack_item

infix 2 $

(* Next section gives a static error while trying to
 * construct either a term or a proposition from an
 * arithmetic expression
 *)
fun arith2 r f (Arith(e1), Arith(e2)) = Arith(f(e1,e2))
  | arith2 r f (Prop(phi1), _) = parse_error (r, "applying arithmetic operator to proposition")
  | arith2 r f (_, Prop(phi2)) = parse_error (r, "applying arithmetic operator to proposition")

fun arith1 r f (Arith(e)) = Arith(f(e))
  | arith1 r f (Prop(phi)) = parse_error (r, "applying arithmetic operator to proposition")

fun rel2 r f (Arith(e1), Arith(e2)) = Prop(f(e1,e2))
  | rel2 r f (Prop(phi1), _) = parse_error (r, "applying relational operator to proposition")
  | rel2 r f (_, Prop(phi2)) = parse_error (r, "applying relational operator to proposition")

fun prop2 r f (Prop(phi1), Prop(phi2)) = Prop(f(phi1,phi2))
  | prop2 r f (Arith(e1), _) = parse_error (r, "applying propositional operator to arithmetic expression")
  | prop2 r f (_, Arith(e2)) = parse_error (r, "applying propositional operator to arithmetic expression")

fun prop1 r f (Prop(phi)) = Prop(f(phi))
  | prop1 r f (Arith(e)) = parse_error (r, "applying propositional operator to arithmetic expression")

fun aexp2prop r (Prop(phi)) = phi
  | aexp2prop r (Arith(e)) = parse_error (r, "expected proposition, found arithmetic expression")

fun aexp2arith r (Arith(e)) = e
  | aexp2arith r (Prop(phi)) = parse_error (r, "expected arithmetic expression, found proposition")

(* precedes_infix S = true if S could be legal stack while
 * looking at an infix operator
 *)
fun precedes_infix (S $ AExp _) = true
  | precedes_infix _ = false

(* arithmetic prefix and infix operators *)
(* each with precedence, associativity, region, and abstract syntax constructor *)
fun opr (S, t, r) = case t of
    T.MINUS => if precedes_infix S
               then Infix(7, Left, t, r, arith2 r R.Sub)
               else Prefix(9, t, r, arith1 r (fn e => R.Sub(R.Int(0),e)))
  | T.STAR => Infix(8, Left, t, r, arith2 r R.Mult)
  | T.PLUS => Infix(7, Left, t, r, arith2 r R.Add)
(*  T.MINUS => Infix(7 t, r, R.Sub) see above) *)
  | T.EQ => Infix(6, Non, t, r, rel2 r R.Eq)
  | T.LANGLE => Infix(6, Non, t, r, rel2 r R.Lt)
  | T.RANGLE => Infix(6, Non, t, r, rel2 r R.Gt)
  | T.LEQ => Infix(6, Non, t, r, rel2 r R.Le)
  | T.GEQ => Infix(6, Non, t, r, rel2 r R.Ge)
  | T.NEQ => Infix(6, Non, t, r, rel2 r (fn (e1,e2) => R.Not(R.Eq(e1,e2))))
  | T.NOT => Prefix(5, t, r, prop1 r R.Not)
  | T.AND => Infix(4, Right, t, r, prop2 r R.And)
  | T.OR => Infix(3, Right, t, r, prop2 r R.Or)
  | T.RARROW => Infix(2, Right, t, r, prop2 r R.Implies)
  | _ => Nonfix(t, r)

fun left_assoc Left = true
  | left_assoc _ = false

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
    T.TYPE => ST |> shift >> p_id_parm_seq >> p_eq_type >> reduce r_decl
  | T.EQTYPE => ST |> shift >> p_eqtype >> reduce r_decl
  | T.DECL => ST |> shift >> p_id_parm_seq >> p_exp_decl >> reduce r_decl
  | T.PROC => ST |> shift >> p_exp_def >> reduce r_decl
  | T.EXEC => ST |> shift >> p_id >> reduce r_decl
  | T.PRAGMA _ => ST |> shift >> reduce r_decl
  | T.EOF => ST
  | t => parse_error (here ST, "unexpected token " ^ pp_tok t ^ " at top level")

(* <id> <parm_seq> *)
(* TpVars(_,r) accumulates the ast for <tpvar_seq> *)
and p_id_parm_seq ST = ST |> p_id >> push (TpVars(nil, here ST)) >> p_parm_seq
and p_parm_seq ST = case first ST of
    T.LBRACKET => ST |> shift >> p_id >> p_terminal T.RBRACKET >> reduce r_tpvar_seq >> p_parm_seq
  | t => ST |> push (Vars(nil, here ST)) >> p_var_seq

(* <var_seq> *)
and p_var_seq ST = case first ST of
    T.LBRACE => ST |> shift >> p_var_prop >> p_terminal T.RBRACE >> reduce r_var_seq >> p_var_seq
  | t => ST

(* <var> |  <var> '|' <prop> *) 
and p_var_prop ST = ST |> p_id >> p_bar_prop_opt

(* ['|' <prop>] *)
and p_bar_prop_opt ST = case first ST of
    T.BAR => ST |> drop >> p_aexp (* !! *)
  | _ => ST

(* accumulate type variables alpha *)
and r_tpvar_seq (S $ TpVars(alphas,r1) $ Tok(T.LBRACKET,_) $ Tok(T.IDENT(alpha),_) $ Tok(T.RBRACKET,r2)) =
    S $ TpVars(alphas @ [alpha], join r1 r2)

(* accumulate (v,phi) for every variable v and constraint phi (defaults to 'true') *)
and r_var_seq (S $ Vars(l,r1) $ Tok(T.LBRACE,_) $ Tok(T.IDENT(v),_) $ AExp(e,r) $ Tok(T.RBRACE,r2)) =
    S $ Vars(l @ [(v,aexp2prop r e)], join r1 r2)
  | r_var_seq (S $ Vars(l,r1) $ Tok(T.LBRACE,_) $ Tok(T.IDENT(v),_) $ Tok(T.RBRACE,r2)) =
    S $ Vars(l @ [(v,R.True)], join r1 r2)

(* <id> <arg_seq> *)
(* Tps(As,r) accumulates the type arguments *)
and p_id_arg_seq ST = ST |> p_id >> push (Tps(nil, here ST)) >> p_arg_seq

(* <arg_seq> *)
and p_arg_seq ST = case first ST of
    T.LBRACKET => ST |> shift >> p_type >> p_terminal T.RBRACKET >> reduce r_type_seq >> p_arg_seq
  | _ => ST |> push (Indices(nil, here ST)) >> p_idx_seq

(* <id> <idx_seq> *)
(* Indices(_,r) accumulates the ast for <idx_seq> *)
and p_id_idx_seq ST = ST |> p_id >> push (Indices(nil, here ST)) >> p_idx_seq

(* <idx_seq> *)
and p_idx_seq ST = case first ST of
    T.LBRACE => ST |> p_idx >> reduce r_idx_seq >> p_idx_seq
  | t => ST

(* accumulate e into sequence of indices *)
and r_idx_seq (S $ Indices(l,r1) $ AExp(e,r2)) = S $ Indices(l @ [aexp2arith r2 e], join r1 r2)

(* '=' <type> *)
and p_eq_type ST = case first ST of
    T.EQ => ST |> shift >> p_type
  | t => error_expected (here ST, T.EQ, t)

(* <id> <arg_seq> '=' <id> <arg_seq> *)
and p_eqtype ST = ST |> p_id_arg_seq >> p_terminal T.EQ >> p_id_arg_seq

(* ':' ( <ctx> | '.' ) <turnstile> '(' <id> ':' <type> ')' *)
and p_exp_decl ST = case first ST of
    T.COLON => ST |> shift >> p_ctx_opt >> p_turnstile_id_tp
  | t => error_expected (here ST, T.COLON, t)

(* '.' | <ctx> *)
and p_ctx_opt ST = case first ST of
    T.PERIOD => ST |> drop >> push (Context([], here ST))
  | T.LPAREN => ST |> push (Context([], here ST)) >> p_ctx
  | t => error_expected_list (here ST, [T.PERIOD, T.LPAREN], t)

(* '(' <id> ':' <type> ')' [<ctx>] *)
and p_ctx ST = ST |> p_terminal T.LPAREN >> p_id >> p_terminal T.COLON >> p_type
                      >> p_terminal T.RPAREN >> reduce r_chan_tp >> p_ctx2

(* [<ctx>] *)
and p_ctx2 ST = case first ST of
    T.LPAREN => ST |> p_ctx
  | T.TURNSTILE => ST
  | T.BAR => ST
  | t => error_expected_list (here ST, [T.LPAREN, T.TURNSTILE, T.BAR], t)

and r_chan_tp (S $ Context(ctx, r) $ Tok(T.LPAREN, _) $ Tok(T.IDENT(id), _) $ Tok(T.COLON,_) $ Tp(tp,_) $ Tok(T.RPAREN, r2)) =
    S $ Context(ctx @ [(id,tp)], join r r2)

(* <turnstile> '(' <id> : <type> ')' *)
and p_turnstile_id_tp ST = case first ST of
    T.TURNSTILE => ST |> shift >> p_id_tp
  | T.BAR => ST |> shift >> p_idx >> p_terminal T.MINUS >> p_id_tp
  | t => error_expected_list (here ST, [T.TURNSTILE, T.BAR], t)

(* '(' <id> ':' <type> ')' *)
and p_id_tp ST = ST |> p_terminal T.LPAREN >> p_id >> p_terminal T.COLON >> p_type >> p_terminal T.RPAREN

(* <id> <- <id> <parm_seq> <id_seq> = <exp> *)
and p_exp_def ST = ST |> p_id >> p_terminal T.LARROW >> p_id_parm_seq
                      >> push (Chans ([], here ST)) >> p_id_seq_exp

(* <id_seq> '=' <exp> *)
and p_id_seq_exp ST = case first ST of
    T.IDENT(_) => ST |> p_id >> reduce r_chan >> p_id_seq_exp
  | T.EQ => ST |> shift >> p_actions
  | t => parse_error (here ST, "expected '=' or identifier, found: " ^ pp_tok t)

and r_chan (S $ Chans(args, r1) $ Tok(T.IDENT(id), r2)) = S $ Chans(args @ [id], join r1 r2)

(* reduce top-level declaration *)
(* split in pieces to work around mlton compiler performance bug *)
and r_decl S = r_decl_1 S
and r_decl_1 (S $ Tok(T.TYPE,r1) $ Tok(T.IDENT(id),_) $ TpVars(alphas,_) $ Vars(l,_) $ Tok(T.EQ,_) $ Tp(tp,r2)) =
    (* 'type' <id> <parm_seq> = <type> *)
    S $ Decl(A.TpDef(id,alphas,vars l,phis l,tp,PS.ext(join r1 r2)))
  | r_decl_1 (S $ Tok(T.EQTYPE,r1) $ Tok(T.IDENT(id1),_) $ Tps(As1,_) $ Indices(es1,_)
                $ Tok(T.EQ,_) $ Tok(T.IDENT(id2),_) $ Tps(As2,_) $ Indices(es2, r2)) =
    (* 'eqtype' <id> <arg_seq> = <id> <arg_seq> *)
    S $ Decl(A.TpEq([],[],R.True,A.TpName(id1,As1,es1),A.TpName(id2,As2,es2),PS.ext(join r1 r2)))
  | r_decl_1 (S $ Tok(T.DECL,r1) $ Tok(T.IDENT(id),_) $ TpVars(alphas,_) $ Vars(l,_) $ Tok(T.COLON,_)
                $ Context(ctx,_) $ Tok(T.TURNSTILE,_)
                $ Tok(T.LPAREN,_) $ Tok(T.IDENT(c),_) $ Tok(T.COLON,_) $ Tp(tp,_) $ Tok(T.RPAREN,r2)) =
    (* 'decl' <id> <parm_seq> : <ctx> |- <id> : <type> *)
    S $ Decl(A.ExpDec(id,alphas,vars l,phis l,(ctx,R.Int(0),(c,tp)), PS.ext(join r1 r2)))
  | r_decl_1 S = r_decl_2 S

and r_decl_2 (S $ Tok(T.DECL,r1) $ Tok(T.IDENT(id),_) $ TpVars(alphas,_) $ Vars(l,_) $ Tok(T.COLON,_)
                $ Context(ctx,_) $ Tok(T.BAR,_) $ AExp(pot,r) $ Tok(T.MINUS,_)
                $ Tok(T.LPAREN,_) $ Tok(T.IDENT(c),_) $ Tok(T.COLON,_) $ Tp(tp,_) $ Tok(T.RPAREN,r2)) =
    (* 'decl' <id> <parm_seq> : <ctx> '|{' <arith> '}-' <id> : <type> *)
    S $ Decl(A.ExpDec(id,alphas,vars l,phis l,(ctx,aexp2arith r pot,(c,tp)), PS.ext(join r1 r2)))
  | r_decl_2 (S $ Tok(T.PROC,r1) $ Tok(T.IDENT(x),_) $ Tok(T.LARROW,_) $ Tok(T.IDENT(id),_) $ TpVars(alphas, _) $ Vars(l,r)
                $ Chans(xs,_) $ Tok(T.EQ,_) $ Exp(exp,r2)) =
    (* 'proc' <id> '<-' <id> <parm_seq> <id_seq> = <exp> *)
    (case (phis l)
     of R.True => S $ Decl(A.ExpDef(id,alphas,vars l,(xs, exp, x),PS.ext(join r1 r2)))
      | _ => parse_error (r, "constraint found in process definition"))
  | r_decl_2 (S $ Tok(T.EXEC,r1) $ Tok(T.IDENT(id),r2)) =
    (* 'exec' <id> *)
    S $ Decl(A.Exec(id, PS.ext(join r1 r2)))
  | r_decl_2 (S $ Tok(T.PRAGMA(p,line),r)) =
    (* '#' <line> '\n' *)
    S $ Decl(A.Pragma(p,line,PS.ext(r)))
  (* should be the only possibilities *)

(* <idx> ::= '{' <arith> '}' *)
and p_idx ST = case first ST of
    T.LBRACE => ST |> shift >> p_aexp >> p_terminal T.RBRACE >> reduce r_idx
  | t => error_expected (here ST, T.LBRACE, t)

(* reduce '{' <arith> '}' *)
and r_idx (S $ Tok(T.LBRACE,r1) $ AExp(e, _) $ Tok(T.RBRACE,r2)) = S $ AExp (e, join r1 r2)

(* <type> *)
and p_type ST = case first ST of
    T.NAT(1) => ST |> shift >> reduce r_type >> p_type
  | T.NAT(n) => parse_error (here ST, "expected type, found " ^ Int.toString n)
  | T.PLUS => ST |> shift >> p_choices >> reduce r_type >> p_type
  | T.AMPERSAND => ST |> shift >> p_choices >> reduce r_type >> p_type
  | T.BACKQUOTE => ST |> shift >> p_type >> reduce r_type >> p_type
  | T.LPAREN => ST |> shift >> p_next_or_type
  | T.LBRACKET => ST |> shift >> p_terminal T.RBRACKET >> p_type >> reduce r_type >> p_type
  | T.LANGLE => ST |> shift >> p_tpopr_dia_ltri >> p_type >> reduce r_type >> p_type (* maybe not shift *)
  | T.BAR => ST |> shift >> p_tpopr_rtri >> p_type >> reduce r_type >> p_type        (* maybe not shift *)
  | T.STAR => ST |> drop >> push (TpInfix(1, A.Tensor, here ST)) >> p_type_prec
  | T.LOLLI => ST |> drop >> push (TpInfix(1, A.Lolli, here ST)) >> p_type_prec
  | T.QUESTION => ST |> shift >> p_con_dot >> p_type >> reduce r_type >> p_type
  | T.EXCLAMATION => ST |> shift >> p_con_dot >> p_type >> reduce r_type >> p_type
  | T.IDENT(id) => ST |> p_id_arg_seq >> reduce r_type >> p_type
  | t => ST |> reduce r_type

(* shift/reduce decision based on operator precedence *)
and p_type_prec ST = case ST of
    (S $ Tp(tp1,r1) $ TpInfix(prec1, constr1, _) $ Tp(tp2, r2) $ TpInfix(prec, con, r), ft) =>
      if prec1 > prec         (* all type operators are right associative *)
      then p_type_prec (S $ Tp(constr1(tp1,tp2), join r1 r2) $ TpInfix(prec, con, r), ft) (* reduce *)
      else p_type ST          (* shift *)
  | (S $ Tp(_,_) $ TpInfix(_,_,_), _) => p_type ST (* shift *)
  | (S $ TpInfix(_,_,r1) $ TpInfix(_,_,r2), _) => parse_error (join r1 r2, "consecutive infix type operators")
  | (S $ TpInfix(_,_,r), _) => parse_error (r, "leading infix type operator")

(* ')' | <idx> ')' *)
(* follows '(' to parse circle *)
and p_next_or_type ST = case first ST of
    T.RPAREN => ST |> shift >> p_type >> reduce r_type >> p_type
  | T.LBRACE => ST |> p_idx >> p_terminal T.RPAREN >> p_type >> reduce r_type >> p_type
  | t => ST |> p_type >> p_terminal T.RPAREN >> reduce r_type >> p_type 

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

(* <con> '.' | <id> '.' | '[' <id> ']' '.' *)
and p_con_dot ST = case first ST of
    T.LBRACE => ST |> shift >> p_aexp >> p_terminal T.RBRACE >> reduce r_con >> p_terminal T.PERIOD
  | T.IDENT(id) => ST |> shift >> p_terminal T.PERIOD
  | T.LBRACKET => ST |> shift >> p_id >> p_terminal T.RBRACKET >> reduce r_con >> p_terminal T.PERIOD
  | t => error_expected_list (here ST, [T.LBRACKET, T.LBRACE, T.IDENT("<var>")], t)

(* reduce <con> ::= '{' <prop> '}' | '[' <id> ']' *)
and r_con (S $ Tok(T.LBRACE,r1) $ AExp(e,_) $ Tok(T.RBRACE,r2)) = S $ AExp(e, join r1 r2)
  | r_con (S $ Tok(T.LBRACKET,r1) $ Tok(T.IDENT(id), _) $ Tok(T.RBRACKET,r2)) = S $ TpVars([id], join r1 r2)

(* <arith> and <prop>, parsed as <aexp> *)
(* This needs to be a joint infix parser because we cannot
 * reliably predict if the next items we parse denote an
 * arithmetic expression or a proposition.
 *)
and c_follows_nonaexp (ST as (S, ft)) = case (S, first ST) of
    (S $ AExp(e,r), _) => parse_error (join r (here ST), "consecutive arithmetic expressions")
  | (S, _) => ST                                                              

(* arithmetic expressions *)
and p_aexp (ST as (S,ft)) = case first ST of
    T.LPAREN => ST |> c_follows_nonaexp >> shift >> p_aexp >> p_terminal T.RPAREN >> reduce r_aexp >> p_aexp
  | T.NAT(n) => ST |> c_follows_nonaexp >> shift >> reduce r_aexp >> p_aexp
  | T.IDENT(x) => ST |> c_follows_nonaexp >> shift >> reduce r_aexp >> p_aexp
  | t => (case opr (S, t, here ST)
           of Nonfix(t',r) => (* nonfix: do not consume token! *)
              ST |> p_aexp_prec (Nonfix(t',r))
            | subject => (* infix or prefix: subject includes token; use operator precedence *)
              ST |> drop >> p_aexp_prec subject)

(* p_aexp_prec subject (S, ft) compares precedence of subject to S
 * to decide if to shift, reduce, or raise an error.
 * Continue if expression could be extended by further tokens. *)
and p_aexp_prec subject (ST as (S,ft)) = case (S,subject) of

  (* looking at infix operator *)
    (S $ AExp _ $ Infix(k1, a1, t1, _, _) $ AExp _, Infix(k2, a2, t2, _, _)) =>
    if k1 > k2 orelse (k1 = k2 andalso left_assoc a1) (* left associative, a1 = a2 required *)
                               (* non-associative operators will be caught in function rel2 *)
    then ST |> reduce r_aexp >> p_aexp_prec subject (* reduce *)
    else ST |> push subject >> p_aexp               (* shift *)
  | (S $ Prefix(k1, _, _, _) $ AExp _, Infix(k2, _, _, _, _)) =>
    if k1 > k2              (* k1 <> k2 (prefix should never have same prec as infix) *)
    then ST |> reduce r_aexp >> p_aexp_prec subject (* reduce *)
    else ST |> push subject >> p_aexp               (* shift *)
  | (S $ AExp _, Infix _) => (* preceding two cases don't match: first infix *)
    ST |> push subject >> p_aexp                    (* shift *)
  (* error conditions for infix operator *)
  | (S $ Infix(_, _, t1, r1, _), Infix(_, _, t2, r2, _)) => parse_error (join r1 r2, "consecutive infix operators " ^ pp_tok t1 ^ " " ^ pp_tok t2)
  | (S $ Prefix(_, t1, r1, _), Infix(_, _, t2, r2, _)) => parse_error (join r1 r2, "prefix operator " ^ pp_tok t2 ^ " followed by infox operator " ^ pp_tok t2)
  | (S, Infix(_, _, t, r, _)) => parse_error (r, "leading infix operator " ^ pp_tok t)

  (* looking at prefix operator *)
  | (S $ AExp _, Prefix(_, t, r, _)) => parse_error (r, "prefix operator " ^ pp_tok t ^ " immediately following expression")
  | (S, Prefix(_, t, r, _)) => (* prefix operator: cannot reduce; always shift *)
    ST |> push subject >> p_aexp

  (* looking at nonfix operator (end of aexp) *)
  (* keep reducing *)
  | (S $ AExp _ $ Infix _  $ AExp _, Nonfix _) => ST |> reduce r_aexp >> p_aexp_prec subject
  | (S $          Prefix _ $ AExp _, Nonfix _) => ST |> reduce r_aexp >> p_aexp_prec subject

  (* remaining error conditions *)
  | (S $ Infix(_, _, t, r, _), Nonfix _) => parse_error (r, "trailing infix operator " ^ pp_tok t)
  | (S $ Prefix(_, t, r, _),   Nonfix _) => parse_error (r, "trailing prefix operator " ^ pp_tok t)
  | (S $ AExp _,               Nonfix _) => ST   (* already reduced *)
  | (S, Nonfix (t, r))                   => parse_error (r, "empty arithmetic expression before " ^ pp_tok t)

and r_aexp (S $ Tok(T.NAT(n), r)) = S $ AExp(Arith(R.Int(n)), r)
  | r_aexp (S $ Tok(T.IDENT(x), r)) = S $ AExp(Arith(R.Var(x)), r)
  | r_aexp (S $ Tok(T.LPAREN, r1) $ AExp(e,_) $ Tok(T.RPAREN, r2)) = S $ AExp(e, join r1 r2)
  | r_aexp (S $ AExp(e1, r1) $ Infix(_, _, _, _, constr) $ AExp(e2, r2)) = S $ AExp(constr(e1,e2), join r1 r2)
  | r_aexp (S $ Prefix(_, _, r1, constr) $ AExp(e, r2)) = S $ AExp(constr(e), join r1 r2)
  | r_aexp (S $ AExp(e,r)) = S $ AExp(e,r)  (* default case; must be last *)
  (* no other cases should be possible *)                            

(* <type_opt> *)
and p_type_opt ST = case first ST of
    T.PERIOD => ST |> shift >> reduce r_type
  | _ => p_type ST                              

(* reduce <type> *)
(* broken up into separate function to avoid mlton performance bug *)
and r_type S = r_type_1 S
and r_type_1 (S $ Tok(T.NAT(1),r)) = S $ Tp(A.One, r)
  | r_type_1 (S $ Tok(T.PLUS,r1) $ Tok(T.LBRACE,_) $ Alts(alts) $ Tok(T.RBRACE,r2)) = S $ Tp(A.Plus(alts), join r1 r2)
  | r_type_1 (S $ Tok(T.AMPERSAND,r1) $ Tok(T.LBRACE,_) $ Alts(alts) $ Tok(T.RBRACE,r2)) = S $ Tp(A.With(alts), join r1 r2)
  | r_type_1 (S $ Tok(T.BACKQUOTE,r1) $ Tp(tp,r2)) = S $ Tp(A.Next(R.Int(1),tp), join r1 r2)
  | r_type_1 (S $ Tok(T.LPAREN,r1) $ Tok(T.RPAREN,_) $ Tp(tp,r2)) = S $ Tp(A.Next(R.Int(1),tp), join r1 r2)
  | r_type_1 (S $ Tok(T.LPAREN,r1) $ AExp(t,r) $ Tok(T.RPAREN,_) $ Tp(tp,r2)) = S $ Tp(A.Next(aexp2arith r t,tp), join r1 r2)
  | r_type_1 (S $ Tok(T.LBRACKET,r1) $ Tok(T.RBRACKET,_) $ Tp(tp,r2)) = S $ Tp(A.Box(tp), join r1 r2)
  | r_type_1 (S $ Tok(T.LANGLE,r1) $ Tok(T.RANGLE,_) $ Tp(tp,r2)) = S $ Tp(A.Dia(tp), join r1 r2)
  | r_type_1 (S $ Tok(T.LANGLE,r1) $ Tok(T.BAR,_) $ Tp(tp, r2)) = S $ Tp(A.GetPot(R.Int(1),tp), join r1 r2)
  | r_type_1 (S $ Tok(T.LANGLE,r1) $ AExp(p,r) $ Tok(T.BAR,_) $ Tp(tp, r2)) = S $ Tp(A.GetPot(aexp2arith r p,tp), join r1 r2)
  | r_type_1 S = r_type_2 S
and r_type_2 (S $ Tok(T.BAR,r1) $ Tok(T.RANGLE,_) $ Tp(tp, r2)) = S $ Tp(A.PayPot(R.Int(1),tp), join r1 r2)
  | r_type_2 (S $ Tok(T.BAR,r1) $ AExp(p,r) $ Tok(T.RANGLE,_) $ Tp(tp, r2)) = S $ Tp(A.PayPot(aexp2arith r p,tp), join r1 r2)
  | r_type_2 (S $ Tok(T.QUESTION,r1) $ AExp(e,r) $ Tok(T.PERIOD,_) $ Tp(tp,r2)) = S $ Tp(A.Exists(aexp2prop r e,tp), join r1 r2)
  | r_type_2 (S $ Tok(T.QUESTION,r1) $ Tok(T.IDENT(id),_) $ Tok(T.PERIOD,_) $ Tp(tp,r2)) = S $ Tp(A.ExistsNat(id,tp), join r1 r2)
  | r_type_2 (S $ Tok(T.QUESTION,r1) $ TpVars([id],_) $ Tok(T.PERIOD,_) $ Tp(tp,r2)) = S $ Tp(A.ExistsTp(id,tp), join r1 r2)
  | r_type_2 (S $ Tok(T.EXCLAMATION,r1) $ AExp(e,r) $ Tok(T.PERIOD,_) $ Tp(tp,r2)) = S $ Tp(A.Forall(aexp2prop r e,tp), join r1 r2)
  | r_type_2 (S $ Tok(T.EXCLAMATION,r1) $ Tok(T.IDENT(id),_) $ Tok(T.PERIOD,_) $ Tp(tp,r2)) = S $ Tp(A.ForallNat(id,tp), join r1 r2)
  | r_type_2 (S $ Tok(T.EXCLAMATION,r1) $ TpVars([id],_) $ Tok(T.PERIOD,_) $ Tp(tp,r2)) = S $ Tp(A.ForallTp(id,tp), join r1 r2)
  | r_type_2 S = r_type_3 S
and r_type_3 (S $ Tok(T.IDENT(id),r1) $ Tps(As,_) $ Indices(es,r2)) = S $ Tp(A.TpName(id,As,es),join r1 r2)
  | r_type_3 (S $ Tok(T.LPAREN, r1) $ Tp(tp,_) $ Tok(T.RPAREN, r2)) = S $ Tp(tp, join r1 r2)
  | r_type_3 (S $ Tp(tp1, r1) $ TpInfix(_, con, _) $ Tp(tp2, r2)) = r_type (S $ Tp(con(tp1,tp2), join r1 r2))
  | r_type_3 (S $ Tp(_,r1) $ Tp(_, r2)) = parse_error (join r1 r2, "consecutive types")
  | r_type_3 (S $ TpInfix(_,_,r)) = parse_error (r, "trailing infix type operator")
  | r_type_3 (S $ Tp(tp,r)) = S $ Tp(tp,r)
  | r_type_3 (S $ Tok(_,r)) = parse_error (r, "unknown or empty type expression")
  (* should be the only possibilities *)

and r_type_seq (S $ Tps(As,r1) $ Tok(T.LBRACKET,_) $ Tp(A,_) $ Tok(T.RBRACKET, r2)) = S $ Tps(As @ [A], join r1 r2)

and r_type_msg (S $ Tok(T.LBRACKET,r1) $ Tp(tp,_) $ Tok(T.RBRACKET,r2)) = S $ Tp(tp, join r1 r2)

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

(* <exp>, initial call *)
and p_actions ST = ST |> push (Action (fn K => K, here ST)) >> p_exp

(* <exp>, recursive calls *)
and p_exp ST = case first ST of
    T.IDENT(id) => ST |> shift >> p_id_exps
  | T.CASE => ST |> shift >> p_id >> p_terminal T.LPAREN >> push (Branches []) >> p_branches >> p_terminal T.RPAREN >> reduce r_exp_atomic >> reduce r_exp
  | T.SEND => ST |> shift >> p_id >> p_id_exp >> p_terminal T.SEMICOLON >> reduce r_action >> p_exp
  | T.CLOSE => ST |> shift >> p_id >> reduce r_exp_atomic >> reduce r_exp
  | T.WAIT => ST |> shift >> p_id >> p_terminal T.SEMICOLON >> reduce r_action >> p_exp
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
  | T.IMPOSSIBLE => ST |> shift >> reduce r_exp_atomic >> reduce r_exp
  (* receiving a natural number or type *)
  | T.LBRACE => ST |> shift >> p_id >> p_terminal T.RBRACE >> p_recv_nat_tp >> p_exp
  | T.LBRACKET => ST |> shift >> p_id >> p_terminal T.RBRACKET >> p_recv_nat_tp >> p_exp
  (* end of expression; do not consume token *)
  | t => ST |> reduce r_exp

and p_id_exp ST = case first ST of
    T.IDENT(x) => ST |> shift
  | T.LBRACE => ST |> shift >> p_aexp >> p_terminal T.RBRACE >> reduce r_idx
  | T.LBRACKET => ST |> shift >> p_type >> p_terminal T.RBRACKET >> reduce r_type_msg
  | t => error_expected_list (here ST, [T.IDENT("<id>"), T.LBRACE, T.LBRACKET], t)

and p_id_exps ST = case first ST of
    T.PERIOD => ST |> shift >> p_id >> p_terminal T.SEMICOLON >> reduce r_action >> p_exp
  | T.LARROW => ST |> shift >> p_spawn_or_recv
  | T.LRARROW => ST |> shift >> p_id >> reduce r_exp_atomic >> reduce r_exp
  | t => error_expected_list (here ST, [T.PERIOD, T.LARROW, T.LRARROW], t)

and p_spawn_or_recv ST = case first ST of
    T.RECV => ST |> shift >> p_id >> p_terminal T.SEMICOLON >> reduce r_action >> p_exp
  | T.IDENT(id) => ST |> p_id >> push (Tps(nil, here ST)) >> p_arg_seq
                      >> push (Chans([], here ST)) >> p_id_seq
  | t => parse_error (here ST, "expected 'recv', or identifier, found " ^ pp_tok t)

and p_recv_nat_tp ST = case first ST of
    T.LARROW => ST |> shift >> p_terminal T.RECV >> p_id >> p_terminal T.SEMICOLON >> reduce r_action
  | t => error_expected (here ST, T.LARROW, t)

and p_id_seq ST = case first ST of
    T.IDENT(_) => ST |> p_id >> reduce r_chan >> p_id_seq
  | T.SEMICOLON => ST |> shift >> reduce r_action >> p_exp
  | _ => ST |> reduce r_exp_atomic >> reduce r_exp

(* [<idx>] postfix of action, default is 1 *)
and p_idx_opt ST = case first ST of
    T.SEMICOLON => ST |> push (AExp(Arith(R.Int(1)), here ST)) >> shift >> reduce r_action
  | T.LBRACE => ST |> p_idx >> p_terminal T.SEMICOLON >> reduce r_action
  | t => error_expected_list (here ST, [T.SEMICOLON, T.LBRACE], t)

(* <con> ';' as postfix of 'assert' and 'assume' *)
and p_con_semi ST = case first ST of
    T.LBRACE => ST |> shift >> p_aexp >> p_terminal T.RBRACE >> reduce r_con >> p_terminal T.SEMICOLON >> reduce r_action
  | t => error_expected (here ST, T.LBRACE, t)

(* reduce <exp>, where <exp> has no continuation (atomic expressions) *)
and r_exp_atomic (S $ Tok(T.CLOSE,r1) $ Tok(T.IDENT(id),r2)) = S $ Exp(m_exp(A.Close(id),join r1 r2),join r1 r2)
  | r_exp_atomic (S $ Tok(T.IDENT(x),r1) $ Tok(T.LARROW,_) $ Tok(T.IDENT(f),_) $ Tps(As,_) $ Indices(es,_) $ Chans(xs,r2)) =
    S $ Exp(m_exp(A.ExpName(x,f,As,es,xs),join r1 r2),join r1 r2)
  | r_exp_atomic (S $ Tok(T.IDENT(x),r1) $ Tok(T.LRARROW,_) $ Tok(T.IDENT(y),r2)) =
    S $ Exp(m_exp(A.Id(x,y), join r1 r2), join r1 r2)
  | r_exp_atomic (S $ Tok(T.CASE,r1) $ Tok(T.IDENT(id),_) $ Tok(T.LPAREN,_) $ Branches(branches) $ Tok(T.RPAREN,r2)) =
    S $ Exp(m_exp(A.Case(id,branches),join r1 r2),join r1 r2)
  | r_exp_atomic (S $ Tok(T.IMPOSSIBLE,r)) =
    S $ Exp(m_exp(A.Imposs,r),r)
  (* should be the only atomic expressions *)

(* reduce <exp>, possibly multiple actions, cuts, or expressions *)
(* stack ends with Action, Cut, or Exp items *)
and r_exp (S $ Action(act,r1) $ Exp(exp,r2)) = r_exp (S $ Exp(act(exp), join r1 r2))
  | r_exp (S $ Action(act, r)) = parse_error (r, "incomplete or missing action")
  (* done reducing *)
  | r_exp (S $ Exp(exp,r)) = S $ Exp(exp,r)

(* reduce action prefix of <exp> *)
(* split into pieces to work around mlton compiler performance bug *)
and r_action S = r_action_1 S
and r_action_1 (S $ Tok(T.IDENT(x),r1) $ Tok(T.PERIOD,_) $ Tok(T.IDENT(id),r2) $ Tok(T.SEMICOLON,r3)) =
    S $ Action((fn K => m_exp(A.Lab(x,id,K),join r1 r2)), join r1 r3)
  | r_action_1 (S $ Tok(T.IDENT(y),r1) $ Tok(T.LARROW,_) $ Tok(T.RECV,_) $ Tok(T.IDENT(x),r2) $ Tok(T.SEMICOLON,r3)) =
    S $ Action((fn K => m_exp(A.Recv(x,y,K),join r1 r2)), join r1 r3)
  | r_action_1 (S $ Tok(T.IDENT(x),r1) $ Tok(T.LARROW,_) $ Tok(T.IDENT(f),_) $ Tps(As,_) $ Indices(es,_) $ Chans(xs,r2) $ Tok(T.SEMICOLON,r3)) =
    S $ Action((fn K => m_exp(A.Spawn(A.ExpName(x,f,As,es,xs),K), join r1 r2)), join r1 r3)
  | r_action_1 (S $ Tok(T.LBRACE,r1) $ Tok(T.IDENT(v),_) $ Tok(T.RBRACE,_) $ Tok(T.LARROW,_)
                $ Tok(T.RECV, _) $ Tok(T.IDENT(x),r2) $ Tok(T.SEMICOLON, r3)) =
    S $ Action((fn K => m_exp(A.RecvNat(x,v,K),join r1 r2)), join r1 r3)
  | r_action_1 (S $ Tok(T.LBRACKET,r1) $ Tok(T.IDENT(alpha),_) $ Tok(T.RBRACKET,_) $ Tok(T.LARROW,_)
                  $ Tok(T.RECV, _) $ Tok(T.IDENT(x),r2) $ Tok(T.SEMICOLON, r3)) =
    S $ Action((fn K => m_exp(A.RecvTp(x,alpha,K),join r1 r2)), join r1 r3)
  | r_action_1 (S $ Tok(T.SEND,r1) $ Tok(T.IDENT(x),_) $ Tok(T.IDENT(w),r2) $ Tok(T.SEMICOLON, r3)) =
    S $ Action((fn K => m_exp(A.Send(x,w,K), join r1 r2)), join r1 r3)
  | r_action_1 (S $ Tok(T.SEND,r1) $ Tok(T.IDENT(x),_) $ AExp(e, r2) $ Tok(T.SEMICOLON, r3)) =
    S $ Action((fn K => m_exp(A.SendNat(x,aexp2arith r2 e,K), join r1 r2)), join r1 r3)
  | r_action_1 (S $ Tok(T.SEND,r1) $ Tok(T.IDENT(x),_) $ Tp(A, r2) $ Tok(T.SEMICOLON, r3)) =
    S $ Action((fn K => m_exp(A.SendTp(x,A,K), join r1 r2)), join r1 r3)
  | r_action_1 (S $ Tok(T.WAIT,r1) $ Tok(T.IDENT(id),r2) $ Tok(T.SEMICOLON,r3)) =
    S $ Action((fn K => m_exp(A.Wait(id,K),join r1 r2)), join r1 r3)
  | r_action_1 S = r_action_2 S
and r_action_2 (S $ Tok(T.DELAY,r1) $ AExp(t,r) $ Tok(T.SEMICOLON,r2)) =
    S $ Action((fn K => m_exp(A.Delay(aexp2arith r t,K),r1)), join r1 r2)
  | r_action_2 (S $ Tok(T.TICK,r1) $ Tok(T.SEMICOLON,r2)) =
    S $ Action((fn K => m_exp(A.Delay(R.Int(1),K),r1)), join r1 r2)
  | r_action_2 (S $ Tok(T.WHEN,r1) $ Tok(T.IDENT(id),r2) $ Tok(T.SEMICOLON,r3)) =
    S $ Action((fn K => m_exp(A.When(id,K),join r1 r2)), join r1 r3)
  | r_action_2 (S $ Tok(T.NOW,r1) $ Tok(T.IDENT(id),r2) $ Tok(T.SEMICOLON,r3)) =
    S $ Action((fn K => m_exp(A.Now(id,K),join r1 r2)), join r1 r3)
  | r_action_2 S = r_action_3 S
and r_action_3 (S $ Tok(T.WORK,r1) $ AExp(pot,r) $ Tok(T.SEMICOLON,r2)) =
    S $ Action((fn K => m_exp(A.Work(aexp2arith r pot,K),r1)), join r1 r2)
  | r_action_3 (S $ Tok(T.PAY,r1) $ Tok(T.IDENT(id),_) $ AExp(pot,r2) $ Tok(T.SEMICOLON,r3)) =
    S $ Action((fn K => m_exp(A.Pay(id,aexp2arith r2 pot,K),join r1 r2)), join r1 r3)
  | r_action_3 (S $ Tok(T.GET,r1) $ Tok(T.IDENT(id),_) $ AExp(pot,r2) $ Tok(T.SEMICOLON,r3)) =
    S $ Action((fn K => m_exp(A.Get(id,aexp2arith r2 pot,K), join r1 r2)), join r1 r3)
  | r_action_3 (S $ Tok(T.ASSERT,r1) $ Tok(T.IDENT(id),_) $ AExp(e,r2) $ Tok(T.SEMICOLON,r3)) =
    S $ Action((fn K => m_exp(A.Assert(id,aexp2prop r2 e,K), join r1 r2)), join r1 r2)
  | r_action_3 (S $ Tok(T.ASSUME,r1) $ Tok(T.IDENT(id),_) $ AExp(e,r2) $ Tok(T.SEMICOLON,r3)) =
    S $ Action((fn K => m_exp(A.Assume(id,aexp2prop r2 e,K),join r1 r2)), join r1 r2)
  (* no other actions should be possible *)

(* <branches> *)
and p_branches ST = case first ST of
    T.IDENT(id) => ST |> shift >> p_terminal T.RARROW >> p_actions >> reduce r_branch >> p_branches2
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
