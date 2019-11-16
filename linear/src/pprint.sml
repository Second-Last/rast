(* Pretty Printing *)

(*
 * Client code should only use this printing
 * functionality. The print functions associated
 * directly with various modules are primarily for
 * debugging and program development purposes
 *)

signature PPRINT =
sig

    (* arithmetic expression and propositions *)
    val pp_arith : Arith.arith -> string (* pp_arith e = "e" *)
    val pp_prop : Arith.prop -> string   (* pp_prop phi = "phi" *)

    (* types *)
    val pp_con : Arith.prop -> string     (* pp_con phi = "{phi}" *)
    val pp_pot : Ast.pot -> string        (* pp_pot p = "{p}", or "" if p = 0 *)
    val pp_potpos : Ast.pot -> string     (* pp_potpos p = "{p}", or "" if p = 1 *)
    val pp_time : Ast.time -> string      (* pp_time t = "{t}", or "" if t = 1 *)

    val pp_tp : Ast.env -> Ast.tp -> string         (* pp_tp env A = "A", with line breaks and indentation *)
    val pp_tp_compact : Ast.env -> Ast.tp -> string (* pp_tp_compact env A = "A", on one line *)
    val pp_context_compact : Ast.env -> Ast.context -> string

    val pp_tpj : Ast.env -> Ast.context -> Ast.pot -> Ast.chan_tp -> string (* pp_tpj env A p C = "A |{p}- C" *)
    val pp_tpj_compact : Ast.env -> Ast.context -> Ast.pot -> Ast.chan_tp -> string (* like pp_tpj, on one line *)

    (* process expressions *)
    val pp_exp : Ast.env -> Ast.exp -> string        (* pp_exp env P = "P", with line breaks and indentation *)
    val pp_exp_prefix : Ast.env -> Ast.exp -> string (* pp_exp_prefix P = "<top action in P>" *)

    (* declarations *)
    val pp_decl : Ast.env -> Ast.decl -> string

    (* configurations *)
    val pp_config : bool -> bool -> Ast.config -> string

end

structure PPrint :> PPRINT =
struct

structure R = Arith
structure RP = R.Print
structure A = Ast
structure P = A.Print

(**************************)
(* Arithmetic expressions *)
(**************************)
              
(* Uses precedence
 * prec('+','-') = 1; prec('*') = 2
 *)
fun parens prec_left prec s =
    if prec_left >= prec then "(" ^ s ^ ")" else s

(* pp_arith_prec prec_left e = "e"
 * using the precedence prec_left of the operator
 * to the left to decide on parentheses
 * All arithmetic operators are left associative
 *)
fun pp_arith_prec prec_left (R.Int(n)) =
    if n >= 0 then Int.toString n
    else pp_arith_prec prec_left (R.Sub(R.Int(0),R.Int(0-n))) (* might overflow *)
  | pp_arith_prec prec_left (R.Add(s,t)) =
    parens prec_left 1 (pp_arith_prec 0 s ^ "+" ^ pp_arith_prec 1 t)
  | pp_arith_prec prec_left (R.Sub(s,t)) =
    parens prec_left 1 (pp_arith_prec 0 s ^ "-" ^ pp_arith_prec 1 t)
  | pp_arith_prec prec_left (R.Mult(s,t)) =
    parens prec_left 2 (pp_arith_prec 1 s ^ "*" ^ pp_arith_prec 2 t)
  | pp_arith_prec prec_left (R.Var(x)) = x

(* pp_arith e = "e" *)
fun pp_arith e = pp_arith_prec 0 e

(****************)
(* Propositions *)
(****************)

(* omit parenthesis for /\ and \/ and right-associative => *)
(* precedence: ~ > /\,\/,=> *)

datatype opr = Or | And | Implies | Not | None

fun parens_opr None opr s = s   (* root: no parentheses *)
  | parens_opr opr_above opr s =
    if opr_above = opr then s else "(" ^ s ^ ")"

fun pp_prop_prec opr_above (R.Eq(s,t)) = pp_arith s ^ " = " ^ pp_arith t
  | pp_prop_prec opr_above (R.Lt(s,t)) = pp_arith s ^ " < " ^ pp_arith t
  | pp_prop_prec opr_above (R.Gt(s,t)) = pp_arith s ^ " > " ^ pp_arith t
  | pp_prop_prec opr_above (R.Le(s,t)) = pp_arith s ^ " <= " ^ pp_arith t
  | pp_prop_prec opr_above (R.Ge(s,t)) = pp_arith s ^ " >= " ^ pp_arith t
  | pp_prop_prec opr_above (R.Divides(n,t)) =
    Int.toString n ^ "|" ^ pp_arith_prec 3 t (* parens for clarity *)
  | pp_prop_prec opr_above (R.True) = "true"
  | pp_prop_prec opr_above (R.False) = "false"
  | pp_prop_prec opr_above (R.Or(F,G)) =
    parens_opr opr_above Or (pp_prop_prec Or F ^ " \\/ " ^ pp_prop_prec Or G)
  | pp_prop_prec opr_above (R.And(R.True,G)) = (* one small optimization *)
    pp_prop_prec opr_above G
  | pp_prop_prec opr_above (R.And(F,G)) =
    parens_opr opr_above And (pp_prop_prec And F ^ " /\\ " ^ pp_prop_prec And G)
  | pp_prop_prec opr_above (R.Implies(F,G)) =
    (* in F => G, treat F as in ~F *)
    parens_opr opr_above Implies (pp_prop_prec Not F ^ " => " ^ pp_prop_prec Implies G)
  | pp_prop_prec opr_above (R.Not(F)) =
    parens_opr opr_above Not ("~" ^ pp_prop_prec Not F)

fun pp_prop F = pp_prop_prec None F

(*******************************)
(* Types, and their components *)
(*******************************)
                
fun pp_con phi = "{" ^ pp_prop phi ^ "}"

(* pp_idx es = "{e1}...{en}" *)
fun pp_idx nil = ""
  | pp_idx (e::es) = "{" ^ pp_arith e ^ "}" ^ pp_idx es

(* pp_pot p = "{p}", "" if p = 0 *)
fun pp_pot (R.Int(0)) = ""
  | pp_pot e = "{" ^ pp_arith e ^ "}"

(* pp_pospos p = "{p}", "" if p = 1 *)
fun pp_potpos (R.Int(1)) = ""
  | pp_potpos e = "{" ^ pp_arith e ^ "}"

(* pp_time t = "{t}", "" if t = 1 *)
fun pp_time (R.Int(1)) = ""
  | pp_time e = "{" ^ pp_arith e ^ "}"

(***********************)
(* Externalizing types *)
(***********************)
fun is_internal a = String.sub (a,0) = #"%"

(* In order to have a reasonable type equality algorithm, types
 * only have one layer of constructors followed by a type name
 * internal type names (starting with '%') are expanded and
 * external type names (all others) are kept
 *)
(* ext_tp env A = A_ext, in external form *)
fun ext_tp env (A.One) = A.One
  | ext_tp env (A.Plus(choices)) = A.Plus(ext_choices env choices)
  | ext_tp env (A.With(choices)) = A.With(ext_choices env choices)
  | ext_tp env (A.Tensor(A,B)) = A.Tensor(ext_tp env A, ext_tp env B)
  | ext_tp env (A.Lolli(A,B)) = A.Lolli(ext_tp env A, ext_tp env B)
  | ext_tp env (A.Next(t,A)) = A.Next(t,ext_tp env A)
  | ext_tp env (A.Box(A)) = A.Box(ext_tp env A)
  | ext_tp env (A.Dia(A)) = A.Dia(ext_tp env A)
  | ext_tp env (A.GetPot(p,A)) = A.GetPot(p,ext_tp env A)
  | ext_tp env (A.PayPot(p,A)) = A.PayPot(p,ext_tp env A)
  | ext_tp env (A.Exists(phi,A)) = A.Exists(phi,ext_tp env A)
  | ext_tp env (A.Forall(phi,A)) = A.Forall(phi,ext_tp env A)
  | ext_tp env (A as A.TpName(a,es)) =
    if is_internal a
    then ext_tp env (A.expd_tp env (a,es))   (* must be defined to be mentioned *)
    else A
  | ext_tp env (A.Dot) = A.Dot

and ext_choices env nil = nil
  | ext_choices env ((l,A)::choices) =
    (l, ext_tp env A)::(ext_choices env choices)

(*******************************)
(* Multiline Printing of Types *)
(*******************************)

fun spaces n =
    if n <= 0 then ""
    else " " ^ spaces (n-1)

fun len s = String.size s

(* pp_tp i A = "A", where i is the indentation after a newline
 * A must be externalized, or internal name '%n' will be printed
 *)
fun pp_tp i (A.One) = "1"
  | pp_tp i (A.Plus(choice)) = "+{ " ^ pp_choice (i+3) choice ^ " }"
  | pp_tp i (A.With(choice)) = "&{ " ^ pp_choice (i+3) choice ^ " }"
  | pp_tp i (A.Tensor(A,B)) =
      let val astr = pp_tp i A ^ " * "
          val l = len (astr)
      in
      astr ^ pp_tp (i+l) B
      end
  | pp_tp i (A.Lolli(A,B)) =
      let val astr = pp_tp i A ^ " -o "
          val l = len (astr)
      in
      astr ^ pp_tp (i+l) B
      end
  | pp_tp i (A.Next(t,A)) = "(" ^ pp_time t ^ ") " ^ pp_tp (i+len(pp_time t)+3) A
  | pp_tp i (A.Box(A)) = "[]" ^ pp_tp (i+2) A
  | pp_tp i (A.Dia(A)) = "<>" ^ pp_tp (i+2) A
  | pp_tp i (A.GetPot(p,A)) = "<" ^ pp_potpos p ^ "| " ^ pp_tp (i+len(pp_potpos(p))+3) A
  | pp_tp i (A.PayPot(p,A)) = "|" ^ pp_potpos p ^ "> " ^ pp_tp (i+len(pp_potpos(p))+3) A
  | pp_tp i (A.Exists(phi,A)) = "?" ^ pp_con phi ^ ". " ^ pp_tp (i+len(pp_con(phi))+3) A
  | pp_tp i (A.Forall(phi,A)) = "!" ^ pp_con phi ^ ". " ^ pp_tp (i+len(pp_con(phi))+3) A
  | pp_tp i (A.TpName(a,l)) = a ^ pp_idx l
  | pp_tp i (A.Dot) = "."
and pp_tp_indent i A = spaces i ^ pp_tp i A
and pp_tp_after i s A = s ^ pp_tp (i+len(s)) A

and pp_choice i nil = ""
  | pp_choice i ((l,A)::nil) =
    pp_tp_after i (l ^ " : ") A
  | pp_choice i ((l,A)::choices) =
    pp_tp_after i (l ^ " : ") A ^ ",\n"
    ^ pp_choice_indent i choices
and pp_choice_indent i choices = spaces i ^ pp_choice i choices

val pp_tp = fn env => fn A => pp_tp 0 (ext_tp env A)

(* pp_tp_compact env A = "A", without newlines
 * this first externalizes A, then prints on one line
 *)
fun pp_tp_compact env A = P.pp_tp (ext_tp env A)

fun pp_chan_tp_compact env (x,A) = "(" ^ x ^ " : " ^ pp_tp_compact env A ^ ")"
fun pp_context_compact env nil = "."
  | pp_context_compact env [xA] = pp_chan_tp_compact env xA
  | pp_context_compact env (xA::D) = pp_chan_tp_compact env xA ^ " " ^ pp_context_compact env D

(* pp_tpj env A pot C = "A |{p}- C" *)
fun pp_tpj env D pot zC =
    pp_context_compact env D ^ " |" ^ pp_pot pot ^ "- " ^ pp_chan_tp_compact env zC

(* pp_tpj_compact env A pot C = "A |{p}- C", on one line *)
fun pp_tpj_compact env D pot zC =
    pp_context_compact env D ^ " |" ^ pp_pot pot ^ "- " ^ pp_chan_tp_compact env zC

(***********************)
(* Process expressions *)
(***********************)

(* Cut is right associative, so we need paren around
 * the left-hand side of a cut if it is not atomic.
 * Atomic are Id, Case<dir>, CloseR, ExpName
 * Rather than propagating a binding strength downward,
 * we just peek ahead.
 *)
fun atomic P = case P of
    A.Id _ => true | A.Case _ => true
  | A.Close _ => true | A.ExpName _ => true
  | A.Marked(marked_exp) => atomic (Mark.data marked_exp)
  | _ => false

fun long P = case P of
    A.Case _ => true
  | A.Marked(marked_exp) => long (Mark.data marked_exp)
  | _ => false

fun pp_chanlist [] = ""
  | pp_chanlist [x] = x
  | pp_chanlist (x::l) = x ^ " " ^ pp_chanlist l

fun pp_exp env i (A.Spawn(P,Q)) = (* P = f *)
    pp_exp env i P ^ " ;\n" ^ pp_exp_indent env i Q
  | pp_exp env i (A.Id(x,y)) = x ^ " <- " ^ y
  | pp_exp env i (A.Lab(x,k,P)) = x ^ "." ^ k ^ " ;\n" ^ pp_exp_indent env i P
  | pp_exp env i (A.Case(x,branches)) = "case " ^ x ^ " (" ^ pp_branches env (i+7+len(x)) branches ^ " )"
  | pp_exp env i (A.Send(x,w,P)) = "send " ^ x ^ " " ^ w ^ " ;\n" ^ pp_exp_indent env i P
  | pp_exp env i (A.Recv(x,y,Q)) = y ^ " <- recv " ^ x ^ " ;\n" ^ pp_exp_indent env i Q
  | pp_exp env i (A.Close(x)) = "close " ^ x
  | pp_exp env i (A.Wait(x,Q)) = "wait " ^ x ^ " ;\n" ^ pp_exp_indent env i Q
  | pp_exp env i (A.Delay(t,P)) = "delay " ^ pp_time t ^ " ;\n" ^ pp_exp_indent env i P
  | pp_exp env i (A.When(x,P)) = "when? " ^ x ^ " ;\n" ^ pp_exp_indent env i P
  | pp_exp env i (A.Now(x,Q)) = "now! " ^ x ^ " ;\n" ^ pp_exp_indent env i Q
  | pp_exp env i (A.Work(p, P)) = "work " ^ pp_potpos p ^ " ;\n" ^ pp_exp_indent env i P
  | pp_exp env i (A.Pay(x,p,P)) = "pay " ^ x ^ " " ^ pp_potpos p ^ " ;\n" ^ pp_exp_indent env i P
  | pp_exp env i (A.Get(x,p,P)) = "get " ^ x ^ " " ^ pp_potpos p ^ " ;\n" ^ pp_exp_indent env i P
  | pp_exp env i (A.Assert(x,phi,P)) = "assert " ^ x ^ " " ^ pp_con phi ^ " ;\n" ^ pp_exp_indent env i P
  | pp_exp env i (A.Assume(x,phi,P)) = "assume " ^ x ^ " " ^ pp_con phi ^ " ;\n" ^ pp_exp_indent env i P
  | pp_exp env i (A.Imposs) = "impossible"
  | pp_exp env i (A.ExpName(x,f,es,xs)) = x ^ " <- " ^ f ^ pp_idx es ^ " <- " ^ pp_chanlist xs
  | pp_exp env i (A.Marked(marked_exp)) = pp_exp env i (Mark.data marked_exp)
and pp_exp_indent env i P = spaces i ^ pp_exp env i P
and pp_exp_after env i s P = s ^ pp_exp env (i+len(s)) P

and pp_branches env i nil = ""
  | pp_branches env i ((l,_,P)::nil) = pp_exp_after env i (l ^ " => ") P
  | pp_branches env i ((l,_,P)::branches) =
    pp_exp_after env i (l ^ " => ") P ^ "\n"
    ^ pp_branches_indent env i branches
and pp_branches_indent env i branches = spaces (i-2) ^ "| " ^ pp_branches env i branches

(*******************)
(* Prefix printing *)
(*******************)

(* prints only a prefix of the process expression, for
 * tracing purposes
 *)
fun pp_exp_prefix env (A.Spawn(P,Q)) = pp_exp_prefix env P ^ " ; ..."
  | pp_exp_prefix env (A.Id(x,y)) = x ^ " <- " ^ y
  | pp_exp_prefix env (A.Lab(x,k,P)) = x ^ "." ^ k ^ " ; ..."
  | pp_exp_prefix env (A.Case(x,branches)) = "case " ^ x ^ "(...)"
  | pp_exp_prefix env (A.Send(x,w,P)) = "send " ^ x ^ " " ^ w ^ " ; ..."
  | pp_exp_prefix env (A.Recv(x,y,Q)) = y ^ " <- recv " ^ x ^ " ; ..."
  | pp_exp_prefix env (A.Close(x)) = "close " ^ x
  | pp_exp_prefix env (A.Wait(x,Q)) = "wait " ^ x ^ " ; ..."
  | pp_exp_prefix env (A.Delay(t,P)) = "delay " ^ pp_time t ^ " ; ..."
  | pp_exp_prefix env (A.When(x,P)) = "when? " ^ x ^ " ; ..."
  | pp_exp_prefix env (A.Now(x,Q)) = "now! " ^ x ^ " ; ..."
  | pp_exp_prefix env (A.Work(p,P)) = "work " ^ pp_potpos p ^ " ; ..."
  | pp_exp_prefix env (A.Pay(x,p,P)) = "pay " ^ x ^ " " ^ pp_potpos p ^ " ; ..."
  | pp_exp_prefix env (A.Get(x,p,P)) = "get " ^ x ^ " " ^ pp_potpos p ^ " ; ..."
  | pp_exp_prefix env (A.Assert(x,phi,P)) = "assert " ^ x ^ " " ^ pp_con phi ^ " ; ..."
  | pp_exp_prefix env (A.Assume(x,phi,P)) = "assume " ^ x ^ " " ^ pp_con phi ^ " ; ..."
  | pp_exp_prefix env (A.Imposs) = "impossible"
  | pp_exp_prefix env (A.ExpName(x,f,es,xs)) = x ^ " <- " ^ f ^ pp_idx es ^ " <- " ^ pp_chanlist xs
  | pp_exp_prefix env (A.Marked(marked_exp)) = pp_exp_prefix env (Mark.data marked_exp)

(****************)
(* Declarations *)
(****************)

fun pp_decl env (A.TpDef(a,vs,R.True,A,_)) =
    pp_tp_after 0 ("type " ^ a ^ P.pp_vars vs ^ " = ") (ext_tp env A)
  | pp_decl env (A.TpDef(a,vs,con,A,_)) =
    pp_tp_after 0 ("type " ^ a ^ P.pp_vars vs ^ P.pp_con con ^ " = ") (ext_tp env A)
  | pp_decl env (A.TpEq(ctx,con,A.TpName(a,es),A.TpName(a',es'),_)) =
    "eqtype " ^ a ^ pp_idx es ^ " = " ^ a' ^ pp_idx es'
  | pp_decl env (A.ExpDec(f,vs,con,(D,pot,zC),_)) =
    "proc " ^ f ^ P.pp_vars vs ^ P.pp_con con ^ " : "
    ^ pp_context_compact env D ^ " |" ^ pp_pot pot ^ "- " ^ pp_chan_tp_compact env zC
  | pp_decl env (A.ExpDef(f,vs,(xs,P,x),_)) = pp_exp_after env 0 ("proc " ^ f ^ P.pp_vars vs ^ " : " ^ x ^ " <- " ^ pp_chanlist xs ^ " = ") P
  | pp_decl env (A.Exec(f,_)) = "exec " ^ f
  | pp_decl env (A.Pragma(p,line,_)) = p ^ line

(******************)
(* Configurations *)
(******************)

fun pp_config mtime mwork nil = ""
  | pp_config mtime mwork (A.Proc(t, (w, pot), P)::config) =
    (if mtime then "$ " ^ Int.toString(t) ^ " " else "")
    ^ (if mwork then "$ (" ^ Int.toString(w) ^ ", " ^ Int.toString(pot) ^ ") " else "")
    ^ "$ " ^ P.pp_exp P ^ "\n"         (* print compactly *)
    ^ pp_config mtime mwork config
  | pp_config mtime mwork (A.Msg(t, (w, pot), M)::config) =
    (if mtime then "@ " ^ Int.toString(t) ^ " " else "")
    ^ (if mwork then "@ (" ^ Int.toString(w) ^ ", " ^ Int.toString(pot) ^ ") " else "")
    ^ "@ " ^ P.pp_msg M ^ "\n"         (* print compactly *)
    ^ pp_config mtime mwork config

(**********************)
(* External Interface *)
(**********************)

val pp_exp = fn env => fn P => pp_exp env 0 P

end (* structure PPrint *)