(* Abstract Syntax *)

signature AST =
sig

type label = string             (* l,k for internal and external choice *)
type tpname = string            (* a, for types defined with a = A *)
type expname = string           (* f, for processes defined with f = P *)
type ext = Mark.ext option      (* optional extent (source region info) *)

type pot = Arith.arith          (* p,q, potential for work *)
type time = Arith.arith         (* s,t, for time *)

(* Types *)
datatype tp =
         Plus of (label * tp) list (* +{...} *)
       | With of (label * tp) list (* &{...} *)
       | One                       (* 1 *)
       | Exists of Arith.prop * tp (* ?{phi}. A *)
       | Forall of Arith.prop * tp (* !{phi}. A *)
       | PayPot of pot * tp        (* |> A  or  |{p}> A *)
       | GetPot of pot * tp        (* <| A  or  <{p}| A *)
       | Next of time * tp         (* ()A  or  ({t}) A *)
       | Dia of tp                 (* <> A *)
       | Box of tp                 (* [] A *)
       | TpName of tpname * Arith.arith list (* a  or  a{...} *)
       | Dot                       (* pseudo-type for empty context *)
type choices = (label * tp) list

type chan = string
type chan_tp = chan * tp
type context = chan_tp list

(* Process Expressions *)
datatype exp =
       (* judgmental constructs *)
         Id of chan * chan                                             (* x <- y *)
       | Spawn of exp * exp                                            (* P || Q *)
       | ExpName of chan * expname * Arith.arith list * chan list      (* x <- f, f{...} <- xs *)

       (* internal/external choice +{...} *)
       | Lab of chan * label * exp                   (* x.k ; P *)
       | Case of chan * (label * ext * exp) list     (* case x (...) *)

       (* termination 1 *)
       | Close of chan                               (* closeR *)
       | Wait of chan * exp                          (* waitL ; P *)

       (* existential quantifier ?{phi}. A *)
       | Assert of chan * Arith.prop * exp           (* assertR{phi} ; P *)
       | Assume of chan * Arith.prop * exp           (* assumeL{phi} ; P *)

       (* impossibility; no concrete syntax for now *)
       | Imposs                                      (* impossible *)             

       (* work *)
       | Work of pot * exp                           (* work ; P or work{p} ; P *)

       (* pay potential |>A *)
       | Pay of chan * pot * exp                     (* payR ; P or payR{p} ; P *)
       | Get of chan * pot * exp                     (* getL ; P or getL{p} ; P *)

       (* next time ()A *)
       | Delay of time * exp                         (* delay ; P or delay{t} ; P *)

       (* some future time <>A *)
       | Now of chan * exp                           (* nowR ; P *)
       | When of chan * exp                          (* whenL ; P *)

       (* mark with source region *)
       | Marked of exp Mark.marked

type branches = (label * ext * exp) list       (* (l1 => P1 | ... | ln => Pn) *)

(* Declarations *)
datatype decl =
         Pragma of string * string * ext                     (* #options, #test *)
       | TpDef of tpname * Arith.ctx * Arith.prop * tp * ext (* type a = A *)
       | TpEq of Arith.ctx * Arith.prop * tp * tp * ext      (* eqtype a = b *)
       | ExpDec of expname * Arith.ctx * Arith.prop * (context * pot * chan_tp) * ext
                                                             (* proc f : Delta |{pot}- C *)
       | ExpDef of expname * Arith.ctx * (chan list * exp * chan) * ext
                                                             (* proc x <- f <- xs = P *)
       | Exec of expname * ext                               (* exec f *)

type env = decl list

(* Substitution *)
val apply_tp : Arith.subst -> tp -> tp    (* [sigma]A *)
val apply_exp : Arith.subst -> exp -> exp (* [sigma]P *)
val apply_chan_tp : Arith.subst -> chan_tp -> chan_tp
val apply_context : Arith.subst -> context -> context

(* Environments *)
val lookup_tp : env -> tpname -> (Arith.ctx * Arith.prop * tp) option
val lookup_expdec : env -> expname -> (Arith.ctx * Arith.prop * (context * pot * chan_tp)) option
val lookup_expdef : env -> expname -> (Arith.ctx * (chan list * exp * chan)) option

val lookup_choice : choices -> label -> tp option
val lookup_branch : branches -> label -> exp option

(* Definitions and Declarations *)
val expd_tp : env -> tpname * Arith.arith list -> tp  (* must exist, by some invariant *)
val expd_expdec : env -> expname * Arith.arith list -> (Arith.prop * (context * pot * chan_tp)) option
val expd_expdef : env -> expname * Arith.arith list -> exp option

(* Operational Semantics *)
val strip_exts : exp -> exp     (* remove all marks to support pattern matching *)

(* Messages *)
structure M : sig
datatype msg =
         LabR of label
       | LabL of label
       | CloseR
       | AssertR of Arith.prop
       | AssertL of Arith.prop
       | PayR of pot
       | PayL of pot
       | NowR
       | NowL
end

(* Semantic objects *)
datatype proc = Proc of int * (int * int) * exp   (* Proc(time, (work, pot), P) *)
              | Msg of int * (int * int) * M.msg  (* Msg(time, (work, pot), M) *)

type config = proc list

(* Printing *)
(* for internal and debugging purposes only *)
(* see pprint.sml for external printing *)
structure Print :
sig
    val pp_vars : Arith.varname list -> string
    val pp_idx : Arith.arith list -> string
    val pp_prop : Arith.prop -> string
    val pp_con : Arith.prop -> string
    val pp_tp : tp -> string
    val pp_exp : exp -> string
    val pp_decl : decl -> string
    val pp_pot : pot -> string
    val pp_potpos : pot -> string
    val pp_time : time -> string
    val pp_msg : M.msg -> string
    val pp_config : config -> string
end

end (* signature AST *)

structure Ast :> AST =
struct

structure R = Arith
structure RP = R.Print

type label = string
type tpname = string
type expname = string
type ext = Mark.ext option

type pot = R.arith
type time = R.arith

(* Types *)
datatype tp =
         Plus of (label * tp) list (* +{...} *)
       | With of (label * tp) list (* &{...} *)
       | One                       (* 1 *)
       | Exists of R.prop * tp     (* ?{phi}. A *)
       | Forall of R.prop * tp     (* !{phi}. A *)
       | PayPot of pot * tp        (* |> A  or  |{p}> A *)
       | GetPot of pot * tp        (* <| A  or  <{p}| A *)
       | Next of time * tp         (* ()A  or  ({t}) A *)
       | Dia of tp                 (* <> A *)
       | Box of tp                 (* [] A *)
       | TpName of tpname * R.arith list (* a  or  a{...} *)
       | Dot                       (* pseudo-type for empty context *)
type choices = (label * tp) list

type chan = string
type chan_tp = chan * tp
type context = chan_tp list

datatype exp =
       (* judgmental constructs *)
         Id of chan * chan                                             (* x <- y *)
       | Spawn of exp * exp                                            (* P || Q *)
       | ExpName of chan * expname * Arith.arith list * chan list      (* x <- f, f{...} <- xs *)

       (* internal/external choice +{...} *)
       | Lab of chan * label * exp                   (* x.k ; P *)
       | Case of chan * (label * ext * exp) list     (* case x (...) *)

       (* termination 1 *)
       | Close of chan                               (* closeR *)
       | Wait of chan * exp                          (* waitL ; P *)

       (* existential quantifier ?{phi}. A *)
       | Assert of chan * Arith.prop * exp           (* assertR{phi} ; P *)
       | Assume of chan * Arith.prop * exp           (* assumeL{phi} ; P *)

       (* impossibility; no concrete syntax for now *)
       | Imposs                                      (* impossible *)             

       (* work *)
       | Work of pot * exp                           (* work ; P or work{p} ; P *)

       (* pay potential |>A *)
       | Pay of chan * pot * exp                     (* payR ; P or payR{p} ; P *)
       | Get of chan * pot * exp                     (* getL ; P or getL{p} ; P *)

       (* next time ()A *)
       | Delay of time * exp                         (* delay ; P or delay{t} ; P *)

       (* some future time <>A *)
       | Now of chan * exp                           (* nowR ; P *)
       | When of chan * exp                          (* whenL ; P *)

       (* mark with source region *)
       | Marked of exp Mark.marked

type branches = (label * ext * exp) list       (* (l1 => P1 | ... | ln => Pn) *)

datatype decl =
         Pragma of string * string * ext
       | TpDef of tpname * R.ctx * R.prop * tp * ext
       | TpEq of R.ctx * R.prop * tp * tp * ext
       | ExpDec of expname * R.ctx * R.prop * (context * pot * chan_tp) * ext
       | ExpDef of expname * R.ctx * (chan list * exp * chan) * ext
       | Exec of expname * ext

type env = decl list

(****************)
(* Substitution *)
(****************)

fun apply_tp sg (One) = One
  | apply_tp sg (Plus(choices)) = Plus(apply_choices sg choices)
  | apply_tp sg (With(choices)) = With(apply_choices sg choices)
  | apply_tp sg (Next(t,A)) = Next(R.apply sg t, apply_tp sg A)
  | apply_tp sg (Box(A)) = Box(apply_tp sg A)
  | apply_tp sg (Dia(A)) = Dia(apply_tp sg A)
  | apply_tp sg (GetPot(p,A)) = GetPot(R.apply sg p,apply_tp sg A)
  | apply_tp sg (PayPot(p,A)) = PayPot(R.apply sg p,apply_tp sg A)
  | apply_tp sg (Exists(phi,A)) = Exists(R.apply_prop sg phi, apply_tp sg A)
  | apply_tp sg (Forall(phi,A)) = Forall(R.apply_prop sg phi, apply_tp sg A)
  | apply_tp sg (TpName(a,es)) = TpName(a, R.apply_list sg es)
  | apply_tp sg (Dot) = Dot

and apply_choices sg choices = List.map (fn (l,Al) => (l, apply_tp sg Al)) choices

fun apply_chan_tp sg (x,A) = (x,apply_tp sg A)
fun apply_context sg D = List.map (fn xA => apply_chan_tp sg xA) D

fun apply_exp sg (Spawn(P,Q)) = Spawn(apply_exp sg P, apply_exp sg Q)
  | apply_exp sg (Id(x,y)) = Id(x,y)
  | apply_exp sg (Lab(x,k,P)) = Lab(x,k, apply_exp sg P)
  | apply_exp sg (Case(x,branches)) = Case(x,apply_branches sg branches)
  | apply_exp sg (Close(x)) = Close(x)
  | apply_exp sg (Wait(x,Q)) = Wait(x,apply_exp sg Q)
  | apply_exp sg (Delay(t,Q)) = Delay(R.apply sg t, apply_exp sg Q)
  | apply_exp sg (When(x,Q)) = When(x,apply_exp sg Q)
  | apply_exp sg (Now(x,Q)) = Now(x,apply_exp sg Q)
  | apply_exp sg (Work(p,P)) = Work(R.apply sg p, apply_exp sg P)
  | apply_exp sg (Pay(x,p,P)) = Pay(x,R.apply sg p, apply_exp sg P)
  | apply_exp sg (Get(x,p,P)) = Get(x,R.apply sg p, apply_exp sg P)
  | apply_exp sg (Assert(x,phi,P)) = Assert(x,R.apply_prop sg phi, apply_exp sg P)
  | apply_exp sg (Assume(x,phi,P)) = Assume(x,R.apply_prop sg phi, apply_exp sg P)
  | apply_exp sg (Imposs) = Imposs
  | apply_exp sg (ExpName(x,f,es,xs)) = ExpName(x,f, R.apply_list sg es, xs)
  | apply_exp sg (Marked(marked_P)) = Marked(Mark.mark' (Mark.data marked_P, Mark.ext marked_P))

and apply_branches sg branches = List.map (fn (l,ext,P) => (l,ext,apply_exp sg P)) branches

(* Environments *)

fun lookup_tp (TpDef(a',vs,con,A,_)::env') a  =
    if a = a' then SOME(vs,con,A) else lookup_tp env' a
  | lookup_tp (_ ::env') a = lookup_tp env' a
  | lookup_tp (nil) a = NONE

fun lookup_expdec (ExpDec(f',vs,con,(D, pot, zC),_)::env') f =
    if f = f' then SOME(vs,con,(D,pot,zC)) else lookup_expdec env' f
  | lookup_expdec (_::env') f = lookup_expdec env' f
  | lookup_expdec nil f = NONE

fun lookup_expdef (ExpDef(f',vs,(xs,P,x),_)::env') f =
    if f = f' then SOME(vs,(xs,P,x)) else lookup_expdef env' f
  | lookup_expdef (_::env') f = lookup_expdef env' f
  | lookup_expdef nil f = NONE

fun lookup_choice ((l:label,A)::choices) k =
    if k = l then SOME(A)
    else lookup_choice choices k
  | lookup_choice nil k = NONE

fun lookup_branch ((l:label,_,P)::branches) k =
    if k = l then SOME(P)
    else lookup_branch branches k
  | lookup_branch nil k = NONE

(********************************)
(* Definitions and declarations *)
(********************************)

(* expd_tp env (a,es) = [es/vs]A if a{vs} = A
 * assumes a is defined and |es| = |vs|
 * requires that constraints con |= a{vs} = A are entailed
 * in current context, which should be enforced by type validity
 *)
fun expd_tp env (a,es) =
    case lookup_tp env a
     of SOME(vs,con,A) => apply_tp (R.zip vs es) A (* cannot return NONE *)

fun expd_expdec env (f,es) =
    (case lookup_expdec env f
      of SOME(vs,con,(D,pot,(z,C))) =>
         let val sg = R.zip vs es (* requires |vs| = |es| *)
         in SOME(R.apply_prop sg con, (apply_context sg D, R.apply sg pot, (z,apply_tp sg C)))
         end
       | NONE => NONE)

fun expd_expdef env (f,es) =
  (case lookup_expdef env f of
    SOME(vs,(xs,P,x)) => SOME(apply_exp (R.zip vs es) P) (* requires |vs| = |es| *)
  | NONE => NONE)

(*************************)
(* Operational Semantics *)
(*************************)

(* strip_exts P = P' strips all source location information from P
 * This helps in writing the operational rules by pattern matching
 *)
fun strip_exts (Id(x,y)) = Id(x,y)
  | strip_exts (Spawn(P,Q)) = Spawn(strip_exts P,strip_exts Q)
  | strip_exts (ExpName(x,f,es,xs)) = ExpName(x,f,es,xs)
  | strip_exts (Lab(x,k,P)) = Lab(x,k, strip_exts P)
  | strip_exts (Case(x,branches)) = Case(x,strip_exts_branches branches)
  | strip_exts (Close(x)) = Close(x)
  | strip_exts (Wait(x,Q)) = Wait(x,strip_exts Q)
  | strip_exts (Assert(x,phi,P)) = Assert(x,phi, strip_exts P)
  | strip_exts (Assume(x,phi,Q)) = Assume(x,phi, strip_exts Q)
  | strip_exts (Imposs) = Imposs
  | strip_exts (Work(p,P)) = Work(p,strip_exts P)
  | strip_exts (Pay(x,p,P)) = Pay(x,p,strip_exts P)
  | strip_exts (Get(x,p,P)) = Get(x,p,strip_exts P)
  | strip_exts (Delay(t,P)) = Delay(t,strip_exts P)
  | strip_exts (Now(x,P)) = Now(x,strip_exts P)
  | strip_exts (When(x,Q)) = When(x,strip_exts Q)
  | strip_exts (Marked(marked_P)) = strip_exts (Mark.data marked_P)
and strip_exts_branches nil = nil
  | strip_exts_branches ((l,ext,P)::branches) =
    (l,ext,strip_exts P)::strip_exts_branches branches

structure M = struct
datatype msg =
         LabR of label
       | LabL of label
       | CloseR
       | AssertR of Arith.prop
       | AssertL of Arith.prop
       | PayR of pot
       | PayL of pot
       | NowR
       | NowL
end

datatype proc = Proc of int * (int * int) * exp   (* Proc(time, (work, pot), P) *)
              | Msg of int * (int * int) * M.msg  (* Msg(time, (work, pot), M) *)

type config = proc list

(************)
(* Printing *)
(************)

structure Print =
struct

fun pp_pot (R.Int(0)) = ""
  | pp_pot e = "{" ^ RP.pp_arith e ^ "}"

fun pp_potpos (R.Int(1)) = ""
  | pp_potpos e = "{" ^ RP.pp_arith e ^ "}"

fun pp_time (R.Int(1)) = ""
  | pp_time e = "{" ^ RP.pp_arith e ^ "}"

fun pp_vars nil = ""
  | pp_vars (v::vs) = "{" ^ v ^ "}" ^ pp_vars vs

fun pp_idx nil = ""
  | pp_idx (e::l) = "{" ^ RP.pp_arith e ^ "}" ^ pp_idx l

fun pp_prop phi = "{" ^ RP.pp_prop phi ^ "}"

fun pp_tp (One) = "1"
  | pp_tp (Plus(choice)) = "+{" ^ pp_choice choice ^ "}"
  | pp_tp (With(choice)) = "&{" ^ pp_choice choice ^ "}"
  | pp_tp (Next(t,A)) = "(" ^ pp_time t ^ ")" ^ pp_tp A
  | pp_tp (Box(A)) = "[]" ^ pp_tp A
  | pp_tp (Dia(A)) = "<>" ^ pp_tp A
  | pp_tp (GetPot(p,A)) = "<" ^ pp_potpos p ^ "|" ^ pp_tp A
  | pp_tp (PayPot(p,A)) = "|" ^ pp_potpos p ^ ">" ^ pp_tp A
  | pp_tp (Exists(phi,A)) = "?" ^ pp_prop phi ^ ". " ^ pp_tp A
  | pp_tp (Forall(phi,A)) = "!" ^ pp_prop phi ^ ". " ^ pp_tp A
  | pp_tp (TpName(a,l)) = a ^ pp_idx l
  | pp_tp (Dot) = "."
and pp_choice nil = ""
  | pp_choice ((l,A)::nil) = l ^ " : " ^ pp_tp A
  | pp_choice ((l,A)::choices) =
    l ^ " : " ^ pp_tp A ^ ", " ^ pp_choice choices

fun pp_chanlist [] = ""
  | pp_chanlist [x] = x
  | pp_chanlist (x::l) = x ^ " " ^ pp_chanlist l

fun pp_exp (Spawn(P,Q)) = pp_exp P ^ " ; " ^ pp_exp Q
  | pp_exp (Id(x,y)) = x ^ " <- " ^ y
  | pp_exp (Lab(x,k,P)) = x ^ "." ^ k ^ " ; " ^ pp_exp P
  | pp_exp (Case(x,branches)) = "case " ^ x ^ " (" ^ pp_branches branches ^ ")"
  | pp_exp (Close(x)) = "close " ^ x
  | pp_exp (Wait(x,Q)) = "wait " ^ x ^ " ; " ^ pp_exp Q
  | pp_exp (Delay(t,P)) = "delay " ^ pp_time t ^ " ; " ^ pp_exp P
  | pp_exp (When(x,P)) = "when? " ^ x ^ " ; " ^ pp_exp P
  | pp_exp (Now(x,Q)) = "now! " ^ x ^ " ; " ^ pp_exp Q
  | pp_exp (Work(p,P)) = "work " ^ pp_potpos p ^ " ; " ^ pp_exp P
  | pp_exp (Pay(x,p,P)) = "pay " ^ x ^ " " ^ pp_potpos p ^ " ; " ^ pp_exp P
  | pp_exp (Get(x,p,P)) = "get " ^ x ^ " " ^ pp_potpos p ^ " ; " ^ pp_exp P
  | pp_exp (Assert(x,phi,P)) = "assert " ^ x ^ " " ^ pp_prop phi ^ " ; " ^ pp_exp P
  | pp_exp (Assume(x,phi,P)) = "assume " ^ x ^ " " ^ pp_prop phi ^ " ; " ^ pp_exp P
  | pp_exp (Imposs) = "impossible"
  | pp_exp (ExpName(x,f,es,xs)) = x ^ " <- " ^ f ^ pp_idx es ^ " <- " ^ pp_chanlist xs
  | pp_exp (Marked(marked_exp)) = pp_exp (Mark.data marked_exp)
and pp_branches (nil) = ""
  | pp_branches ((l,_,P)::nil) = l ^ " => " ^ pp_exp P
  | pp_branches ((l,_,P)::branches) =
    l ^ " => " ^ pp_exp P ^ " | " ^ pp_branches branches

fun pp_con (R.True) = ""
  | pp_con con = "{_|" ^ RP.pp_prop con ^ "}"

fun pp_chan_tp (x,A) = "(" ^ x ^ " : " ^ pp_tp A ^ ")"
fun pp_context nil = "."
  | pp_context [xA] = pp_chan_tp xA
  | pp_context (xA::D) = pp_chan_tp xA ^ " " ^ pp_context D


fun pp_decl (TpDef(a,vs,R.True,A,_)) = "type " ^ a ^ pp_vars vs ^ " = " ^ pp_tp A
  | pp_decl (TpDef(a,vs,con,A,_)) = "type " ^ a ^ pp_vars vs ^ pp_prop con ^ " = " ^ pp_tp A
  | pp_decl (TpEq(ctx,con,TpName(a,l),TpName(a',l'),_)) = "eqtype " ^ a ^ pp_idx l ^ " = " ^ a' ^ pp_idx l'
  | pp_decl (ExpDec(f,vs,con,(D,pot,zC),_)) = "proc " ^ f ^ pp_vars vs ^ pp_con con ^ " : " ^ pp_context D ^ " |" ^ pp_pot pot ^ "- " ^ pp_chan_tp zC
  | pp_decl (ExpDef(f,vs,(xs,P,x),_)) = "proc " ^ f ^ pp_vars vs ^ " : " ^ x ^ " <- " ^ pp_chanlist xs ^ " = " ^ pp_exp P
  | pp_decl (Exec(f,_)) = "exec " ^ f
  | pp_decl (Pragma(p,line,_)) = p ^ line

fun pp_msg (M.LabR(k)) = "R." ^ k
  | pp_msg (M.LabL(k)) = "L." ^ k
  | pp_msg (M.CloseR) = "closeR"
  | pp_msg (M.NowR) = "nowR"
  | pp_msg (M.NowL) = "nowL"
  | pp_msg (M.PayL(p)) = "payL " ^ pp_potpos p
  | pp_msg (M.PayR(p)) = "payR " ^ pp_potpos p
  | pp_msg (M.AssertR(phi)) = "assertR " ^ pp_prop phi
  | pp_msg (M.AssertL(phi)) = "assertL " ^ pp_prop phi

fun pp_config nil = ""
  | pp_config (Proc(t, (w, pot), P)::config) =
    "$ " ^ Int.toString(t) ^ " $ " ^ "(" ^ Int.toString(w) ^ ", " ^ Int.toString(pot) ^ ")" ^ " $ " ^ pp_exp P ^ "\n"
    ^ pp_config config
  | pp_config (Msg(t, (w, pot), M)::config) =
    "@ " ^ Int.toString(t) ^ " @ " ^ "(" ^ Int.toString(w) ^ ", " ^ Int.toString(pot) ^ ")" ^ " @ " ^ pp_msg M ^ "\n"
    ^ pp_config config

end (* structure Print *)

end (* structure Ast *)
