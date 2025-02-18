(* Validity of Types *)
(* Authors: Ankush Das <ankushd@cs.cmu.edu>
 *          Frank Pfenning <fp@cs.cmu.edu>
 *)

(*
 * Checking validity of types
 *
 * Besides being closed with respect to index variables
 * this comes in two forms: for explicit syntax and for
 * implicit syntax.  In explicit syntax, we need to make sure
 * that the constraints are sufficient to guarantee that
 * potentials, times, and index objects are all >= 0.
 *
 * For implicit syntax, we issue a warning if there are
 * positive/negative polarity transitions in types which
 * could make reconstruction incomplete
 *)

signature TYPE_VALID =
sig

    (* validity of types *)
    val closed : Arith.ctx -> Arith.arith -> Ast.ext -> unit     (* may raise ErrorMsg.Error *)
    val closed_prop : Arith.ctx -> Arith.prop -> Ast.ext -> unit (* may raise ErrorMsg.Error *)
    val closed_tp : Ast.tp_ctx -> Arith.ctx -> Ast.tp -> Ast.ext -> unit       (* may raise ErrorMsg.Error *)
    val closed_exp : Ast.tp_ctx -> Arith.ctx -> Ast.exp -> Ast.ext -> unit     (* may raise ErrorMsg.Error *)

    val valid : Ast.env -> Ast.tp_ctx -> Arith.ctx -> Arith.prop -> Ast.tp -> Ast.ext -> unit (* may raise ErrorMsg.Error *)

    (* properties of types *)
    val contractive : Ast.env -> Ast.tp -> bool

end  (* signature TYPE_VALID *)

structure TypeValid :> TYPE_VALID =
struct

structure R = Arith
structure A = Ast
structure PP = PPrint
structure E = TpError
structure C = Constraints
val ERROR = ErrorMsg.ERROR

(*********************)
(* Validity of types *)
(*********************)

fun closed ctx p ext =
    if R.closed ctx p then ()
    else ERROR ext ("arithmetic expression " ^ PP.pp_arith p ^ " not closed")

fun closed_prop ctx phi ext =
    if R.closed_prop ctx phi then ()
    else ERROR ext ("proposition " ^ PP.pp_prop phi ^ " not closed")

fun closed_tp tpctx ctx (A.Plus(choice)) ext = closed_choice tpctx ctx choice ext
  | closed_tp tpctx ctx (A.With(choice)) ext = closed_choice tpctx ctx choice ext
  | closed_tp tpctx ctx (A.Tensor(A,B)) ext = ( closed_tp tpctx ctx A ext ; closed_tp tpctx ctx B ext )
  | closed_tp tpctx ctx (A.Lolli(A,B)) ext = ( closed_tp tpctx ctx A ext ; closed_tp tpctx ctx B ext )
  | closed_tp tpctx ctx (A.One) ext = ()
  | closed_tp tpctx ctx (A.Exists(phi,A)) ext = ( closed_prop ctx phi ext ; closed_tp tpctx ctx A ext )
  | closed_tp tpctx ctx (A.Forall(phi,A)) ext = ( closed_prop ctx phi ext ; closed_tp tpctx ctx A ext )
  | closed_tp tpctx ctx (A.ExistsNat(v,A)) ext = closed_tp tpctx (v::ctx) A ext
  | closed_tp tpctx ctx (A.ForallNat(v,A)) ext = closed_tp tpctx (v::ctx) A ext
  | closed_tp tpctx ctx (A.ExistsTp(alpha,A)) ext = closed_tp (alpha::tpctx) ctx A ext
  | closed_tp tpctx ctx (A.ForallTp(alpha,A)) ext = closed_tp (alpha::tpctx) ctx A ext
  | closed_tp tpctx ctx (A.PayPot(p,A)) ext = ( closed ctx p ext ; closed_tp tpctx ctx A ext )
  | closed_tp tpctx ctx (A.GetPot(p,A)) ext = ( closed ctx p ext ; closed_tp tpctx ctx A ext )
  | closed_tp tpctx ctx (A.Next(t,A)) ext = ( closed ctx t ext ; closed_tp tpctx ctx A ext )
  | closed_tp tpctx ctx (A.Dia(A)) ext = closed_tp tpctx ctx A ext
  | closed_tp tpctx ctx (A.Box(A)) ext = closed_tp tpctx ctx A ext
  | closed_tp tpctx ctx (A.TpVar(alpha)) ext =
    if List.exists (fn alpha' => alpha = alpha') tpctx then ()
    else ERROR ext ("free type variable " ^ alpha)
  | closed_tp tpctx ctx (A.TpName(a,As,es)) ext =
    ( List.app (fn A => closed_tp tpctx ctx A ext) As
    ; List.app (fn e => closed ctx e ext) es )
and closed_choice tpctx ctx nil ext = ()
  | closed_choice tpctx ctx ((l,Al)::choices) ext =
    ( closed_tp tpctx ctx Al ext ; closed_choice tpctx ctx choices ext )

fun closed_exp tpctx ctx (A.Id _) ext = ()
  | closed_exp tpctx ctx (A.Spawn(P,Q)) ext =
    ( closed_exp tpctx ctx P ext
    ; closed_exp tpctx ctx Q ext )
  | closed_exp tpctx ctx (A.ExpName(x,f,As,es,xs)) ext =
    ( List.app (fn A => closed_tp tpctx ctx A ext) As
    ; List.app (fn e => closed ctx e ext) es )

  | closed_exp tpctx ctx (A.Lab(x,k,P)) ext = closed_exp tpctx ctx P ext
  | closed_exp tpctx ctx (A.Case(x,branches)) ext = closed_branches tpctx ctx branches ext

  | closed_exp tpctx ctx (A.Send(x,w,P)) ext = closed_exp tpctx ctx P ext
  | closed_exp tpctx ctx (A.Recv(x,y,Q)) ext = closed_exp tpctx ctx Q ext

  | closed_exp tpctx ctx (A.Close _) ext = ()
  | closed_exp tpctx ctx (A.Wait(x,Q)) ext = closed_exp tpctx ctx Q ext
                                      
  | closed_exp tpctx ctx (A.Assert(x,phi,P)) ext = (closed_prop ctx phi ext ; closed_exp tpctx ctx P ext )
  | closed_exp tpctx ctx (A.Assume(x,phi,P)) ext = (closed_prop ctx phi ext ; closed_exp tpctx ctx P ext )
  | closed_exp tpctx ctx (A.SendNat(x,e,P)) ext = (closed ctx e ext ; closed_exp tpctx ctx P ext )
  | closed_exp tpctx ctx (A.RecvNat(x,v,P)) ext = closed_exp tpctx (v::ctx) P ext
  | closed_exp tpctx ctx (A.SendTp(x,A,P)) ext = (closed_tp tpctx ctx A ext ; closed_exp tpctx ctx P ext )
  | closed_exp tpctx ctx (A.RecvTp(x,alpha,P)) ext = closed_exp (alpha::tpctx) ctx P ext
  | closed_exp tpctx ctx (A.Imposs) ext = ()

  | closed_exp tpctx ctx (A.Work(p,P)) ext = ( closed ctx p ext ; closed_exp tpctx ctx P ext )
  | closed_exp tpctx ctx (A.Pay(x,p,P)) ext = ( closed ctx p ext ; closed_exp tpctx ctx P ext )
  | closed_exp tpctx ctx (A.Get(x,p,P)) ext = ( closed ctx p ext ; closed_exp tpctx ctx P ext )

  | closed_exp tpctx ctx (A.Delay(t,P)) ext = (closed ctx t ext ; closed_exp tpctx ctx P ext )
  | closed_exp tpctx ctx (A.When(x,P)) ext = closed_exp tpctx ctx P ext
  | closed_exp tpctx ctx (A.Now(x,P)) ext = closed_exp tpctx ctx P ext

  | closed_exp tpctx ctx (A.Marked(marked_P)) ext = closed_exp tpctx ctx (Mark.data marked_P) (Mark.ext marked_P)

and closed_branches tpctx ctx nil ext = ()
  | closed_branches tpctx ctx ((l,ext',P)::branches) ext =
    ( closed_exp tpctx ctx P ext'
    ; closed_branches tpctx ctx branches ext )

(* valid_explicit env ctx con A ext = ()
 * raises ErrorMsg.Error if not a valid type
 * env must be the full environment which checking any
 * type to allow mutually recursive definitions.
 *)
fun valid_explicit env ctx con (A.Plus(choice)) ext = valid_choice env ctx con choice ext
  | valid_explicit env ctx con (A.With(choice)) ext = valid_choice env ctx con choice ext
  | valid_explicit env ctx con (A.Tensor(A,B)) ext =
    ( valid_explicit env ctx con A ext
    ; valid_explicit env ctx con B ext )
  | valid_explicit env ctx con (A.Lolli(A,B)) ext =
    ( valid_explicit env ctx con A ext
    ; valid_explicit env ctx con B ext )
  | valid_explicit env ctx con A.One ext = ()

  | valid_explicit env ctx con (A.Exists(phi,A)) ext = valid_explicit env ctx (R.And(con,phi)) A ext
  | valid_explicit env ctx con (A.Forall(phi,A)) ext = valid_explicit env ctx (R.And(con,phi)) A ext
  | valid_explicit env ctx con (A.ExistsNat(v,A)) ext = valid_explicit env (v::ctx) con A ext
  | valid_explicit env ctx con (A.ForallNat(v,A)) ext = valid_explicit env (v::ctx) con A ext
  | valid_explicit env ctx con (A.ExistsTp(alpha,A)) ext = valid_explicit env ctx con A ext (* tpctx? *)
  | valid_explicit env ctx con (A.ForallTp(alpha,A)) ext = valid_explicit env ctx con A ext (* tpctx? *)

  | valid_explicit env ctx con (A.PayPot(e,A)) ext =
    if not (C.entails ctx con (R.Ge(e,R.Int(0)))) (* allowing 0, for uniformity *)
    then ERROR ext ("potential " ^ PP.pp_arith e ^ " not positive under constraints " ^ PP.pp_prop con)
    else valid_explicit env ctx con A ext
  | valid_explicit env ctx con (A.GetPot(e,A)) ext =
    if not (C.entails ctx con (R.Ge(e,R.Int(0)))) (* allowing 0, for uniformity *)
    then ERROR ext ("potential " ^ PP.pp_arith e ^ " not positive under constraints " ^ PP.pp_prop con)
    else valid_explicit env ctx con A ext

  | valid_explicit env ctx con (A.Next(t,A)) ext =
    if not (C.entails ctx con (R.Ge(t,R.Int(0))))
    then ERROR ext ("time " ^ PP.pp_arith t ^ " not positive under constraints " ^ PP.pp_prop con)
    else valid_explicit env ctx con A ext
  | valid_explicit env ctx con (A.Dia(A)) ext = valid_explicit env ctx con A ext
  | valid_explicit env ctx con (A.Box(A)) ext = valid_explicit env ctx con A ext

  | valid_explicit env ctx con (A.TpVar(alpha)) ext =
    (* already checked that it is closed *)
    ()
  | valid_explicit env ctx con (A.TpName(a,As,es)) ext =
    (* allow forward references since 'env' is the full environment *)
    ( case A.lookup_tp env a
       of NONE => ERROR ext ("type name " ^ a ^ " undefined")
        | SOME(alphas,Ws_opt,vs,con',_) =>
          if not (List.length vs = List.length es)
          then E.error_index_number "type name" (List.length vs, List.length es) ext
          else if not (List.length alphas = List.length As)
          then E.error_tparam_number "type name" (List.length alphas, List.length As) ext
          else case List.find (fn e => not (C.entails ctx con (R.Ge(e, R.Int(0))))) es
                of SOME(e) => ERROR ext ("type index cannot shown to be positive\n"
                                         ^ C.pp_jfail con (R.Ge(e, R.Int(0))))
                 | NONE => if not (C.entails ctx con (R.apply_prop (R.zip vs es) con'))
                           then ERROR ext ("type constraint " ^ PP.pp_prop (R.apply_prop (R.zip vs es) con')
                                           ^ " not satisfied")
                           else ()
    ; List.app (fn A => valid_explicit env ctx con A ext) As )
and valid_choice env ctx con nil ext = ()
  | valid_choice env ctx con ((l,Al)::choices) ext =
    ( valid_explicit env ctx con Al ext
    ; valid_choice env ctx con choices ext )

(* Occurrences of |> and <| are restricted to
 * positive and negative positions in a type, respectively
 *)
datatype polarity = Pos | Neg | Zero | Top

(* valid_implicit env polarity A ext = ()
 * raises ErrorMsg.Error if not a valid in implicit form
 * (for reconstruction).  In particular, there must be
 * no polarity alternation on types whose process expressions
 * are implicit.
 * Assume the type has already been check as valid in the usual
 * sense.
 *)
fun valid_implicit env _ (A.Plus(choice)) ext = valid_implicit_choice env Zero choice ext
  | valid_implicit env _ (A.With(choice)) ext = valid_implicit_choice env Zero choice ext
  | valid_implicit env _ (A.Tensor(A,B)) ext =
    ( valid_implicit env Top A ext
    ; valid_implicit env Zero B ext )
  | valid_implicit env _ (A.Lolli(A,B)) ext =
    ( valid_implicit env Top A ext
    ; valid_implicit env Zero B ext )
  | valid_implicit env _ A.One ext = ()

  | valid_implicit env Neg (A as A.Exists _) ext =
    ERROR ext ("implicit type ?{...} appears directly under !{...} or <|"
               ^ PP.pp_tp_compact env A)
  | valid_implicit env Top (A as A.Exists _) ext =
    ERROR ext ("implicit type ?{...} at top level or left of tensor (*) or lolli (-o):\n"
               ^ PP.pp_tp_compact env A)
  | valid_implicit env _ (A.Exists(phi, A)) ext = valid_implicit env Pos A ext

  | valid_implicit env Pos (A as A.Forall _) ext = 
    ERROR ext ("implicit type !{...} appears directly under ?{...} or |>"
               ^ PP.pp_tp_compact env A)
  | valid_implicit env Top (A as A.Forall _) ext =
    ERROR ext ("implicit type !{...} at top level or left of tensor (*) or lolli (-o):\n"
               ^ PP.pp_tp_compact env A)
  | valid_implicit env _ (A.Forall(phi, A)) ext = valid_implicit env Neg A ext

  | valid_implicit env _ (A.ExistsNat(v,A)) ext = valid_implicit env Pos A ext
  | valid_implicit env _ (A.ForallNat(v,A)) ext = valid_implicit env Neg A ext
  | valid_implicit env _ (A.ExistsTp(alpha,A)) ext = valid_implicit env Pos A ext
  | valid_implicit env _ (A.ForallTp(alpha,A)) ext = valid_implicit env Neg A ext

  | valid_implicit env Neg (A as A.PayPot _) ext =
    ERROR ext ("implicit type |> appears directly under !{...} or <|"
               ^ PP.pp_tp_compact env A)
  | valid_implicit env Top (A as A.PayPot _) ext =
    ERROR ext ("implicit type |> at top level or left of tensor (*) or lolli (-o):\n"
               ^ PP.pp_tp_compact env A)
  | valid_implicit env _ (A.PayPot(_,A)) ext = valid_implicit env Pos A ext

  | valid_implicit env Pos (A as A.GetPot _) ext =
    ERROR ext ("implicit type <| appears directly under ?{...} or <|"
               ^ PP.pp_tp_compact env A)
  | valid_implicit env Top (A as A.GetPot _) ext =
    ERROR ext ("implicit type <| at top level or left of tensor (*) or lolli (-o):\n"
               ^ PP.pp_tp_compact env A)
  | valid_implicit env _ (A.GetPot(_,A)) ext = valid_implicit env Neg A ext

  (* propagate polarity for temporal types -fp Wed Feb 13 07:27:24 2019 *)
  | valid_implicit env polarity (A.Next(t,A)) ext = valid_implicit env polarity A ext
  | valid_implicit env polarity (A.Dia(A)) ext = valid_implicit env polarity A ext
  | valid_implicit env polarity (A.Box(A)) ext = valid_implicit env polarity A ext

  | valid_implicit env polarity (A.TpVar(alpha)) ext = () (* is this correct ??? *)

  | valid_implicit env _ (A.TpName(a,As,es)) ext =
    List.app (fn A => valid_implicit env Top A ext) As (* is Top polarity correct ??? *)

and valid_implicit_choice env pol nil ext = ()
  | valid_implicit_choice env pol ((l,Al)::choices) ext =
    ( valid_implicit env pol Al ext
    ; valid_implicit_choice env pol choices ext )

fun valid env tpctx ctx con A ext = (* tpctx currently unused *)
    ( valid_explicit env ctx con A ext
    ; case !Flags.syntax
       of Flags.Implicit => ( valid_implicit env Top A ext
                              handle ErrorMsg.Error => ( TextIO.print "% Warning: reconstruction may be incomplete\n"
                                                       ; TextIO.print "% Treating error as warning\n" ; () ) )
        | _ => () )

(* Next(t,a) is not contractive because for t = 0
 * this can lead to an infinite loop in type-checking
 *)
fun contractive env (A as A.Next(_,A')) = contractive env A'
  | contractive env (A as A.TpVar(alpha)) = false
  | contractive env (A as A.TpName(a,As,es)) = false
  | contractive env A = true

end  (* structure TpValid *)

