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
    val closed_tp : Arith.ctx -> Ast.tp -> Ast.ext -> unit       (* may raise ErrorMsg.Error *)
    val closed_exp : Arith.ctx -> Ast.exp -> Ast.ext -> unit     (* may raise ErrorMsg.Error *)

    val valid : Ast.env -> Arith.ctx -> Arith.prop -> Ast.tp -> Ast.ext -> unit (* may raise ErrorMsg.Error *)

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

fun closed_tp ctx (A.Plus(choice)) ext = closed_choice ctx choice ext
  | closed_tp ctx (A.With(choice)) ext = closed_choice ctx choice ext
  | closed_tp ctx (A.Tensor(A,B)) ext = ( closed_tp ctx A ext ; closed_tp ctx B ext )
  | closed_tp ctx (A.Lolli(A,B)) ext = ( closed_tp ctx A ext ; closed_tp ctx B ext )
  | closed_tp ctx (A.One) ext = ()
  | closed_tp ctx (A.Exists(phi,A)) ext = ( closed_prop ctx phi ext ; closed_tp ctx A ext )
  | closed_tp ctx (A.Forall(phi,A)) ext = ( closed_prop ctx phi ext ; closed_tp ctx A ext )
  | closed_tp ctx (A.ExistsNat(v,A)) ext = closed_tp (v::ctx) A ext
  | closed_tp ctx (A.ForallNat(v,A)) ext = closed_tp (v::ctx) A ext
  | closed_tp ctx (A.PayPot(p,A)) ext = ( closed ctx p ext ; closed_tp ctx A ext )
  | closed_tp ctx (A.GetPot(p,A)) ext = ( closed ctx p ext ; closed_tp ctx A ext )
  | closed_tp ctx (A.Next(t,A)) ext = ( closed ctx t ext ; closed_tp ctx A ext )
  | closed_tp ctx (A.Dia(A)) ext = closed_tp ctx A ext
  | closed_tp ctx (A.Box(A)) ext = closed_tp ctx A ext
  | closed_tp ctx (A.TpName(a,es)) ext = List.app (fn e => closed ctx e ext) es
  (* A.Dot should be impossible here *)
and closed_choice ctx nil ext = ()
  | closed_choice ctx ((l,Al)::choices) ext =
    ( closed_tp ctx Al ext ; closed_choice ctx choices ext )

fun closed_exp ctx (A.Id _) ext = ()
  | closed_exp ctx (A.Spawn(P,Q)) ext =
    ( closed_exp ctx P ext
    ; closed_exp ctx Q ext )
  | closed_exp ctx (A.ExpName(x,f,es,xs)) ext = List.app (fn e => closed ctx e ext) es

  | closed_exp ctx (A.Lab(x,k,P)) ext = closed_exp ctx P ext
  | closed_exp ctx (A.Case(x,branches)) ext = closed_branches ctx branches ext

  | closed_exp ctx (A.Send(x,w,P)) ext = closed_exp ctx P ext
  | closed_exp ctx (A.Recv(x,y,Q)) ext = closed_exp ctx Q ext

  | closed_exp ctx (A.Close _) ext = ()
  | closed_exp ctx (A.Wait(x,Q)) ext = closed_exp ctx Q ext
                                      
  | closed_exp ctx (A.Assert(x,phi,P)) ext = (closed_prop ctx phi ext ; closed_exp ctx P ext )
  | closed_exp ctx (A.Assume(x,phi,P)) ext = (closed_prop ctx phi ext ; closed_exp ctx P ext )
  | closed_exp ctx (A.SendNat(x,e,P)) ext = (closed ctx e ext ; closed_exp ctx P ext )
  | closed_exp ctx (A.RecvNat(x,v,P)) ext = closed_exp (v::ctx) P ext
  | closed_exp ctx (A.Imposs) ext = ()

  | closed_exp ctx (A.Work(p,P)) ext = ( closed ctx p ext ; closed_exp ctx P ext )
  | closed_exp ctx (A.Pay(x,p,P)) ext = ( closed ctx p ext ; closed_exp ctx P ext )
  | closed_exp ctx (A.Get(x,p,P)) ext = ( closed ctx p ext ; closed_exp ctx P ext )

  | closed_exp ctx (A.Delay(t,P)) ext = (closed ctx t ext ; closed_exp ctx P ext )
  | closed_exp ctx (A.When(x,P)) ext = closed_exp ctx P ext
  | closed_exp ctx (A.Now(x,P)) ext = closed_exp ctx P ext

  | closed_exp ctx (A.Marked(marked_P)) ext = closed_exp ctx (Mark.data marked_P) (Mark.ext marked_P)

and closed_branches ctx nil ext = ()
  | closed_branches ctx ((l,ext',P)::branches) ext =
    ( closed_exp ctx P ext'
    ; closed_branches ctx branches ext )

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

  | valid_explicit env ctx con (A.TpName(a,es)) ext =
    (* allow forward references since 'env' is the full environment *)
    (case A.lookup_tp env a
      of NONE => ERROR ext ("type name " ^ a ^ " undefined")
       | SOME(vs,con',_) =>
         if not (List.length vs = List.length es)
         then ERROR ext ("type " ^ a ^ " defined with " ^ Int.toString (List.length vs)
                         ^ " indices, but used with " ^ Int.toString (List.length es))
         else case List.find (fn e => not (C.entails ctx con (R.Ge(e, R.Int(0))))) es
               of SOME(e) => ERROR ext ("type index cannot shown to be positive\n"
                                        ^ C.pp_jfail con (R.Ge(e, R.Int(0))))
                | NONE => if not (C.entails ctx con (R.apply_prop (R.zip vs es) con'))
                          then ERROR ext ("type constraint " ^ PP.pp_prop (R.apply_prop (R.zip vs es) con')
                                          ^ " not satisfied")
                          else ())
  (* A.Dot impossible *)
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

  | valid_implicit env _ (A.TpName(a,es)) ext = ()

and valid_implicit_choice env pol nil ext = ()
  | valid_implicit_choice env pol ((l,Al)::choices) ext =
    ( valid_implicit env pol Al ext
    ; valid_implicit_choice env pol choices ext )

fun valid env ctx con A ext =
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
  | contractive env (A as A.TpName(a,es)) = false
  | contractive env A = true

end  (* structure TpValid *)

