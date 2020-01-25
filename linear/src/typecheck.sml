(* Type Checking *)
(* Use the syntax-directed rules to check the types and
 * raises ErrorMsg.Error if an error is discovered
 *)

signature TYPE_CHECK =
sig
    (* validity of types *)
    val closed : Arith.ctx -> Arith.arith -> Ast.ext -> unit     (* may raise ErrorMsg.Error *)
    val closed_prop : Arith.ctx -> Arith.prop -> Ast.ext -> unit (* may raise ErrorMsg.Error *)
    val closed_tp : Arith.ctx -> Ast.tp -> Ast.ext -> unit       (* may raise ErrorMsg.Error *)
    val closed_exp : Arith.ctx -> Ast.exp -> Ast.ext -> unit     (* may raise ErrorMsg.Error *)

    val valid : Ast.env -> Arith.ctx -> Arith.prop -> Ast.tp -> Ast.ext -> unit (* may raise ErrorMsg.Error *)

    (* properties of types *)
    val contractive : Ast.env -> Ast.tp -> bool
    val eventually_box : Ast.env -> Ast.tp -> bool
    val eventually_dia : Ast.env -> Ast.tp -> bool

    (* operations on types *)
    val decrementL : Ast.env -> Arith.ctx -> Arith.prop
                     -> Ast.tp -> Arith.arith -> Ast.ext -> Ast.tp (* may raise ErrorMsg.Error *)
    val decrementR : Ast.env -> Arith.ctx -> Arith.prop
                     -> Ast.tp -> Arith.arith -> Ast.ext -> Ast.tp (* may raise ErrorMsg.Error *)
    val strip_next0 : Ast.env -> Arith.ctx -> Arith.prop -> Ast.chan_tp -> Ast.chan_tp
    val strip_next0_context : Ast.env -> Arith.ctx -> Arith.prop -> Ast.context -> Ast.context
    val eq_tp : Ast.env -> Arith.ctx -> Arith.prop -> Ast.tp -> Ast.tp -> bool

    (* operations on approximately typed expressions (see arecon.sml) *)
    (* they synthesize the expected type *)
    val syn_call : Ast.env -> Ast.context -> Ast.exp -> Ast.ext -> Ast.context
    val syn_pot : Ast.env -> Ast.exp -> Ast.ext -> Ast.pot
    val synL : Ast.env -> (Ast.chan * Ast.expname * Arith.arith list * Ast.chan list) -> Ast.context
    val synR : Ast.env -> (Ast.chan * Ast.expname * Arith.arith list * Ast.chan list) -> Ast.chan_tp

    val syn_altR : Ast.env -> Ast.chan_tp -> Ast.label -> Ast.chan_tp
    val syn_altL : Ast.env -> Ast.context -> Ast.chan -> Ast.label -> Ast.context
    val syn_sendR : Ast.env -> Ast.chan_tp -> Ast.chan_tp
    val syn_sendL : Ast.env -> Ast.context -> Ast.chan -> Ast.context
    val syn_recvR1 : Ast.env -> Ast.context -> Ast.chan_tp -> Ast.chan -> Ast.context
    val syn_recvR2 : Ast.env -> Ast.chan_tp -> Ast.chan_tp
    val syn_recvL : Ast.env -> Ast.context -> Ast.chan -> Ast.chan -> Ast.context
    val syn_waitL : Ast.env -> Ast.context -> Ast.chan -> Ast.context

    val syn_branchesR : Ast.env -> Ast.chan_tp -> Ast.chan * Ast.choices

    val syn_branchesL : Ast.env -> Ast.context -> Ast.chan -> Ast.chan * Ast.choices

    val syn_assertR : Ast.env -> Ast.chan_tp -> Ast.chan_tp
    val syn_assertL : Ast.env -> Ast.context -> Ast.chan -> Ast.context
    val syn_assumeR : Ast.env -> Ast.chan_tp -> Ast.chan_tp
    val syn_assumeL : Ast.env -> Ast.context -> Ast.chan -> Ast.context

    val syn_sendNatR : Ast.env -> Arith.arith -> Ast.chan_tp -> Ast.chan_tp
    val syn_sendNatL : Ast.env -> Ast.context -> Arith.arith -> Ast.chan -> Ast.context
    val syn_recvNatR : Ast.env -> Arith.varname -> Ast.chan_tp -> Ast.chan_tp
    val syn_recvNatL : Ast.env -> Ast.context -> Ast.chan -> Arith.varname -> Ast.context

    (* helpers needed for recon *)
    val remove_chans : Ast.chan list -> Ast.context -> Ast.ext -> Ast.context
    val remove_chan : Ast.chan -> Ast.context -> Ast.ext -> Ast.context
    val expand : Ast.env -> Ast.tp -> Ast.tp
    val update_tp : Ast.chan_tp -> Ast.context -> Ast.context
    val lookup_context : Ast.env -> Ast.chan -> Ast.context -> Ast.ext -> Ast.tp

    (* check_exp trace env ctx con A pot P C ext = ()
     * checks that A |- P : C with potential pot
     * trace = true means print some tracinng information
     * ctx = context of free index variables
     * con = constraints
     * ext is approximation of source extent for P, if available
     * may raise ErrorMsg.Error *)
    val check_exp : bool -> Ast.env -> Arith.ctx -> Arith.prop
                    -> Ast.context -> Ast.pot -> Ast.exp -> Ast.chan_tp -> Ast.ext -> unit

end (* signature TYPE_CHECK *)

structure TypeCheck :> TYPE_CHECK =
struct

structure R = Arith
structure A = Ast
structure PP = PPrint
(* structure N = Normalize *)
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
 * type to allow mutually recursive definitions
 * Type A must be an actual type (not '.' = A.Dot)
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

(***********************)
(* Properties of types *)
(***********************)

(* Next(t,a) is not contractive because for t = 0
 * this can lead to an infinite loop in type-checking
 *)
fun contractive env (A as A.Next(_,A')) = contractive env A'
  | contractive env (A as A.TpName(a,l)) = false
  | contractive env A = true

(* needed for BoxR and DiaL rules *)
fun eventually_box env (A.Box(A)) = true
  | eventually_box env (A.Next(_,A)) = eventually_box env A
  | eventually_box env (A.TpName(a,es)) = eventually_box env (A.expd_tp env (a,es))
  | eventually_box _ _ = false

fun eventually_box_ctx env [] ext = ()
  | eventually_box_ctx env ((x,A)::D') ext =
    if eventually_box env A then eventually_box_ctx env D' ext
    else ERROR ext ("type of " ^ x ^ " : " ^ PP.pp_tp_compact env A ^ " is not patient (ie, not (n)[]A")

fun eventually_dia env (A.Dia(A)) = true
  | eventually_dia env (A.Next(_,A)) = eventually_dia env A
  | eventually_dia env (A.TpName(a,es)) = eventually_dia env (A.expd_tp env (a,es))
  | eventually_dia _ _ = false

(***********************)
(* Operations on types *)
(***********************)

fun decrementL env ctx con (A.Next(t,A)) t' ext =
    if C.entails ctx con (R.Ge(t,t'))
    then A.Next(R.minus (t,t'),A)
    else if C.entails ctx con (R.Le(t,t')) (* was: R.Lt, -fp Fri Feb  8 07:30:35 2019 *)
    then decrementL env ctx con A (R.minus (t',t)) ext
    else ERROR ext ("cannot decide: " ^ C.pp_unrel con t t')
  | decrementL env ctx con (A.Box(A)) t' ext = A.Box(A)
  | decrementL env ctx con (A.TpName(a,es)) t' ext = decrementL env ctx con (A.expd_tp env (a,es)) t' ext
  | decrementL env ctx con A t' ext =
    if C.entails ctx con (R.Eq(t',R.Int(0)))
    then A
    else ERROR ext ("left type " ^ PP.pp_tp_compact env A ^ " is neither (_)A nor []A :\n"
                    ^ C.pp_jfail con (R.Eq(t',R.Int(0))))

fun decrement env ctx con D t ext = List.map (fn (x,A) => (x,decrementL env ctx con A t ext)) D

fun decrementR env ctx con (A.Next(t,A)) t' ext =
    if C.entails ctx con (R.Ge(t,t'))
    then A.Next(R.minus(t,t'),A)
    else if C.entails ctx con (R.Le(t,t')) (* was: R.Lt, -fp Fri Feb  8 07:30:47 2019 *)
    then decrementR env ctx con A (R.minus (t',t)) ext
    else ERROR ext ("cannot decide: " ^ C.pp_unrel con t' t)
  | decrementR env ctx con (A.Dia(A)) t' ext = A.Dia(A)
  | decrementR env ctx con (A.TpName(a,es)) t' ext = decrementR env ctx con (A.expd_tp env (a,es)) t' ext
  | decrementR env ctx con A t' ext =
    if C.entails ctx con (R.Eq(t',R.Int(0)))
    then A
    else ERROR ext ("right type " ^ PP.pp_tp_compact env A ^ " is neither (_)A or <>A :\n"
                    ^ C.pp_jfail con (R.Eq(t',R.Int(0))))

(*****************)
(* Type equality *)
(*****************)

(* eq_id ctx con e e' iff ctx ; con |= e = e' *)
fun eq_id ctx con e e' = C.entails ctx con (R.Eq(e,e'))

(* eq_idx ctx con es es', assumes |es| = |es'| *)
fun eq_idx ctx con nil nil = true
  | eq_idx ctx con (e::es) (e'::es') =
      eq_id ctx con e e' andalso eq_idx ctx con es es'

(* Type equality, equirecursively defined *)

(* Structural equality *)
(* mem_env env a a' => SOME(CTX,CON,TpName(a,es),TpName(a',es')) if exists in env *)
fun mem_env (A.TpEq(CTX,CON,A as A.TpName(B,ES),A' as A.TpName(B',ES'),_)::env) a a' =
    if B = a andalso B' = a'
    then SOME(CTX,CON,(A,A'))
    else if B = a' andalso B' = a
    then SOME(CTX,CON,(A',A))   (* flip! *)
    else mem_env env a a'
  | mem_env (_::env) a a' = mem_env env a a'
  | mem_env nil a a' = NONE

(* mem_env env seen a a' => SOME(CTX,CON,TpName(a,es),TpName(a',es')) if exists in seen *)
fun mem_seen env ((E as (CTX,CON,(A as A.TpName(B, ES), A' as A.TpName(B', ES'))))::seen) a a' =
    if B = a andalso B' = a'
    then SOME(CTX,CON,(A,A'))
    else if B = a' andalso B' = a
    then SOME(CTX,CON,(A',A))
    else mem_seen env seen a a'
  | mem_seen env (_::seen) a a' = mem_seen env seen a a'
  | mem_seen env nil a a' = mem_env env a a'

fun fresh v = "%" ^ v

fun gen_fresh nil = (nil, nil)
  | gen_fresh (v::vs) =
    let val fv = fresh v
        val (fvs, sigma) = gen_fresh vs
    in
      (fv::fvs,(v, R.Var(fv))::sigma)
    end

fun gen_eq nil nil = R.True
  | gen_eq (E::ES) (e::es) = R.And(R.Eq(E,e), gen_eq ES es)

(* gen_prop_eq FCTX FCON FES es FES' es' => FCTX |= FCON /\ FES = es /\ FES' = es' *)
fun gen_prop_eq FCTX FCON FES es FES' es' =
    let val eqs = gen_eq FES es
        val eqs' = gen_eq FES' es'
        val and_prop = R.And(FCON, R.And(eqs, eqs'))
        (* val () = TextIO.print (PP.pp_prop and_prop ^ "\n") *)
        val nnf_prop = R.nnf and_prop
        val exists_prop = R.elim_vars FCTX nnf_prop (* exists_prop is in NNF, but not using it *)
    in
        exists_prop
    end

(* stripnext0 ctx con A = A' preserves definitions for tracing
 * purposes but strips off all prefixes (t)A' if con |= t = 0.
 * For use in type equality, see aggregate_nexts
 *)
fun stripnext0 env ctx con (A as A.Next(t,A')) =
    if C.entails ctx con (R.Eq(t,R.Int(0)))
    then stripnext0 env ctx con A'
    else A
  | stripnext0 env ctx con A = A

fun strip_next0 env ctx con (x,A) = (x, stripnext0 env ctx con A)
fun strip_next0_context env ctx con D = List.map (fn xA => strip_next0 env ctx con xA) D

(* aggregate_nexts' env ctx con s A = A'
 * where all initial next-time operators in A are added to S.
 * If the result is 0, the next-time operators is stripped entirely.
 *)
fun aggregate_nexts' env ctx con s (A.Next(t,A')) =
    aggregate_nexts' env ctx con (R.plus(s,t)) A'
  | aggregate_nexts' env ctx con s (A.TpName(a,es)) =
    aggregate_nexts' env ctx con s (A.expd_tp env (a,es))
  | aggregate_nexts' env ctx con s A = (* A <> Next _ *)
    if C.entails ctx con (R.Eq(s,R.Int(0)))
    then A
    else A.Next(s,A)

(* aggregate_nexts env ctx con A = A', where initial next-time
 * operators in A are combined into 0 or 1 operators.
 * Type definitions are not expanded unless A is a Next(_).
 * This ensures that, for example, ()()A and ({2})A are considered equal.
 *)
fun aggregate_nexts env ctx con (A as A.Next(t,A')) =
    aggregate_nexts' env ctx con t A'
  | aggregate_nexts env ctx con A = A

(* eq_tp env con seen A A' = true if (A = A'), defined coinductively *)
fun eq_tp' env ctx con seen A A' =
    eq_tp env ctx con seen
          (aggregate_nexts env ctx con A)
          (aggregate_nexts env ctx con A')

and eq_tp env ctx con seen (A.Plus(choice)) (A.Plus(choice')) =
    eq_choice env ctx con seen choice choice'
  | eq_tp env ctx con seen (A.With(choice)) (A.With(choice')) =
    eq_choice env ctx con seen choice choice'
  
  | eq_tp env ctx con seen (A.Tensor(A,B)) (A.Tensor(A',B')) =
    eq_tp' env ctx con seen A A'
    andalso eq_tp' env ctx con seen B B'
  | eq_tp env ctx con seen (A.Lolli(A,B)) (A.Lolli(A',B')) =
    eq_tp' env ctx con seen A A'
    andalso eq_tp' env ctx con seen B B'

  | eq_tp env ctx con seen (A.One) (A.One) = true

  | eq_tp env ctx con seen (A.Exists(phi,A)) (A.Exists(phi',A')) =
    C.equiv ctx con phi phi'
    andalso eq_tp' env ctx (R.And(con,phi)) seen A A'
    (* for now, require equality even in the presence of contradictory constraints *)
    (* orelse C.contradictory ctx con phi *)
  | eq_tp env ctx con seen (A.Forall(phi,A)) (A.Forall(phi',A')) =
    C.equiv ctx con phi phi'
    andalso eq_tp' env ctx (R.And(con,phi)) seen A A'
    (* for now, require equality even in the presence of contradictory constraints *)
    (* orelse C.contradictory ctx con phi *)

  | eq_tp env ctx con seen (A.ExistsNat(v,A)) (A.ExistsNat(v',A')) =
    eq_tp_bind env ctx con seen (v,A) (v',A')
  | eq_tp env ctx con seen (A.ForallNat(v,A)) (A.ForallNat(v',A')) =
    eq_tp_bind env ctx con seen (v,A) (v',A')

  | eq_tp env ctx con seen (A.PayPot(p,A)) (A.PayPot(p',A')) =
    eq_id ctx con p p' andalso eq_tp' env ctx con seen A A'
  | eq_tp env ctx con seen (A.GetPot(p,A)) (A.GetPot(p',A')) = 
    eq_id ctx con p p' andalso eq_tp' env ctx con seen A A'

  | eq_tp env ctx con seen (A.Next(t,A)) (A.Next(t',A')) =
    eq_id ctx con t t' andalso eq_tp' env ctx con seen A A'
  | eq_tp env ctx con seen (A.Box(A)) (A.Box(A')) =
    eq_tp' env ctx con seen A A'
  | eq_tp env ctx con seen (A.Dia(A)) (A.Dia(A')) =
    eq_tp' env ctx con seen A A'

  | eq_tp env ctx con seen (A as A.TpName(a,es)) (A' as A.TpName(a',es')) =
    if a = a'
    (* reflexivity *)
    then case !Flags.equality
          of Flags.SubsumeRefl => eq_idx ctx con es es' orelse eq_name_name env ctx con seen A A' (* both *)
           | Flags.Subsume => eq_name_name env ctx con seen A A' (* only coinductive equality *)
           | Flags.Refl => eq_idx ctx con es es'                 (* only reflexivity *)
    else eq_name_name env ctx con seen A A' (* coinductive type equality *)
  | eq_tp env ctx con seen (A as A.TpName(a,es)) A' =
    eq_tp' env ctx con seen (A.expd_tp env (a,es)) A'
  | eq_tp env ctx con seen A (A' as A.TpName(a',es')) =
    eq_tp' env ctx con seen A (A.expd_tp env (a',es'))

  | eq_tp env ctx con seen A A' = false

and eq_tp_bind env ctx con seen (v,A) (v',A') =
    let val sigma = R.zip ctx (R.create_idx ctx)
        val w = R.fresh_var sigma v
        val wA = A.apply_tp ((v, R.Var(w))::sigma) A
        val wA' = A.apply_tp ((v', R.Var(w))::sigma) A'
    in eq_tp' env (w::ctx) con seen wA wA' end

and eq_choice env ctx con seen nil nil = true
  | eq_choice env ctx con seen ((l,A)::choice) ((l',A')::choice') = (* order must be equal *)
    l = l' andalso eq_tp' env ctx con seen A A'
    andalso eq_choice env ctx con seen choice choice'
  | eq_choice env ctx con seen ((l,A)::choice) nil = false
  | eq_choice env ctx con seen nil ((l',A')::choice') = false

and eq_name_name env ctx con seen (A as A.TpName(a,es)) (A' as A.TpName(a',es')) =
    case mem_seen env seen a a'
     of NONE => eq_tp' env ctx con ((ctx,con,(A,A'))::seen)
                       (A.expd_tp env (a,es)) (A.expd_tp env (a',es'))
      | SOME(CTX,CON, (A.TpName(_,ES), A.TpName(_,ES'))) =>
        let val (FCTX,sigma) = gen_fresh CTX
            val FCON = R.apply_prop sigma CON
            val FES = R.apply_list sigma ES
            val FES' = R.apply_list sigma ES'
            (* val () = TextIO.print (PP.pp_prop con ^ " |- ") *)
            val phi = gen_prop_eq FCTX FCON FES es FES' es'
            (* val () = TextIO.print (PP.pp_prop phi ^ "\n") *)
            val result = C.entails ctx con phi (* could be trusting non-linear *)
            (* val () = if result then TextIO.print("true\n") else TextIO.print("false\n") *)
        in
            result
        end

(*****************************)
(* Operations on expressions *)
(*****************************)

(* expd env a{es} = A for a type a{vs} = A *)
fun expd env (A.TpName(a,es)) = A.expd_tp env (a,es)
fun expand env (A.TpName(a,es)) = expand env (A.expd_tp env (a,es))
  | expand env A = A

(* match_contexts env ctx con D D' ext = ()
 * D is typing of channels passed to a process f in call
 * D' is typing of parameter channels in declaration of process f
 * Order should match, types should match, channel names may be different
 *)
fun match_contexts env ctx con ((x,A)::D) ((x',A')::D') ext =
    if eq_tp' env ctx con nil A A'
    then match_contexts env ctx con D D' ext
    else let val (x_len,x'_len) = (String.size x, String.size x')
             val var_len = Int.max(x_len, x'_len)
             val (x_str,x'_str) = (StringCvt.padRight #" " var_len x,
                                   StringCvt.padRight #" " var_len x')
         in
             ERROR ext ("type mismatch in call:\n"
                        ^ "expected " ^ x'_str ^ " : " ^ PP.pp_tp_compact env A' ^ "\n"
                        ^ "found    " ^ x_str ^ " : " ^ PP.pp_tp_compact env A)
         end
  | match_contexts env ctx con nil nil ext = ()
  | match_contexts env ctx con D D' ext =
    ERROR ext ("wrong number of arguments in call:\n"
               ^ "expected " ^ PP.pp_context_compact env D' ^ "\n"
               ^ "found    " ^ PP.pp_context_compact env D)

fun lookup_context env x ((y,A)::D') ext = if x = y then expand env A else lookup_context env x D' ext
  | lookup_context env x nil ext = ERROR ext ("channel " ^ x ^ " not present in context")

fun update_tp (x,A) ((y,B)::D') = if x = y then (x,A)::D' else (y,B)::(update_tp (x,A) D')
    (* nil should be impossible *)

fun remove_chan x ((y,B)::D') ext = if x = y then D' else (y,B)::(remove_chan x D' ext)
  | remove_chan x nil ext = ERROR ext ("channel " ^ x ^ " not present in context")

fun remove_chans (x::xs) D ext = remove_chans xs (remove_chan x D ext) ext
  | remove_chans nil D ext = D

fun gen_context env xs D ext = List.map (fn x => (x,lookup_context env x D ext)) xs

fun exists x ((y,A)::D) = if x = y then true else exists x D
  | exists x [] = false

(* zip_check f vs es ext = [es/vs]
 * raises ErrorMsg.Error if |es| <> |vs|
 *)
fun zip_check f vs es ext =
    let val () = if List.length es = List.length vs then ()
                 else ERROR ext ("process " ^ f ^ " called with incorrect number of indices:\n"
                                 ^ "expected " ^ Int.toString (List.length vs) ^ "\n"
                                 ^ "found " ^ Int.toString (List.length es))
    in R.zip vs es end

(* expd_expdec_check env f{es} ext = [es/vs](con, (A, p, C))
 * if vs ; con ; A |{p}- f : C
 * raises ErrorMsg.Error if f undeclared or |es| <> |vs|
 *)
fun expd_expdec_check env (f,es) ext =
    (case A.lookup_expdec env f
      of SOME(vs,con,(D,pot,zC)) =>
         let val sg = zip_check f vs es ext
         in (R.apply_prop sg con, (A.apply_context sg D, R.apply sg pot, A.apply_chan_tp sg zC)) end
       | NONE => E.error_undeclared (f, ext))

(* syn_call env D (x <- f{es} <- xs) ext = (x : B) :: (D / [es/vs]D')
 * if vs ; con ; D' |{p}- f : B
 * raises ErrorMsg.Error if f undeclared or |es| <> |vs|
 *)
fun syn_call env D (P as A.ExpName(x,f,es,xs)) ext =
    (case A.lookup_expdec env f
      of SOME(vs,con',(D',pot',(y,B'))) =>
         let val sg = zip_check f vs es ext
             val B = A.apply_tp sg B'
         in (x,B)::remove_chans xs D ext end
       | NONE => ERROR ext ("process " ^ f ^ " undeclared"))
  | syn_call env D (A.Marked(marked_P)) ext = (* Q: preserve mark? *)
    syn_call env D (Mark.data marked_P) (Mark.ext marked_P)
  | syn_call env D P ext = ERROR ext ("call must be a process name")

(* syn_pot env D (x <- f{es} <- xs) ext = [es/vs]p
 * if vs ; con ; D' |{p}- f : B
 * raises ErrorMsg.Error if f undeclared or |es| <> |vs|
 *)
fun syn_pot env (P as A.ExpName(x,f,es,xs)) ext =
    (case A.lookup_expdec env f
      of SOME(vs,con',(D',pot',(y,B'))) =>
         let val sg = zip_check f vs es ext
             val pot = R.apply sg pot'
         in pot end
       | NONE => ERROR ext ("process " ^ f ^ " undeclared"))
  | syn_pot env (A.Marked(marked_P)) ext = (* Q: preserve mark? *)
    syn_pot env (Mark.data marked_P) (Mark.ext marked_P)
  | syn_pot env P ext = ERROR ext ("call must be a process name")

(* synL env (f,es) = A where D |- f : _, approximately *)
fun synL env (y, f, es, xs) =
    (case A.expd_expdec env (f, es)
      of SOME(con, (D, pot, zC)) => ListPair.mapEq (fn (x,(x',A')) => (x,A')) (xs,D)
         (* NONE impossible, since f{es} approximately typed *)
    )

(* synR env (f,es) = C where _ |- f : C, approximately *)
fun synR env (y, f, es, xs) =
    (case A.expd_expdec env (f,es)
      of SOME(con, (D, pot, (z,C))) => (y,C)
         (* NONE impossible, since f{es} approximately typed *)
    )

(* synLR env (f,es) = (D,pot,C) where D |{pot}- f : C, approximately *)
fun synLR env (f, es) =
    (case A.expd_expdec env (f,es)
      of SOME(con, (D, pot, zC)) => (D, pot, zC)
         (* NONE impossible, since f{es} approximately typed *)
    )

(* syn_altR env z +(l : Al)_(l in L) k = (z,Ak), assumes k in L *)
fun syn_altR' env z (A.Plus(choices)) k = (z, Option.valOf (A.lookup_choice choices k))
fun syn_altR env (z,C) k = syn_altR' env z (expand env C) k

(* syn_altL env x &(l : Al)_(l in L) k = (x,Ak), assumes k in L *)
fun syn_altL' env x (A.With(choices)) k D = (x, Option.valOf (A.lookup_choice choices k))::D
fun syn_altL env ((x',A)::D') x k =
    if x' = x
    then syn_altL' env x' (expand env A) k D'
    else (x',A)::syn_altL env D' x k
    (* nil impossile by approx typing *)

(* syn_sendR env z (A * B) = (z,B) *)
fun syn_sendR' env z (A.Tensor(A,B)) = (z,B)
fun syn_sendR env (z,C) = syn_sendR' env z (expand env C)

(* syn_sendL env x (A -o B) = (x,B) *)
fun syn_sendL' env x (A.Lolli(A,B)) D = (x,B)::D
fun syn_sendL env ((x',A)::D') x  =
    if x' = x then syn_sendL' env x' (expand env A) D'
    else (x',A)::syn_sendL env D' x
    (* nil impossible by approx typing *)

fun syn_recvR1' env y (A.Lolli(A,B)) D = (y,A)::D
fun syn_recvR1 env D (z,C) y = syn_recvR1' env y (expand env C) D

fun syn_recvR2' env z (A.Lolli(A,B)) = (z,B)
fun syn_recvR2 env (z,C) = syn_recvR2' env z (expand env C)

fun syn_recvL' env (y,x) (A.Tensor(A,B)) D = (y,A)::(x,B)::D
fun syn_recvL env ((x',A)::D') x y =
    if x' = x then syn_recvL' env (y,x) (expand env A) D'
    else (x',A)::syn_recvL env D' x y

fun syn_waitL' env () (A.One) D = D
fun syn_waitL env ((x',A)::D') x =
    if x = x' then syn_waitL' env () (expand env A) D'
    else (x',A)::syn_waitL env D' x

fun syn_branchesR' env z (A.With(choices)) = (z,choices)
fun syn_branchesR env (z,C) = syn_branchesR' env z (expand env C)

fun syn_branchesL' env x (A.Plus(choices)) = (x,choices)
fun syn_branchesL env ((x',A)::D') x =
    if x = x' then syn_branchesL' env x (expand env A)
    else syn_branchesL env D' x

fun syn_assertR' env z (A.Exists(phi,C)) = (z,C)
fun syn_assertR env (z,C) = syn_assertR' env z (expand env C)

fun syn_assertL' env x (A.Forall(phi,A)) D = (x,A)::D
fun syn_assertL env ((x',A)::D') x =
    if x = x' then syn_assertL' env x (expand env A) D'
    else (x',A)::syn_assertL env D' x

fun syn_assumeR' env z (A.Forall(phi,C)) = (z,C)
fun syn_assumeR env (z,C) = syn_assumeR' env z (expand env C)

fun syn_assumeL' env x (A.Exists(phi,A)) D' = (x,A)::D'
fun syn_assumeL env ((x',A)::D') x =
    if x = x' then syn_assumeL' env x (expand env A) D'
    else (x',A)::syn_assumeL env D' x

fun syn_sendNatR' env z e (A.ExistsNat(v,C)) = (z,A.apply_tp [(v,e)] C)
fun syn_sendNatR env e (z,C) = syn_sendNatR' env z e (expand env C)

fun syn_sendNatL' env x e (A.ForallNat(v,A)) D = (x,A.apply_tp [(v,e)] A)::D
fun syn_sendNatL env ((x',A)::D') e x =
    if x = x' then syn_sendNatL' env x e (expand env A) D'
    else (x',A)::syn_sendNatL env D' e x

fun syn_recvNatR' env v' z (A.ForallNat(v,C)) = (z,A.apply_tp [(v,R.Var(v'))] C)
fun syn_recvNatR env v' (z,C) = syn_recvNatR' env v' z (expand env C)

fun syn_recvNatL' env x v' (A.ExistsNat(v,A)) D' = (x,A.apply_tp [(v,R.Var(v'))] A)::D'
fun syn_recvNatL env ((x',A)::D') x v' =
    if x = x' then syn_recvNatL' env x v' (expand env A) D'
    else (x',A)::syn_recvNatL env D' x v'

(*************************************)
(* Type checking process expressions *)
(*************************************)

(* check_explist_pos ctx con es ext = ()
 * if ctx ; con |= e >= 0 for all e in es
 * raises ErrorMsg.Error otherwise
 *)
fun check_explist_pos ctx con (nil) ext = ()
  | check_explist_pos ctx con (e::es) ext =
    if not(C.entails ctx con (R.Ge(e, R.Int(0))))
    then ERROR ext ("index cannot be shown to be positive: " ^ C.pp_jfail con (R.Ge(e, R.Int(0))))
    else check_explist_pos ctx con es ext

(* check_exp trace env ctx con D pot P C = () if ctx ; con ; D |{pot}- P : C
 * raises ErrorMsg.Error otherwise
 * assumes ctx ; con |= D valid
 *         ctx ; con |= C valid
 *         ctx ; con |= pot nat
 *
 * trace = true means to print some tracing information
 *
 * entry point is check_exp'
 *
 * We expand type definitions lazily, based on the direction of
 * interactions.  This is done so tracing (if enabled) or error
 * message are more intelligible.
 *)
fun check_exp' trace env ctx con D pot P zC ext =
    ( if trace
      then TextIO.print (PP.pp_exp_prefix env P ^ " : "
                         ^ PP.pp_tpj_compact env D pot zC ^ "\n")
      else ()

      (* strip zero delays *)
    ; check_exp trace env ctx con (strip_next0_context env ctx con D) pot P (strip_next0 env ctx con zC) ext )

and fwd trace env ctx con D pot (A.Id(x,y)) zC ext =
    let val A = lookup_context env y D ext
        val C = lookup_context env x [zC] ext
        val () = if eq_tp' env ctx con nil A C then ()
                 else ERROR ext ("type mismatch in forward:\n"
                                 ^ "expected " ^ y ^ " : " ^ PP.pp_tp_compact env C ^ "\n"
                                 ^ "found    " ^ y ^ " : " ^ PP.pp_tp_compact env A)
        val () = if not (C.entails ctx con (R.Eq(pot, R.Int(0))))
                 then ERROR ext ("unconsumed potential: " ^ C.pp_jfail con (R.Eq(pot, R.Int(0))))
                 else ()
        val () = if List.length D <> 1
                 then ERROR ext ("context " ^ PP.pp_context_compact env D ^ " not singleton for fwd")
                 else ()
    in () end

and spawn trace env ctx con D pot (A.Spawn(A.ExpName(x,f,es,xs),Q)) zC ext =
    (case expd_expdec_check env (f,es) ext
      of (con',(D',pot',(z',B))) =>
         let val () = if List.length D' = List.length xs then ()
                      else ERROR ext ("incorrect number of arguments in call:\n"
                                      ^ "expected " ^ Int.toString (List.length D') ^ "\n"
                                      ^ "found    " ^ Int.toString (List.length xs))
             val cutD = gen_context env xs D ext
             val () = match_contexts env ctx con cutD D' ext (* should this be after entails? *)
             val () = if not (C.entails ctx con (R.Ge(pot, pot')))
                      then ERROR ext ("insufficient potential to spawn: " ^ C.pp_jfail con (R.Ge(pot, pot')))
                      else ()
             val () = if not (C.entails ctx con (R.Ge(pot',R.Int(0)))) (* and potential >= 0 *)
                      then ERROR ext ("potential not positive: " ^ C.pp_jfail con (R.Ge(pot', R.Int(0))))
                      else ()
             val () = check_explist_pos ctx con es ext
             val () = if not (C.entails ctx con con')
                      then ERROR ext ("constraint not entailed: " ^ C.pp_jfail con con')
                      else ()
             val contD = remove_chans xs D ext
             val () = if exists x (zC::D) then ERROR ext ("variable " ^ x ^ " not fresh") else ()
         in
             check_exp' trace env ctx con ((x,B)::contD) (R.minus(pot,pot')) Q zC ext
         end
    )
  | spawn trace env ctx con D pot (A.Spawn(A.Marked(marked_P),Q)) zC ext =
    spawn trace env ctx con D pot (A.Spawn(Mark.data marked_P,Q)) zC (Mark.ext marked_P)


and expname trace env ctx con D pot (A.ExpName(x,f,es,xs)) (z,C) ext =
    (* verify the type, but also make sure f is defined somewhere *)
    (* eq_context expects lists in the same order, no reordering *)
    if x <> z
    then ERROR ext ("name mismatch: " ^ x ^ " <> " ^ z)
    else
    (case expd_expdec_check env (f,es) ext
      of (con',(D',pot',(z',C'))) =>
         let val () = if List.length D' = List.length xs then ()
                      else ERROR ext ("incorrect number of arguments in tail call:\n"
                                      ^ "expected " ^ Int.toString (List.length D')
                                      ^ "found    " ^ Int.toString (List.length xs))
             val cutD = gen_context env xs D ext
             val () = match_contexts env ctx con cutD D' ext
             val () = if eq_tp' env ctx con nil C' C then ()
                      else ERROR ext ("type mismatch in tail call:\n"
                                      ^ "expected " ^ z ^ " : " ^ PP.pp_tp_compact env C' ^ "\n"
                                      ^ "found    " ^ z ^ " : " ^ PP.pp_tp_compact env C)
             val () = if not (C.entails ctx con (R.Eq(pot, pot')))
                      then ERROR ext ("potential mismatch: " ^ C.pp_jfail con (R.Eq(pot, pot')))
                      else ()
             val () = check_explist_pos ctx con es ext
             val () = if not (C.entails ctx con con')
                      then ERROR ext ("constraint not entailed: " ^ C.pp_jfail con con')
                      else ()
             val contD = remove_chans xs D ext
             val () = if List.length contD > 0
                      then ERROR ext ("unconsumed channels " ^ PP.pp_context_compact env contD ^ " at tail call")
                      else ()
         in () end
    )

and plusR trace env ctx con D pot (A.Lab(x,k,P)) (z,C as A.Plus(choices)) ext (* z = x *) =
    (case A.lookup_choice choices k
      of SOME(Ck) => check_exp' trace env ctx con D pot P (z,Ck) ext
      | NONE => E.error_label_invalid env (k, C, ext))
  | plusR trace env ctx con D pot (A.Lab(x,k,P)) (z,C) ext =
    ERROR ext ("type mismatch for " ^ x ^ ": expected internal choice, found: " ^ PP.pp_tp_compact env C)

and withL trace env ctx con D (A as A.With(choices)) pot (A.Lab(x,k,P)) zC ext (* z != x *) =
    (case A.lookup_choice choices k
      of SOME(Ak) => check_exp' trace env ctx con (update_tp (x,Ak) D) pot P zC ext
      | NONE => E.error_label_invalid env (k, A, ext))
  | withL trace env ctx cond D A pot (A.Lab(x,k,P)) zC ext =
    ERROR ext ("type mismatch for " ^ x ^ ": expected external choice, found: " ^ PP.pp_tp_compact env A)

(* check_branchesR trace env ctx con A branches choices = ()
 * for provider of external choice &{...}
 *)
and check_branchesR trace env ctx con D pot nil (z,nil) ext = ()
  | check_branchesR trace env ctx con D pot ((l,ext',P)::branches) (z,(l',C)::choices) ext =
    (* require exact order *)
    ( if trace then TextIO.print ("| " ^ l ^ " => \n") else ()
    ; if l = l' then () else E.error_label_mismatch (l, l', ext')
    ; check_exp' trace env ctx con D pot P (z,C) ext
    ; check_branchesR trace env ctx con D pot branches (z,choices) ext )
  | check_branchesR trace env ctx con D pot ((l,ext',P)::_) (z,nil) ext = E.error_label_missing_alt (l, ext')
  | check_branchesR trace env ctx con D pot nil (z,(l',C)::_) ext = E.error_label_missing_branch (l', ext)

and withR trace env ctx con D pot (A.Case(x,branches)) (z,A.With(choices)) ext (* z = x *) =
    check_branchesR trace env ctx con D pot branches (z,choices) ext
  | withR trace env ctx con D pot (A.Case(x,branches)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected external choice, found: " ^ PP.pp_tp_compact env C)

(* check_branchesL env ctx con choices branches C ext = ()
 * for client of internal choice +{...}
 *)
and check_branchesL trace env ctx con D (x,nil) pot nil zC ext = ()
  | check_branchesL trace env ctx con D (x,(l,A)::choices) pot ((l',ext',P)::branches) zC ext =
    (* require exact order *)
    ( if trace then TextIO.print ("| " ^ l' ^ " => \n") else ()
    ; if l = l' then () else E.error_label_mismatch (l, l', ext')
    ; check_exp' trace env ctx con (update_tp (x,A) D) pot P zC ext
    ; check_branchesL trace env ctx con D (x,choices) pot branches zC ext )
  | check_branchesL trace env ctx con D (x,(l,A)::_) pot nil zC ext = E.error_label_missing_branch (l, ext)
  | check_branchesL trace env ctx con D (x,nil) pot ((l',ext',P)::_) zC ext = E.error_label_missing_alt (l', ext')

and plusL trace env ctx con D (A.Plus(choices)) pot (A.Case(x,branches)) zC ext (* z != x *) =
    check_branchesL trace env ctx con D (x,choices) pot branches zC ext
  | plusL trace env ctx con D A pot (A.Case(x,branches)) zC ext =
    ERROR ext ("type mismatch for " ^ x ^ ": expected internal choice, found: " ^ PP.pp_tp_compact env A)

and tensorR trace env ctx con D pot (A.Send(x,w,P)) (z,A.Tensor(A,B)) ext (* z = x *) =
    let val A' = lookup_context env w D ext
        val () = if eq_tp' env ctx con nil A A' then ()
                 else ERROR ext ("type of " ^ w ^ ": " ^ PP.pp_tp_compact env A ^
                                 " not equal " ^ PP.pp_tp_compact env A')
    in
    check_exp' trace env ctx con (remove_chan w D ext) pot P (z,B) ext
    end
  | tensorR trace env ctx con D pot (A.Send(x,w,P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected tensor, found: " ^ PP.pp_tp_compact env C)

and lolliL trace env ctx con D (A.Lolli(A,B)) pot (A.Send(x,w,Q)) zC ext (* z != x *) =
    let val A' = lookup_context env w D ext
        val () = if eq_tp' env ctx con nil A A' then ()
                 else ERROR ext ("type of " ^ w ^ ": " ^ PP.pp_tp_compact env A ^
                                 " not equal " ^ PP.pp_tp_compact env A')
    in
    check_exp' trace env ctx con (update_tp (x,B) (remove_chan w D ext)) pot Q zC ext
    end
  | lolliL trace env ctx con D A pot (A.Send(x,w,Q)) zC ext =
    ERROR ext ("type mismatch for " ^ x ^ ": expected lolli, found: " ^ PP.pp_tp_compact env A)

and lolliR trace env ctx con D pot (A.Recv(x,y,P)) (z,A.Lolli(A,B)) ext (* z = x *) =
    if exists y ((z,A.Lolli(A,B))::D)
    then ERROR ext ("variable " ^ y ^ " not fresh")
    else check_exp' trace env ctx con ((y,A)::D) pot P (z,B) ext
  | lolliR trace env ctx con D pot (A.Recv(x,y,P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected lolli, found: " ^ PP.pp_tp_compact env C)

and tensorL trace env ctx con D (A.Tensor(A,B)) pot (A.Recv(x,y,Q)) zC ext (* z != x *) =
    if exists y (zC::D)
    then ERROR ext ("variable " ^ y ^ " not fresh")
    else check_exp' trace env ctx con ((y,A)::(update_tp (x,B) D)) pot Q zC ext
  | tensorL trace env ctx con D A pot (A.Recv(x,y,Q)) zC ext =
    ERROR ext ("type mismatch for " ^ x ^ ": expected tensor, found: " ^ PP.pp_tp_compact env A)

and oneR trace env ctx con D pot (A.Close(x)) (z,A.One) ext (* z = x *) =
    if List.length D > 0
    then ERROR ext ("context " ^ PP.pp_context_compact env D ^ " not empty while closing")
    else if not (C.entails ctx con (R.Eq(pot, R.Int(0))))
    then ERROR ext ("unconsumed potential: " ^ C.pp_jfail con (R.Eq(pot, R.Int(0))))
    else ()
  | oneR trace env ctx con D pot (A.Close(x)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected one, found: " ^ PP.pp_tp_compact env C)

and oneL trace env ctx con D (A.One) pot (A.Wait(x,Q)) zC ext (* z != x *) =
    check_exp' trace env ctx con (remove_chan x D ext) pot Q zC ext
  | oneL trace env ctx con D A pot (A.Wait(x,Q)) zC ext =
    ERROR ext ("type mismatch for " ^ x ^ ": expected one, found: " ^ PP.pp_tp_compact env A)

and existsR trace env ctx con D pot (A.Assert(x,phi,P)) (z,A.Exists(phi',C)) ext (* z = x *) =
    if not (C.entails ctx con phi)
    then ERROR ext ("assertion not entailed: " ^ C.pp_jfail con phi)
    else if not (C.entails ctx con phi') (* equivalent would be con, phi |= phi' *)
    then ERROR ext ("type constraint not entailed: " ^ C.pp_jfail con phi')
    else check_exp' trace env ctx con D pot P (z,C) ext
  | existsR trace env ctx con D pot (A.Assert(x,phi,P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected exists, found: " ^ PP.pp_tp_compact env C)

and forallL trace env ctx con D (A.Forall(phi',A)) pot (A.Assert(x,phi,P)) zC ext (* z != x *) =
    if not (C.entails ctx con phi)
    then ERROR ext ("assertion not entailed: " ^ C.pp_jfail con phi)
    else if not (C.entails ctx con phi') (* equivalent would be con, phi |= phi' *)
    then ERROR ext ("type constraint not entailed: " ^ C.pp_jfail con phi')
    else check_exp' trace env ctx con (update_tp (x,A) D) pot P zC ext
  | forallL trace env ctx con D A pot (A.Assert(x,phi,P)) zC ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected forall, found: " ^ PP.pp_tp_compact env A)

and forallR trace env ctx con D pot (A.Assume(x,phi,P)) (z,A.Forall(phi',C)) ext (* z = x *) =
    if not (C.entails ctx (R.And(con,phi')) phi)
    then ERROR ext ("assumption not entailed: " ^ C.pp_jfail (R.And(con,phi')) phi)
    else check_exp' trace env ctx (R.And(con,phi)) D pot P (z,C) ext (* assume only the possibly weaker phi *)
 | forallR trace env ctx con D pot (A.Assume(x,phi,P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected forall, found: " ^ PP.pp_tp_compact env C)
  
and existsL trace env ctx con D (A.Exists(phi',A)) pot (A.Assume(x,phi,P)) zC ext (* z != x *) =
    if not (C.entails ctx (R.And(con,phi')) phi) (* con, phi' |= phi *)
    then ERROR ext ("assumption not entailed: " ^ C.pp_jfail (R.And(con,phi')) phi)
    else check_exp' trace env ctx (R.And(con,phi)) (update_tp (x,A) D) pot P zC ext (* assume the possibly weaker phi *)
  | existsL trace env ctx con D A pot (A.Assume(x,phi,P)) zC ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected exists, found: " ^ PP.pp_tp_compact env A)

and existsNatR trace env ctx con D pot (A.SendNat(x,e,P)) (z,A.ExistsNat(v,C)) ext (* z = x *) =
    check_exp' trace env ctx con D pot P (z, A.apply_tp (R.zip [v] [e]) C) ext
  | existsNatR trace env ctx con D pot (A.SendNat(x,e,P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected ?<id>._, found: " ^ PP.pp_tp_compact env C)

and forallNatL trace env ctx con D (A.ForallNat(v,A)) pot (A.SendNat(x,e,P)) zC ext (* z != x *) =
    check_exp' trace env ctx con (update_tp (x, A.apply_tp (R.zip [v] [e]) A) D) pot P zC ext
  | forallNatL trace env ctx con D A pot (A.SendNat(x,e,P)) zC ext (* z != x *) =
    ERROR ext ("type mismatch of " ^ x ^ ": expected !<id>._, found: " ^ PP.pp_tp_compact env A)

and forallNatR trace env ctx con D pot (A.RecvNat(x,v,P)) (z,A.ForallNat(v',C)) ext (* z = x *) =
    check_exp' trace env (v::ctx) con D pot P (z, A.apply_tp (R.zip [v'] [R.Var(v)]) C) ext
  | forallNatR trace env ctx con D pot (A.RecvNat(x,v,P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected !<id>._, found: " ^ PP.pp_tp_compact env C)

and existsNatL trace env ctx con D (A.ExistsNat(v',A)) pot (A.RecvNat(x,v,P)) zC ext (* z != x *) =
    check_exp' trace env (v::ctx) con (update_tp (x, A.apply_tp (R.zip [v'] [R.Var(v)]) A) D) pot P zC ext
  | existsNatL trace env ctx con D A pot (A.RecvNat(x,v,P)) zC ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected ?<id>._, found: " ^ PP.pp_tp_compact env A)

and work trace env ctx con D pot (A.Work(p,P)) zC ext =
    if not (C.entails ctx con (R.Ge(p,R.Int(0))))
    then ERROR ext ("potential not positive: " ^ C.pp_jfail con (R.Ge(p,R.Int(0))))
    else if not (C.entails ctx con (R.Ge(pot,p)))
    then ERROR ext ("insufficient potential: " ^ C.pp_jfail con (R.Ge (pot, p)))
    else check_exp' trace env ctx con D (R.minus(pot,p)) P zC ext

and paypotR trace env ctx con D pot (A.Pay(x,p',P)) (z,A.PayPot(p,C)) ext (* z = x *) =
    (* con |= p >= 0 since type is valid *)
    if not (C.entails ctx con (R.Ge(pot,p')))
    then ERROR ext ("insufficient potential: " ^ C.pp_jfail con (R.Ge(pot, p')))
    else if not (C.entails ctx con (R.Eq(p',p)))
    then ERROR ext ("potential mismatch: " ^ C.pp_jfail con (R.Eq(p',p)))
    else check_exp' trace env ctx con D (R.minus (pot,p)) P (z,C) ext
  | paypotR trace env ctx con D pot (A.Pay(x,p',P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected paypot, found: " ^ PP.pp_tp_compact env C)

and getpotL trace env ctx con D (A.GetPot(p,A)) pot (A.Pay(x,p',P)) zC ext (* z != x *) =
    (* con |= p >= 0 since type is valid *)
    if not (C.entails ctx con (R.Ge(pot,p)))
    then ERROR ext ("insufficient potential: " ^ C.pp_jfail con (R.Ge (pot, p)))
    else if not (C.entails ctx con (R.Eq(p,p')))
    then ERROR ext ("potential mismatch: " ^ C.pp_jfail con (R.Eq(p,p')))
    else check_exp' trace env ctx con (update_tp (x,A) D) (R.minus (pot,p)) P zC ext
  | getpotL trace env ctx con D A pot (A.Pay(x,p',P)) zC ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected getpot, found: " ^ PP.pp_tp_compact env A)

and getpotR trace env ctx con D pot (A.Get(x,p',P)) (z,A.GetPot(p,C)) ext (* z = x *) =
    (* con |= p >= 0 since type is valid *)
    if not (C.entails ctx con (R.Eq(p',p)))
    then ERROR ext ("potential mismatch: " ^ C.pp_jfail con (R.Eq(p',p)))
    else check_exp' trace env ctx con D (R.plus (pot,p)) P (z,C) ext
  | getpotR trace env ctx con D pot (A.Get(x,p',P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected paypot, found: " ^ PP.pp_tp_compact env C)

and paypotL trace env ctx con D (A.PayPot(p,A)) pot (A.Get(x,p',P)) zC ext (* z != x *) =
    (* con |= p >= 0 since type is valid *)
    if not (C.entails ctx con (R.Eq(p,p')))
    then ERROR ext ("potential mismatch: " ^ C.pp_jfail con (R.Eq(p,p')))
    else check_exp' trace env ctx con (update_tp (x,A) D) (R.plus (pot,p)) P zC ext
  | paypotL trace env ctx con D A pot (A.Get(x,p',P)) zC ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected getpot, found: " ^ PP.pp_tp_compact env A)

and delay trace env ctx con D pot (A.Delay(t,P)) (z,C) ext =
    if not(C.entails ctx con (R.Ge(t,R.Int(0))))
    then ERROR ext ("delay cannot be shown to be positive : " ^ C.pp_jfail con (R.Ge(t,R.Int(0))))
    else check_exp' trace env ctx con (decrement env ctx con D t ext) pot P (z,decrementR env ctx con C t ext) ext

and diaR trace env ctx con D pot (A.Now(x,P)) (z,A.Dia(C)) ext (* z = x *) =
    check_exp' trace env ctx con D pot P (z,C) ext
  | diaR trace env ctx con D pot (A.Now(x,P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected diamond, found: " ^ PP.pp_tp_compact env C)

and boxL trace env ctx con D (A.Box(A)) pot (A.Now(x,P)) zC ext (* z != x *) =
    check_exp' trace env ctx con (update_tp (x,A) D) pot P zC ext
  | boxL trace env ctx con D A pot (A.Now(x,P)) zC ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected box, found: " ^ PP.pp_tp_compact env A)

and boxR trace env ctx con D pot (A.When(x,P)) (z,A.Box(C)) ext (* z = x *) =
    let val () = eventually_box_ctx env D ext
    in
        check_exp' trace env ctx con D pot P (z,C) ext
    end
  | boxR trace env ctx con D pot (A.When(x,P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected box, found: " ^ PP.pp_tp_compact env C)

and diaL trace env ctx con D (A.Dia(A)) pot (A.When(x,P)) (z,C) ext (* z != x *) =
    let val () = if eventually_dia env C then ()
                 else ERROR ext ("type " ^ PP.pp_tp_compact env C ^ " is not patient (ie, not (n)<>A")
    in
        check_exp' trace env ctx con (update_tp (x,A) D) pot P (z,C) ext
    end
  | diaL trace env ctx con D A pot (A.When(x,P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected diamond, found: " ^ PP.pp_tp_compact env A)

  (* judgmental constructs: id, cut, spawn, call *)
and check_exp trace env ctx con D pot (A.Id(x,y)) zC ext =
    fwd trace env ctx con D pot (A.Id(x,y)) zC ext
  | check_exp trace env ctx con D pot (A.Spawn(P,Q)) zC ext =
    spawn trace env ctx con D pot (A.Spawn(P,Q)) zC ext
  | check_exp trace env ctx con D pot (A.ExpName(x,f,es,xs)) (z,C) ext =
    expname trace env ctx con D pot (A.ExpName(x,f,es,xs)) (z,C) ext
    
  (* structural types +{...}, &{...}, 1 *)
  | check_exp trace env ctx con D pot (A.Lab(x,k,P)) (z,C) ext =
    if x = z
    then plusR trace env ctx con D pot (A.Lab(x,k,P)) (z,expand env C) ext
    else withL trace env ctx con D (lookup_context env x D ext) pot (A.Lab(x,k,P)) (z,C) ext
  | check_exp trace env ctx con D pot (A.Case(x,branches)) (z,C) ext =
    if x = z
    then withR trace env ctx con D pot (A.Case(x,branches)) (z,expand env C) ext
    else plusL trace env ctx con D (lookup_context env x D ext) pot (A.Case(x,branches)) (z,C) ext

  | check_exp trace env ctx con D pot (A.Send(x,w,P)) (z,C) ext =
    if x = z
    then tensorR trace env ctx con D pot (A.Send(x,w,P)) (z,expand env C) ext
    else lolliL trace env ctx con D (lookup_context env x D ext) pot (A.Send(x,w,P)) (z,C) ext
  | check_exp trace env ctx con D pot (A.Recv(x,y,Q)) (z,C) ext =
    if x = z
    then lolliR trace env ctx con D pot (A.Recv(x,y,Q)) (z,expand env C) ext
    else tensorL trace env ctx con D (lookup_context env x D ext) pot (A.Recv(x,y,Q)) (z,C) ext

  | check_exp trace env ctx con D pot (A.Close(x)) (z,C) ext =
    if x = z
    then oneR trace env ctx con D pot (A.Close(x)) (z,expand env C) ext
    else ERROR ext ("name mismatch on right: " ^ x ^ " <> " ^ z)
  | check_exp trace env ctx con D pot (A.Wait(x,Q)) (z,C) ext =
    if x = z
    then ERROR ext ("name mismatch on left: " ^ x ^ " = " ^ z)
    else oneL trace env ctx con D (lookup_context env x D ext) pot (A.Wait(x,Q)) (z,C) ext

  (* quantified types ?{phi}.A, !{phi}.A *)
  | check_exp trace env ctx con D pot (A.Assert(x,phi,P)) (z,C) ext =
    if x = z
    then existsR trace env ctx con D pot (A.Assert(x,phi,P)) (z,expand env C) ext
    else forallL trace env ctx con D (lookup_context env x D ext) pot (A.Assert(x,phi,P)) (z,C) ext
  | check_exp trace env ctx con D pot (A.Assume(x,phi,Q)) (z,C) ext =
    if x = z
    then forallR trace env ctx con D pot (A.Assume(x,phi,Q)) (z,expand env C) ext
    else existsL trace env ctx con D (lookup_context env x D ext) pot (A.Assume(x,phi,Q)) (z,C) ext    

  (* quantified types ?v.A, !v.A *)
  | check_exp trace env ctx con D pot (A.SendNat(x,e,P)) (z,C) ext =
    if x = z
    then existsNatR trace env ctx con D pot (A.SendNat(x,e,P)) (z,expand env C) ext
    else forallNatL trace env ctx con D (lookup_context env x D ext) pot (A.SendNat(x,e,P)) (z,C) ext
  | check_exp trace env ctx con D pot (A.RecvNat(x,v,P)) (z,C) ext =
    if x = z
    then forallNatR trace env ctx con D pot (A.RecvNat(x,v,P)) (z,expand env C) ext
    else existsNatL trace env ctx con D (lookup_context env x D ext) pot (A.RecvNat(x,v,P)) (z,C) ext

  (* impossibility *)
  | check_exp trace env ctx con D pot (A.Imposs) zC ext =
    if not (C.contradictory ctx con R.True) (* TODO: fix interface *)
    then ERROR ext ("constraints not contradictory: " ^ C.pp_jsat con R.True)
    else ()

  (* ergometric types |>, <| *)
  | check_exp trace env ctx con D pot (A.Work(p,P)) zC ext =
    work trace env ctx con D pot (A.Work(p,P)) zC ext
  | check_exp trace env ctx con D pot (A.Pay(x,p',P)) (z,C) ext =
    if x = z
    then paypotR trace env ctx con D pot (A.Pay(x,p',P)) (z,expand env C) ext
    else getpotL trace env ctx con D (lookup_context env x D ext) pot (A.Pay(x,p',P)) (z,C) ext
  | check_exp trace env ctx con D pot (A.Get(x,p',P)) (z,C) ext =
    if x = z
    then getpotR trace env ctx con D pot (A.Get(x,p',P)) (z,expand env C) ext
    else paypotL trace env ctx con D (lookup_context env x D ext) pot (A.Get(x,p',P)) (z,C) ext

  (* temporal types (), [], <> *)
  | check_exp trace env ctx con D pot (A.Delay(t,P)) (z,C) ext =
    delay trace env ctx con D pot (A.Delay(t,P)) (z,C) ext
  
  | check_exp trace env ctx con D pot (A.Now(x,P)) (z,C) ext =
    if x = z
    then diaR trace env ctx con D pot (A.Now(x,P)) (z,expand env C) ext
    else boxL trace env ctx con D (lookup_context env x D ext) pot (A.Now(x,P)) (z,C) ext
  | check_exp trace env ctx con D pot (A.When(x,P)) (z,C) ext =
    if x = z
    then boxR trace env ctx con D pot (A.When(x,P)) (z,expand env C) ext
    else diaL trace env ctx con D (lookup_context env x D ext) pot (A.When(x,P)) (z,C) ext


  (* marked expressions *)
  | check_exp trace env ctx con D pot (A.Marked(marked_P)) zC ext =
    check_exp trace env ctx con D pot (Mark.data marked_P) zC (Mark.ext marked_P)

(* external interface *)
val check_exp = check_exp'      (* entry point for tracing *)
val eq_tp = fn env => fn ctx => fn con => fn A => fn B =>
            eq_tp' env ctx con nil A B

end (* structure TypeCheck *)
