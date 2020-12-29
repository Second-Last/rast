(* Type Equality *)
(* Authors: Ankush Das <ankushd@cs.cmu.edu>
 *          Frank Pfenning <fp@cs.cmu.edu>
 *)

(*
 * Type equality is defined coinductively on the equirecursive
 * interpretation of types. This goes back to the work by
 * Gay and Hole (2005), but has been expanded to account for
 * index objects.  The algorithm is described in
 * Ankush Das and Frank Pfenning, Session Types with Arithmetic
 * Refinements and Their Application to Work Analysis, January 2020,
 * https://arxiv.org/abs/2001.04439
 *
 * Flags.equality determines the details of the algorithm, where
 * the default setting (Flags.SubsumeRefl) is the strongest; the others
 * exist for comparison purposes.
 *)

signature TYPE_EQUALITY =
sig

    val update_variances : Ast.env -> Ast.env
    val eq_tp : Ast.env -> Ast.tp_ctx -> Arith.ctx -> Arith.prop -> Ast.tp -> Ast.variance -> Ast.tp -> bool
    val pp_reason : unit -> string  (* a message regarding the failure of type equality *)

end  (* signature TYPE_EQUALITY *)

structure TypeEquality :> TYPE_EQUALITY =
struct

structure R = Arith
structure A = Ast
structure PP = PPrint
structure TU = TypeUtil
structure C = Constraints

(************************)
(* Analysis of Variance *)
(************************)

(* tpdef env a = (a, alphas, B) if a[alphas]{...} = B in env *)
fun tp_def env a =
    case A.lookup_tp env a
     of SOME(alphas, Ws_opt, vs, con, B) => (a, alphas, B)
        (* NONE should be impossible *)

(* tpctx only for locally quantified variables; currently unused *)
fun variance env tpctx seen alpha (A.Plus(choices)) = variance_choices env tpctx seen alpha choices
  | variance env tpctx seen alpha (A.With(choices)) = variance_choices env tpctx seen alpha choices
  | variance env tpctx seen alpha (A.Tensor(A,B)) =
    A.lub (variance env tpctx seen alpha A) (variance env tpctx seen alpha B)
  | variance env tpctx seen alpha (A.Lolli(A,B)) =
    A.lub (A.neg (variance env tpctx seen alpha A)) (variance env tpctx seen alpha B)
  | variance env tpctx seen alpha (A.One) = A.NonVar
  | variance env tpctx seen alpha (A.Exists(phi,A)) = variance env tpctx seen alpha A
  | variance env tpctx seen alpha (A.Forall(phi,A)) = variance env tpctx seen alpha A
  | variance env tpctx seen alpha (A.ExistsNat(v,A)) = variance env tpctx seen alpha A
  | variance env tpctx seen alpha (A.ForallNat(v,A)) = variance env tpctx seen alpha A
  | variance env tpctx seen alpha (A.ExistsTp(alpha',A)) =
    if alpha = alpha' then A.NonVar
    else variance env (alpha'::tpctx) seen alpha A
  | variance env tpctx seen alpha (A.ForallTp(alpha',A)) =
    if alpha = alpha' then A.NonVar
    else variance env tpctx seen alpha A
  | variance env tpctx seen alpha (A.PayPot(p,A)) = variance env tpctx seen alpha A
  | variance env tpctx seen alpha (A.GetPot(p,A)) = variance env tpctx seen alpha A
  | variance env tpctx seen alpha (A.Next(t,A)) = variance env tpctx seen alpha A
  | variance env tpctx seen alpha (A.Dia(A)) = variance env tpctx seen alpha A
  | variance env tpctx seen alpha (A.Box(A)) = variance env tpctx seen alpha A
  | variance env tpctx seen alpha (A.TpVar(beta)) =
    if alpha = beta then A.CoVar else A.NonVar
  | variance env tpctx seen alpha (A as A.TpName(b,As,es)) =
    variance_list env tpctx seen alpha (tp_def env b) As
and variance_choices env tpctx seen alpha nil = A.NonVar
  | variance_choices env tpctx seen alpha ((l,Al)::choices) =
    A.lub (variance env tpctx seen alpha Al) (variance_choices env tpctx seen alpha choices)
and variance_list env tpctx seen alpha (b, nil, B) nil = A.NonVar
  | variance_list env tpctx seen alpha (b, beta::betas, B) (A::As) =
    let val V_betaB = variance_name env tpctx seen (b, beta, B)
        val V_alphaA = variance env tpctx seen alpha A
    in A.lub (A.cmp V_alphaA V_betaB) (variance_list env tpctx seen alpha (b, betas, B) As) end
and variance_name env tpctx seen (b, beta, B) =
    case List.find (fn (b',beta',W,B') => (b,beta) = (b',beta')) seen (* B = B' by invariant *)
     of SOME(_,_,W,_) => W
        (* NONE is impossible *)

(* round-robin iteration to find least fixed point *)
(* keep items in order just for sake of cleanliness *)
fun iter changed env (old as ((a, alpha, W, A)::old')) new =
    let val W' = variance env nil (List.revAppend (new, old)) alpha A
    in if W' = W (* no change *)
       then iter changed env old' ((a,alpha,W,A)::new)
       else iter true env old' ((a,alpha,W',A)::new)
    end
  | iter true env nil new = iter false env (List.rev new) nil
  | iter false env nil new = new (* found least fixed point *)

(* init env = seen_init, start of least fixed point iteration *)
(* can be called before or after internal names are created *)
fun init (A.TpDef(a,alphas,NONE,vs,phi,A,ext)::env') =
    List.map (fn alpha => (a, alpha, A.NonVar, A)) alphas
    @ init env'
  | init (A.TpDef(a,alphas,SOME _,vs,phi,A,ext)::env') =
    raise Match
  | init (_ :: env') = init env'
  | init nil = nil

fun extract_variances (a, nil) seen = nil
  | extract_variances (a, alpha::alphas) seen =
    case List.find (fn (b, beta, W, B) => (a,alpha) = (b,beta)) seen
     of SOME(_, _, W, _) => W::extract_variances (a, alphas) seen
        (* NONE should be impossible at fixed point *)

fun update_env (A.TpDef(a,alphas,NONE,vs,phi,A,ext)::env') seen =
    let val Vs = extract_variances (a, alphas) seen
        val decl' = A.TpDef(a,alphas,SOME(Vs),vs,phi,A,ext)
    in decl'::update_env env' seen end
  | update_env (A.TpDef(a,alphas,SOME _,vs,phi,A,ext)::env') seen =
    raise Match
  | update_env (decl::env') seen = decl::update_env env' seen
  | update_env nil seen = nil

fun update_variances env =
    let val seen_init = init env
        val seen = iter false env seen_init nil
    in update_env env seen end

fun variances env a =
    case A.lookup_tp env a
     of SOME(alphas, SOME(Ws), vs, phi, A) => Ws
     (* NONE should be impossible *)

(*****************)
(* Type equality *)
(*****************)

(* Reflexivity *)

(* implies W V = true if variance W in memo pad implies variance V in goal *)
(* W and V in CoVar, ContraVar, BiVar *)
fun implies A.BiVar _ = true  (* A == B implies A <= B and A >= B *)
  | implies A.CoVar A.CoVar = true (* A <= B implies A <= B *)
  | implies A.ContraVar A.ContraVar = true  (* A >= B implies A >= B *)
  | implies _ _ = false

(* nested W rel = rel' if a[A]... rel a[B]... where the
 * variance of this argument of a is W <> NonVar
 * requires checking A rel' A 
 * Requires W <> NonVar, rel <> NonVar
 *)
fun nested A.BiVar rel = A.BiVar
  | nested A.CoVar rel = rel
  | nested A.ContraVar rel = A.neg rel

(* entailment, based on relation *)
(* con |- ?{x > 6}. A <= ?{x > 5}. B if con /\ x > 6 |- A <= B *)
(* con |- !{x > 5}. A <= !{x > 6}. B if con /\ x > 6 |- A <= B *)
fun entail ctx con phi (A.BiVar) phi' = C.equiv ctx con phi phi'
  | entail ctx con phi (A.CoVar) phi' = C.entails ctx (R.And(con,phi)) phi'
  | entail ctx con phi (A.ContraVar) phi' = C.entails ctx (R.And(con,phi')) phi

(* pick the assumption that makes both types well-formed *)
(* we assume entail ctx con phi rel phi' == true *)
fun stronger ctx con phi (A.BiVar) phi' = phi (* either okay here *)
  | stronger ctx con phi (A.CoVar) phi' = phi
  | stronger ctx con phi (A.ContraVar) phi' = phi'

(* eq_id ctx con e e' iff ctx ; con |= e = e' *)
fun eq_id ctx con e e' = C.entails ctx con (R.Eq(e,e'))

(* eq_idx ctx con es es', assumes |es| = |es'| *)
fun eq_idx ctx con nil nil = true
  | eq_idx ctx con (e::es) (e'::es') =
      eq_id ctx con e e' andalso eq_idx ctx con es es'

(* Structural equality *)

(* mem_env env a a' => [TPCTX1,CTX1,CON1,TpName(a,As1,es1),REL,TpName(a',As1',es1'),...] *)
fun mem_env (A.TpEq(TPCTX,CTX,CON,A as A.TpName(B,AS,ES),REL,A' as A.TpName(B',AS',ES'),_)::env) a rel a' =
    if B = a andalso B' = a' andalso implies REL rel
    then (TPCTX,CTX,CON,(A,REL,A'))::mem_env env a rel a'
    else if B = a' andalso B' = a andalso implies (A.neg REL) rel
    then (TPCTX,CTX,CON,(A',A.neg REL,A))::mem_env env a rel a'   (* flip! *)
    else mem_env env a rel a'
  | mem_env (_::env) a rel a' = mem_env env a rel a'
  | mem_env nil a rel a' = nil

(* mem_env env seen a a' => [(TPCTX1,CTX1,CON1,TpName(a,As1,es1),rel,TpName(a',As1',es1')),...] *)
fun mem_seen env ((E as (TPCTX,CTX,CON,(A as A.TpName(B,AS,ES), REL, A' as A.TpName(B',AS',ES'))))::seen) a rel a' =
    if B = a andalso B' = a' andalso implies REL rel
    then (TPCTX,CTX,CON,(A,REL,A'))::mem_seen env seen a rel a'
    else if B = a' andalso B' = a andalso implies (A.neg REL) rel
    then (TPCTX,CTX,CON,(A',A.neg REL,A))::mem_seen env seen a rel a' (* flip! *)
    else mem_seen env seen a rel a'
  | mem_seen env (_::seen) a rel a' = mem_seen env seen a rel a'
  | mem_seen env nil a rel a' = nil

(* fresh internal name generation, in the arithmetic layer *)
(*
fun fresh v = "%" ^ v

fun gen_fresh nil = (nil, nil)
  | gen_fresh (v::vs) =
    let val fv = fresh v
        val (fvs, sigma) = gen_fresh vs
    in
      (fv::fvs,(v, R.Var(fv))::sigma)
    end
*)
fun next v = v ^ "^"

fun fresh used v =
    if List.exists (fn u => v = u) used
    then fresh used (next v)
    else v

fun gen_fresh used nil = (nil, nil)
  | gen_fresh used (v::vs) =
    let val fv = fresh used v
        val (fvs, rho) = gen_fresh used vs
    in (fv::fvs, (v,R.Var(fv))::rho) end

fun gen_eq nil nil = R.True
  | gen_eq (E::ES) (e::es) = R.And(R.Eq(E,e), gen_eq ES es)

(* gen_prop_eq FCON FES es FES' es' ==> FCON /\ FES = es /\ FES' = es' *)
fun gen_eqs_prop FCON FES es FES' es' =
    let val eqs = gen_eq FES es
        val eqs' = gen_eq FES' es'
        val eqs_prop = R.And(FCON, R.And(eqs, eqs'))
    in eqs_prop end

fun gen_exists_prop FCTX eqs_prop =
    let
        val nnf_prop = R.nnf eqs_prop
        val exists_prop = R.elim_vars FCTX nnf_prop (* exists_prop is in NNF, but not using it *)
    in
        exists_prop
    end

(* 
 * Temporal types create a complication, since ()()A == ({2})A
 * and ({0})A == A, so we need to aggregate Next operators
 *)

(* aggregate_nexts' env ctx con s A = A'
 * where all initial next-time operators in A are added to S.
 * If the result is 0, the next-time operators is stripped entirely.
 *)
fun aggregate_nexts' env ctx con s (A.Next(t,A')) =
    aggregate_nexts' env ctx con (R.plus(s,t)) A'
  | aggregate_nexts' env ctx con s (A as A.TpName(a,As,es)) =
    aggregate_nexts' env ctx con s (TU.expd env A)
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

(* match_tp env seen tpctx exvars locals ctx con theta A rel A' = theta'
 * (tpctx, exvars, locals) ; ctx ; con |- A type
 * (tpctx, _     , locals) ; ctx ; con |- A' type [no exvars in A']
 * theta' extends theta
 * tpctx |- theta' : exvars  [theta' may not depend on locals]
 * (tpctx, locals) ; ctx ; con |- [theta']A rel A'
 * for 'rel' one of <= (A.CoVar), >= (A.ContraVar), == (A.BiVar)
 *)
fun not_free_in betas A =
    let val alphas = A.free_tpvars nil A
    in List.all (fn beta => not (List.exists (fn alpha => alpha = beta) alphas)) betas end

(* main entry point *)
fun match_tp' env seen tpctx exvars locals ctx con theta A rel A' =
    match_tp env seen tpctx exvars locals ctx con theta
             (aggregate_nexts env ctx con A)
             rel (aggregate_nexts env ctx con A')

and match_tp env seen tpctx exvars locals ctx con theta (A as A.Plus(choice)) rel (A' as A.Plus(choice')) =
    match_ichoice env seen tpctx exvars locals ctx con theta A rel A'
  | match_tp env seen tpctx exvars locals ctx con theta (A as A.With(choice)) rel (A' as A.With(choice')) =
    match_echoice env seen tpctx exvars locals ctx con theta A rel A'
  
  | match_tp env seen tpctx exvars locals ctx con theta (A.Tensor(A,B)) rel (A.Tensor(A',B')) =
    (case match_tp' env seen tpctx exvars locals ctx con theta A rel A'
      of NONE => NONE
       | SOME(theta1) => match_tp' env seen tpctx exvars locals ctx con theta1 B rel B')
  | match_tp env seen tpctx exvars locals ctx con theta (A.Lolli(A,B)) rel (A.Lolli(A',B')) =
    (case match_tp' env seen tpctx exvars locals ctx con theta A (A.neg rel) A'
      of NONE => NONE
       | SOME(theta1) => match_tp' env seen tpctx exvars locals ctx con theta1 B rel B')

  | match_tp env seen tpctx exvars locals ctx con theta (A.One) rel (A.One) = SOME(theta)

  | match_tp env seen tpctx exvars locals ctx con theta (A.Exists(phi,A)) rel (A.Exists(phi',A')) =
    if entail ctx con phi rel phi'
    then match_tp' env seen tpctx exvars locals ctx (R.And(con,stronger ctx con phi rel phi')) theta A rel A'
    else NONE
  | match_tp env seen tpctx exvars locals ctx con theta (A.Forall(phi,A)) rel (A.Forall(phi',A')) =
    if entail ctx con phi (A.neg rel) phi'
    then match_tp' env seen tpctx exvars locals ctx (R.And(con,stronger ctx con phi (A.neg rel) phi')) theta A rel A'
    else NONE

  | match_tp env seen tpctx exvars locals ctx con theta (A.ExistsNat(v,A)) rel (A.ExistsNat(v',A')) =
    match_tp_bind env seen tpctx exvars locals ctx con theta (v,A) rel (v',A')
  | match_tp env seen tpctx exvars locals ctx con theta (A.ForallNat(v,A)) rel (A.ForallNat(v',A')) =
    match_tp_bind env seen tpctx exvars locals ctx con theta (v,A) rel (v',A')

  | match_tp env seen tpctx exvars locals ctx con theta (A.ExistsTp(alpha,A)) rel (A.ExistsTp(alpha',A')) =
    match_tp_tpbind env seen tpctx exvars locals ctx con theta (alpha,A) rel (alpha',A')
  | match_tp env seen tpctx exvars locals ctx con theta (A.ForallTp(alpha,A)) rel (A.ForallTp(alpha',A')) =
    match_tp_tpbind env seen tpctx exvars locals ctx con theta (alpha,A) rel (alpha',A')

  | match_tp env seen tpctx exvars locals ctx con theta (A.PayPot(p,A)) rel (A.PayPot(p',A')) =
    if eq_id ctx con p p'
    then match_tp' env seen tpctx exvars locals ctx con theta A rel A'
    else NONE
  | match_tp env seen tpctx exvars locals ctx con theta (A.GetPot(p,A)) rel (A.GetPot(p',A')) = 
    if eq_id ctx con p p'
    then match_tp' env seen tpctx exvars locals ctx con theta A rel A'
    else NONE

  | match_tp env seen tpctx exvars locals ctx con theta (A.Next(t,A)) rel (A.Next(t',A')) =
    if eq_id ctx con t t'
    then match_tp' env seen tpctx exvars locals ctx con theta A rel A'
    else NONE
  | match_tp env seen tpctx exvars locals ctx con theta (A.Box(A)) rel (A.Box(A')) =
    match_tp' env seen tpctx exvars locals ctx con theta A rel A'
  | match_tp env seen tpctx exvars locals ctx con theta (A.Dia(A)) rel (A.Dia(A')) =
    match_tp' env seen tpctx exvars locals ctx con theta A rel A'
    
  | match_tp env seen tpctx exvars locals ctx con theta (A.TpVar(alpha)) rel A' =
    if List.exists (fn beta => beta = alpha) exvars
    then (* alpha is subject to instantiation! *)
        case List.find (fn (beta,B) => beta = alpha) theta
         of NONE => if not_free_in locals A'  (* check that A' does not depend on local type variables *)
                    then SOME((alpha,A')::theta)
                    else NONE
          | SOME(beta,B) => (* B = A' required, no further instantiation for matching *)
            (* B should not depend on locals, but A' might *)
            (case match_tp env seen tpctx [] locals ctx con [] B rel A'
              of NONE => NONE
               | SOME [] => SOME(theta)
            (* SOME(_::_) should be impossible *)
            )
    else (* alpha is not subject to instantiation! *)
        (* this means it should be in locals or tpctx and A = A' required *)
        if List.exists (fn beta => beta = alpha) (tpctx @ locals)
        then (case A'
               of A.TpVar(alpha') => if alpha = alpha' then SOME(theta) else NONE
                | _ => NONE)
        else raise Match (* this should be impossible *)

  | match_tp env seen tpctx exvars locals ctx con theta (A as A.TpName(a,As,es)) rel (A' as A.TpName(a',As',es')) =
    (* Q: should this be stronger, as in eq_tp but without type unfolding? *)
    if a = a' andalso eq_idx ctx con es es'
    then match_tp_list env seen tpctx exvars locals ctx con theta (variances env a) As rel As'
    else if instance_of env seen (tpctx @ locals) ctx con
                        (mem_seen env seen a rel a' @ mem_env env a rel a')
                        A rel A'
    then SOME(theta)
    else NONE

(* shouldn't need the next two cases by the internal naming invariant? *)
  | match_tp env seen tpctx exvars locals ctx con theta (A as A.TpName(a,As,es)) rel A' =
    match_tp' env seen tpctx exvars locals ctx con theta (TU.expd env A) rel A'
  | match_tp env seen tpctx exvars locals ctx con theta A rel (A' as A.TpName(a',As',es')) =
    match_tp' env seen tpctx exvars locals ctx con theta A rel (TU.expd env A')

  | match_tp env seen tpctx exvars locals ctx con theta A rel A' = NONE

(* match_tp_list env seen tpctx exvars locals ctx con theta (a, alphas, B) As As'
 * requires |alphas| = |As| = |As'| and a[alphas]{...} = B
 *)
and match_tp_list env seen tpctx exvars locals ctx con theta nil nil rel nil = SOME(theta)
  | match_tp_list env seen tpctx exvars locals ctx con theta (W::Ws) (A::As) rel (A'::As') =
    if W = A.NonVar
    then match_tp_list env seen tpctx exvars locals ctx con theta Ws As rel As'
    else case match_tp' env seen tpctx exvars locals ctx con theta A (nested W rel) A'
          of NONE => NONE
           | SOME(theta1) => match_tp_list env seen tpctx exvars locals ctx con theta1 Ws As rel As'

and match_tp_bind env seen tpctx exvars locals ctx con theta (v,A) rel (v',A') =
    let val sigma = R.zip ctx (R.create_idx ctx) (* necessary? *)
        val w = R.fresh_var sigma v
        val wA = A.apply_tp ((v, R.Var(w))::sigma) A
        val wA' = A.apply_tp ((v', R.Var(w))::sigma) A'
    in match_tp' env seen tpctx exvars locals (w::ctx) con theta wA rel wA' end

and match_tp_tpbind env seen tpctx exvars locals ctx con theta (alpha,A) rel (alpha',A') =
    let val allVars = tpctx @ exvars @ locals
        val dummy = ListPair.zipEq (allVars, List.map A.TpVar allVars)
        val beta = A.fresh_tpvar dummy alpha
        val B = A.subst_tp [(alpha, A.TpVar(beta))] A
        val B' = A.subst_tp [(alpha', A.TpVar(beta))] A'
    in match_tp' env seen tpctx exvars (beta::locals) ctx con theta B rel B' end

and match_ichoice env seen tpctx exvars locals ctx con theta (A.Plus((l,A)::choices)) rel (A.Plus(choices')) =
    (case A.lookup_choice_rest choices' l
      of NONE => if rel = A.ContraVar
                 then match_ichoice env seen tpctx exvars locals ctx con theta (A.Plus(choices)) rel (A.Plus(choices'))
                 else NONE
       | SOME(A',choices'') =>
         case match_tp' env seen tpctx exvars locals ctx con theta A rel A'
          of NONE => NONE
           | SOME(theta1) => match_ichoice env seen tpctx exvars locals ctx con theta1 (A.Plus(choices)) rel (A.Plus(choices'')))
  | match_ichoice env seen tpctx exvars locals ctx con theta (A.Plus(nil)) rel (A.Plus((l',A')::choices')) =
    if rel = A.CoVar then SOME(theta) else NONE
  | match_ichoice env seen tpctx exvars locals ctx con theta (A.Plus(nil)) rel (A.Plus(nil)) = SOME(theta)

and match_echoice env seen tpctx exvars locals ctx con theta (A.With((l,A)::choices)) rel (A.With(choices')) =
    (case A.lookup_choice_rest choices' l
      of NONE => if rel = A.CoVar
                 then match_ichoice env seen tpctx exvars locals ctx con theta (A.With(choices)) rel (A.With(choices'))
                 else NONE
       | SOME(A',choices'') =>
         case match_tp' env seen tpctx exvars locals ctx con theta A rel A'
          of NONE => NONE
           | SOME(theta1) => match_echoice env seen tpctx exvars locals ctx con theta1 (A.With(choices)) rel (A.With(choices'')))
  | match_echoice env seen tpctx exvars locals ctx con theta (A.With(nil)) rel (A.With((l',A')::choices')) =
    if rel = A.ContraVar then SOME(theta) else NONE
  | match_echoice env seen tpctx exvars locals ctx con theta (A.With(nil)) rel (A.With(nil)) = SOME(theta)


(* to aid in termination, instance_of does not call on general type equality! *)
and instance_of env seen tpctx ctx con nil A rel A' = false (* do not recurse *)
  | instance_of env seen tpctx ctx con 
                     ((TPCTX,CTX,CON, (W as A.TpName(_,AS,ES), REL, W' as A.TpName(_,AS',ES')))::eqs)
                     (A as A.TpName(a,As,es)) rel (A' as A.TpName(a',As',es')) = (* REL = rel *)
    (* check for substitution instance on types; entailment on constraints *)
    (* first, check that there is an entailment of arithmetic constraints *)
    (* then verify that *all* solutions to the constraint entailment makes the type arguments equal *)
    let val (FCTX,rho) = gen_fresh ctx CTX (* rename away from ctx *)
        val FCON = R.apply_prop rho CON
        val FES = R.apply_list rho ES
        val FES' = R.apply_list rho ES'
        val eqs_prop = gen_eqs_prop FCON FES es FES' es'  (* FCON /\ FES = es /\ FES' = es' *)
        val exists_prop = gen_exists_prop FCTX eqs_prop   (* exists FCTX. FCON /\ FES = es /\ FES' = es' *)
        val idx_entailed = C.entails ctx con exists_prop  (* ctx ; con |= exists FCTX. FCON /\ FES = es /\ FES' = es' *)
                                                          (* could be trusting non-linear *)
        val joint_ctx = ctx @ FCTX
        val joint_con = R.And(con,eqs_prop)               (* but not existentially quantified *)
    in
        (idx_entailed
         (* exvars = TPCTX, locals = [], theta = [] *)
         andalso (case match_tp_list env seen tpctx TPCTX [] joint_ctx joint_con [] (variances env a) AS (A.neg rel) As
                   of NONE => instance_of env seen tpctx ctx con eqs A rel A'
                    | SOME(theta1) => case match_tp_list env seen tpctx TPCTX [] joint_ctx joint_con theta1 (variances env a') AS' rel As'
                                       of NONE => instance_of env seen tpctx ctx con eqs A rel A'
                                        | SOME(theta2) => true))
        orelse instance_of env seen tpctx ctx con eqs A rel A'
    end

(*
 * Paths through types in order to support better
 * error messages on mismatched types.  This is currently
 * not used, although the information is maintained
 * by the algorithm
 *)
datatype path = Root
              | Plus of A.label * path
              | With of A.label * path
              | Tensor1 of path
              | Tensor2 of path
              | Lolli1 of path
              | Lolli2 of path
              | Exists of Arith.prop * path
              | Forall of Arith.prop * path
              | ExistsNat of Arith.varname * path
              | ForallNat of Arith.varname * path
              | ExistsTp of A.tpvarname * path
              | ForallTp of A.tpvarname * path
              | PayPot of A.pot * path
              | GetPot of A.pot * path
              | Next of A.time * path
              | Dia of path
              | Box of path

datatype reason = Mismatch of path * A.tp * A.variance * A.tp
                | BoundExceeded of path * A.tp * A.variance * A.tp

val latest_reason : reason option ref = ref NONE

fun pp_r (SOME(Mismatch _)) = "since the types clash"
  | pp_r (SOME(BoundExceeded _)) = "since the type expansion bound is exceeded"
  | pp_r (NONE) = "for no discernible reason"

fun pp_reason () = pp_r (!latest_reason)

(* eq_tp' env con seen A A' = true if (A == A') *)

(* main entry point *)
fun eq_tp' path env tpctx ctx con seen A rel A' =
    ( () (* TextIO.print (A.Print.pp_tp A ^ " =?= " ^ A.Print.pp_tp A' ^ "\n") *)
    ; eq_tp path env tpctx ctx con seen
            (aggregate_nexts env ctx con A) rel
            (aggregate_nexts env ctx con A')
    )

and eq_tp path env tpctx ctx con seen (A as A.Plus(choice)) rel (A' as A.Plus(choice')) =
    eq_ichoice path env tpctx ctx con seen A rel A'
  | eq_tp path env tpctx ctx con seen (A as A.With(choice)) rel (A' as A.With(choice')) =
    eq_echoice path env tpctx ctx con seen A rel A'
  
  | eq_tp path env tpctx ctx con seen (A.Tensor(A,B)) rel (A.Tensor(A',B')) =
    eq_tp' (Tensor1(path)) env tpctx ctx con seen A rel A'
    andalso eq_tp' (Tensor2(path)) env tpctx ctx con seen B rel B'
  | eq_tp path env tpctx ctx con seen (A.Lolli(A,B)) rel (A.Lolli(A',B')) =
    eq_tp' (Lolli1(path)) env tpctx ctx con seen A (A.neg rel) A'
    andalso eq_tp' (Lolli2(path)) env tpctx ctx con seen B rel B'

  | eq_tp path env tpctx ctx con seen (A.One) rel (A.One) = true

  | eq_tp path env tpctx ctx con seen (A.Exists(phi,A)) rel (A.Exists(phi',A')) =
    entail ctx con phi rel phi'
    andalso eq_tp' (Exists(phi,path)) env tpctx ctx (R.And(con,stronger ctx con phi rel phi')) seen A rel A'
    (* for now, require equality even in the presence of contradictory constraints *)
    (* orelse C.contradictory ctx con phi *)
  | eq_tp path env tpctx ctx con seen (A.Forall(phi,A)) rel (A.Forall(phi',A')) =
    entail ctx con phi (A.neg rel) phi'
    andalso eq_tp' (Forall(phi,path)) env tpctx ctx (R.And(con,stronger ctx con phi rel phi')) seen A rel A'
    (* for now, require equality even in the presence of contradictory constraints *)
    (* orelse C.contradictory ctx con phi *)

  | eq_tp path env tpctx ctx con seen (A.ExistsNat(v,A)) rel (A.ExistsNat(v',A')) =
    eq_tp_bind (ExistsNat(v,path)) env tpctx ctx con seen (v,A) rel (v',A')
  | eq_tp path env tpctx ctx con seen (A.ForallNat(v,A)) rel (A.ForallNat(v',A')) =
    eq_tp_bind (ForallNat(v,path)) env tpctx ctx con seen (v,A) rel (v',A')

  | eq_tp path env tpctx ctx con seen (A.ExistsTp(alpha,A)) rel (A.ExistsTp(alpha',A')) =
    eq_tp_tpbind (ExistsTp(alpha,path)) env tpctx ctx con seen (alpha,A) rel (alpha',A')
  | eq_tp path env tpctx ctx con seen (A.ForallTp(alpha,A)) rel (A.ForallTp(alpha',A')) =
    eq_tp_tpbind (ForallTp(alpha,path)) env tpctx ctx con seen (alpha,A) rel (alpha',A')

  | eq_tp path env tpctx ctx con seen (A.PayPot(p,A)) rel (A.PayPot(p',A')) =
    eq_id ctx con p p' andalso eq_tp' (PayPot(p,path)) env tpctx ctx con seen A rel A'
  | eq_tp path env tpctx ctx con seen (A.GetPot(p,A)) rel (A.GetPot(p',A')) = 
    eq_id ctx con p p' andalso eq_tp' (GetPot(p,path)) env tpctx ctx con seen A rel A'

  | eq_tp path env tpctx ctx con seen (A.Next(t,A)) rel (A.Next(t',A')) =
    eq_id ctx con t t' andalso eq_tp' (Next(t,path)) env tpctx ctx con seen A rel A'
  | eq_tp path env tpctx ctx con seen (A.Box(A)) rel (A.Box(A')) =
    eq_tp' (Box(path)) env tpctx ctx con seen A rel A'
  | eq_tp path env tpctx ctx con seen (A.Dia(A)) rel (A.Dia(A')) =
    eq_tp' (Dia(path)) env tpctx ctx con seen A rel A'
  | eq_tp path env tpctx ctx con seen (A.TpVar(alpha)) rel (A.TpVar(alpha')) =
    alpha = alpha'

  (* case prior to polymorphism untouched *)
  (*
  | eq_tp path env tpctx ctx con seen (A as A.TpName(a,nil,es)) rel (A' as A.TpName(a',nil,es')) =
    if a = a'
    (* reflexivity *)
    then case !Flags.equality
          of Flags.SubsumeRefl => eq_idx ctx con es es'
                                  orelse eq_name_name path env tpctx ctx con seen A rel A' (* both *)
           | Flags.Subsume => eq_name_name path env tpctx ctx con seen A rel A' (* only coinductive equality *)
           | Flags.Refl => eq_idx ctx con es es'                 (* only reflexivity *)
    else eq_name_name path env tpctx ctx con seen A rel A' (* coinductive type equality *)
  *)

  (* new case for polymorphism *)
  | eq_tp path env tpctx ctx con seen (A as A.TpName(a,As,es)) rel (A' as A.TpName(a',As',es')) =
    if a = a'
    (* reflexivity *)
    then case !Flags.equality
          of Flags.SubsumeRefl => (eq_idx ctx con es es'
                                   andalso eq_tp_list path env tpctx ctx con seen (variances env a) As rel As')
                                  orelse eq_name_name path env tpctx ctx con seen A rel A'
           | Flags.Subsume => eq_name_name path env tpctx ctx con seen A rel A'
           | Flags.Refl => (eq_idx ctx con es es'
                            andalso eq_tp_list path env tpctx ctx con seen (variances env a) As rel As')
    else eq_name_name path env tpctx ctx con seen A rel A'

  | eq_tp path env tpctx ctx con seen (A as A.TpName(a,As,es)) rel A' =
    eq_tp' path env tpctx ctx con seen (TU.expd env A) rel A'
  | eq_tp path env tpctx ctx con seen A rel (A' as A.TpName(a',As',es')) =
    eq_tp' path env tpctx ctx con seen A rel (TU.expd env A')

  | eq_tp path env tpctx ctx con seen A rel A' =
    ( latest_reason := SOME(Mismatch(path,A,rel,A'))
    ; false )

(* eq_tp_list path env tpctx ctx con seen (a, alphas, B) As As'
 * requires |alphas| = |As| = |As'| and a[alphas]{...} = B
 *)
and eq_tp_list path env tpctx ctx con seen nil nil rel nil = true
  | eq_tp_list path env tpctx ctx con seen (W::Ws) (A::As) rel (A'::As') =
    ( W = A.NonVar              (* don't require nonvariant argument to be related *)
      orelse eq_tp' path env tpctx ctx con seen A (nested W rel) A' )
    andalso eq_tp_list path env tpctx ctx con seen Ws As rel As'

and eq_tp_bind path env tpctx ctx con seen (v,A) rel (v',A') =
    let val sigma = R.zip ctx (R.create_idx ctx)
        val w = R.fresh_var sigma v
        val wA = A.apply_tp ((v, R.Var(w))::sigma) A
        val wA' = A.apply_tp ((v', R.Var(w))::sigma) A'
    in eq_tp' path env tpctx (w::ctx) con seen wA rel wA' end

and eq_tp_tpbind path env tpctx ctx con seen (alpha,A) rel (alpha',A') =
    let val theta = ListPair.zipEq (tpctx, List.map A.TpVar tpctx) (* create identity type subst *)
        val beta = A.fresh_tpvar theta alpha
        val B = A.subst_tp ((alpha, A.TpVar(beta))::theta) A
        val B' = A.subst_tp ((alpha', A.TpVar(beta))::theta) A'
    in eq_tp' path env (beta::tpctx) ctx con seen B rel B' end

and eq_ichoice path env tpctx ctx con seen (A as A.Plus((l,A1)::choices)) rel (A' as A.Plus(choices')) =
    (case A.lookup_choice_rest choices' l
      of NONE => if rel = A.ContraVar
                 then eq_ichoice path env tpctx ctx con seen (A.Plus(choices)) rel (A.Plus(choices'))
                 else ( latest_reason := SOME(Mismatch(path, A, rel, A')) ; false )
       | SOME(A1',choices'') => eq_tp' (Plus(l,path)) env tpctx ctx con seen A1 rel A1'
                                andalso eq_ichoice path env tpctx ctx con seen (A.Plus(choices)) rel (A.Plus(choices'')))
  | eq_ichoice path env tpctx ctx con seen (A as A.Plus(nil)) rel (A' as A.Plus((l',A1')::choices')) =
    if rel = A.CoVar
    then true
    else ( latest_reason := SOME(Mismatch(path, A, rel, A')) ; false )
  | eq_ichoice path env tpctx ctx con seen (A.Plus(nil)) rel (A.Plus(nil)) = true

and eq_echoice path env tpctx ctx con seen (A as A.With((l,A1)::choices)) rel (A' as A.With(choices')) =
    (case A.lookup_choice_rest choices' l
      of NONE => if rel = A.CoVar
                 then eq_echoice path env tpctx ctx con seen (A.With(choices)) rel (A.With(choices'))
                 else ( latest_reason := SOME(Mismatch(path, A, rel, A')) ; false )
       | SOME(A1',choices'') => eq_tp' (With(l,path)) env tpctx ctx con seen A1 rel A1'
                               andalso eq_echoice path env tpctx ctx con seen (A.With(choices)) rel (A.With(choices'')))
  | eq_echoice path env tpctx ctx con seen (A as A.With(nil)) rel (A' as A.With((l',A1')::choices')) =
    if rel = A.ContraVar
    then true
    else ( latest_reason := SOME(Mismatch(path, A, rel, A')) ; false )
  | eq_echoice path env tpctx ctx con seen (A.With(nil)) rel (A.With(nil)) = true

and eq_name_name path env tpctx ctx con seen (A as A.TpName(a,As,es)) rel (A' as A.TpName(a',As',es')) =
    let val seen_eqs = mem_seen env seen a rel a' (* relevant co-inductive hypotheses *)
        val global_eqs = mem_env env a rel a' (* relevant global assertions *)
        val subsumed = instance_of env seen tpctx ctx con (seen_eqs @ global_eqs) A rel A'
    in subsumed
       orelse if List.length seen_eqs < !Flags.expd_depth
              then eq_tp' path env tpctx ctx con ((tpctx,ctx,con,(A,rel,A'))::seen)
                          (TU.expd env A) rel (TU.expd env A')
              else ( latest_reason := SOME(BoundExceeded(path,A,rel,A')) ; false )
    end

(* interface *)
(* start algorithm with seen = nil *)
fun eq_tp env tpctx ctx con A rel B =
    ( latest_reason := NONE
    ; eq_tp' Root env tpctx ctx con nil A rel B )

end  (* structure TypeEquality *)
