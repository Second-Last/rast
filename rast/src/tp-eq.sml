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
    val eq_tp : Ast.env -> Ast.tp_ctx -> Arith.ctx -> Arith.prop -> Ast.tp -> Ast.tp -> bool

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

(* just for testing purposes *)
fun retrieve_variance alpha (beta::betas) (W::Ws) =
    if alpha = beta then W else retrieve_variance alpha betas Ws
(* nil should be impossible *)

fun invariant env a alpha =
    case A.lookup_tp env a
     of SOME(alphas, SOME(Ws), vs, phi, A) =>
        let val W = retrieve_variance alpha alphas Ws
        in W = A.NonVar end
        (* NONE should be impossible *)

(*****************)
(* Type equality *)
(*****************)

(* Reflexivity *)

(* eq_id ctx con e e' iff ctx ; con |= e = e' *)
fun eq_id ctx con e e' = C.entails ctx con (R.Eq(e,e'))

(* eq_idx ctx con es es', assumes |es| = |es'| *)
fun eq_idx ctx con nil nil = true
  | eq_idx ctx con (e::es) (e'::es') =
      eq_id ctx con e e' andalso eq_idx ctx con es es'

(* Structural equality *)

(* mem_env env a a' => [TPCTX1,CTX1,CON1,TpName(a,As1,es1),TpName(a',As1',es1'),...] *)
fun mem_env (A.TpEq(TPCTX,CTX,CON,A as A.TpName(B,AS,ES),A' as A.TpName(B',AS',ES'),_)::env) a a' =
    if B = a andalso B' = a'
    then (TPCTX,CTX,CON,(A,A'))::mem_env env a a'
    else if B = a' andalso B' = a
    then (TPCTX,CTX,CON,(A',A))::mem_env env a a'   (* flip! *)
    else mem_env env a a'
  | mem_env (_::env) a a' = mem_env env a a'
  | mem_env nil a a' = nil

(* mem_env env seen a a' => [TPCTX1,CTX1,CON1,TpName(a,As1,es1),TpName(a',As1',es1'),...] *)
fun mem_seen env ((E as (TPCTX,CTX,CON,(A as A.TpName(B,AS,ES), A' as A.TpName(B',AS',ES'))))::seen) a a' =
    if B = a andalso B' = a'
    then (TPCTX,CTX,CON,(A,A'))::mem_seen env seen a a'
    else if B = a' andalso B' = a
    then (TPCTX,CTX,CON,(A',A))::mem_seen env seen a a'
    else mem_seen env seen a a'
  | mem_seen env (_::seen) a a' = mem_seen env seen a a'
  | mem_seen env nil a a' = nil

(* fresh internal name generation, in the arithmetic layer *)
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

(* match_tp env exvars tpctx ctx con seen theta A A' = theta'
 * if theta' extends theta and [theta']A === [theta']A'
 * where === is syntactic equality
 *)

fun not_free_in betas A =
    let val alphas = A.free_tpvars nil A
    in List.all (fn beta => not (List.exists (fn alpha => alpha = beta) alphas)) betas end

(* main entry point *)
fun match_tp' env tpctx exvars locals ctx con theta A A' =
    ( () (* TextIO.print (A.Print.pp_tp A ^ " =?= " ^ A.Print.pp_tp A' ^ "\n") *)
    ; match_tp env tpctx exvars locals ctx con theta
            (aggregate_nexts env ctx con A)
            (aggregate_nexts env ctx con A')
    )

and match_tp env tpctx exvars locals ctx con theta (A.Plus(choice)) (A.Plus(choice')) =
    match_choice env tpctx exvars locals ctx con theta choice choice'
  | match_tp env tpctx exvars locals ctx con theta (A.With(choice)) (A.With(choice')) =
    match_choice env tpctx exvars locals ctx con theta choice choice'
  
  | match_tp env tpctx exvars locals ctx con theta (A.Tensor(A,B)) (A.Tensor(A',B')) =
    (case match_tp' env tpctx exvars locals ctx con theta A A'
      of NONE => NONE
       | SOME(theta1) => match_tp' env tpctx exvars locals ctx con theta1 B B')
  | match_tp env tpctx exvars locals ctx con theta (A.Lolli(A,B)) (A.Lolli(A',B')) =
    (case match_tp' env tpctx exvars locals ctx con theta A A'
      of NONE => NONE
       | SOME(theta1) => match_tp' env tpctx exvars locals ctx con theta1 B B')

  | match_tp env tpctx exvars locals ctx con theta (A.One) (A.One) = SOME(theta)

  | match_tp env tpctx exvars locals ctx con theta (A.Exists(phi,A)) (A.Exists(phi',A')) =
    if C.equiv ctx con phi phi'
    then match_tp' env tpctx exvars locals ctx (R.And(con,phi)) theta A A'
    else NONE
  | match_tp env tpctx exvars locals ctx con theta (A.Forall(phi,A)) (A.Forall(phi',A')) =
    if C.equiv ctx con phi phi'
    then match_tp' env tpctx exvars locals ctx (R.And(con,phi)) theta A A'
    else NONE

  | match_tp env tpctx exvars locals ctx con theta (A.ExistsNat(v,A)) (A.ExistsNat(v',A')) =
    match_tp_bind env tpctx exvars locals ctx con theta (v,A) (v',A')
  | match_tp env tpctx exvars locals ctx con theta (A.ForallNat(v,A)) (A.ForallNat(v',A')) =
    match_tp_bind env tpctx exvars locals ctx con theta (v,A) (v',A')

  | match_tp env tpctx exvars locals ctx con theta (A.ExistsTp(alpha,A)) (A.ExistsTp(alpha',A')) =
    match_tp_tpbind env tpctx exvars locals ctx con theta (alpha,A) (alpha',A')
  | match_tp env tpctx exvars locals ctx con theta (A.ForallTp(alpha,A)) (A.ForallTp(alpha',A')) =
    match_tp_tpbind env tpctx exvars locals ctx con theta (alpha,A) (alpha',A')

  | match_tp env tpctx exvars locals ctx con theta (A.PayPot(p,A)) (A.PayPot(p',A')) =
    if eq_id ctx con p p'
    then match_tp' env tpctx exvars locals ctx con theta A A'
    else NONE
  | match_tp env tpctx exvars locals ctx con theta (A.GetPot(p,A)) (A.GetPot(p',A')) = 
    if eq_id ctx con p p'
    then match_tp' env tpctx exvars locals ctx con theta A A'
    else NONE

  | match_tp env tpctx exvars locals ctx con theta (A.Next(t,A)) (A.Next(t',A')) =
    if eq_id ctx con t t'
    then match_tp' env tpctx exvars locals ctx con theta A A'
    else NONE
  | match_tp env tpctx exvars locals ctx con theta (A.Box(A)) (A.Box(A')) =
    match_tp' env tpctx exvars locals ctx con theta A A'
  | match_tp env tpctx exvars locals ctx con theta (A.Dia(A)) (A.Dia(A')) =
    match_tp' env tpctx exvars locals ctx con theta A A'
    
  | match_tp env tpctx exvars locals ctx con theta (A.TpVar(alpha)) A' =
    if List.exists (fn beta => beta = alpha) exvars
    then (* alpha is subject to instantiation! *)
        case List.find (fn (beta,B) => beta = alpha) theta
         of NONE => if not_free_in locals A'
                    then SOME((alpha,A')::theta)
                    else NONE
          | SOME(beta,B) => (* B = A' required, no further instantiation for matching *)
            (* B should not depend on locals, but A' might *)
            (case match_tp env tpctx [] locals ctx con [] B A'
              of NONE => NONE
               | SOME [] => SOME(theta)
            (* SOME(_::_) should be impossible *)
            )
    else (* alpha is not subject to instantiation! *)
        (* this means it should be in locals or tpctx *)
        if List.exists (fn beta => beta = alpha) (tpctx @ locals)
        then (case A'
               of A.TpVar(alpha') => if alpha = alpha' then SOME(theta) else NONE
                | _ => NONE)
        else raise Match (* this should be impossible *)

  | match_tp env tpctx exvars locals ctx con theta (A as A.TpName(a,As,es)) (A' as A.TpName(a',As',es')) =
    if a = a' andalso eq_idx ctx con es es'
    then match_tp_list env tpctx exvars locals ctx con theta (tp_def env a) As As'
    else NONE

  | match_tp env tpctx exvars locals ctx con theta (A as A.TpName(a,As,es)) A' =
    match_tp' env tpctx exvars locals ctx con theta (TU.expd env A) A'
  | match_tp env tpctx exvars locals ctx con theta A (A' as A.TpName(a',As',es')) =
    match_tp' env tpctx exvars locals ctx con theta A (TU.expd env A')

  | match_tp env tpctx exvars locals ctx con theta A A' = NONE

(* match_tp_list env tpctx exvars locals ctx con theta (a, alphas, B) As As'
 * requires |alphas| = |As| = |As'| and a[alphas]{...} = B
 *)
and match_tp_list env tpctx exvars locals ctx con theta (a, nil, B) nil nil = SOME(theta)
  | match_tp_list env tpctx exvars locals ctx con theta (a, alpha::alphas, B) (A::As) (A'::As') =
    if invariant env a alpha
    then match_tp_list env tpctx exvars locals ctx con theta (a, alphas, B) As As'
    else case match_tp' env tpctx exvars locals ctx con theta A A'
          of NONE => NONE
           | SOME(theta1) => match_tp_list env tpctx exvars locals ctx con theta1 (a, alphas, B) As As'

and match_tp_bind env tpctx exvars locals ctx con theta (v,A) (v',A') =
    let val sigma = R.zip ctx (R.create_idx ctx)
        val w = R.fresh_var sigma v
        val wA = A.apply_tp ((v, R.Var(w))::sigma) A
        val wA' = A.apply_tp ((v', R.Var(w))::sigma) A'
    in match_tp' env tpctx exvars locals (w::ctx) con theta wA wA' end

and match_tp_tpbind env tpctx exvars locals ctx con theta (alpha,A) (alpha',A') =
    let val allVars = tpctx @ exvars @ locals
        val dummy = ListPair.zipEq (allVars, List.map A.TpVar allVars)
        val beta = A.fresh_tpvar dummy alpha
        val B = A.subst_tp [(alpha, A.TpVar(beta))] A
        val B' = A.subst_tp [(alpha', A.TpVar(beta))] A'
    in match_tp' env tpctx exvars (beta::locals) ctx con theta B B' end

and match_choice env tpctx exvars locals ctx con theta ((l,A)::choices) choices' =
    (case A.lookup_choice_rest choices' l
      of NONE => NONE
       | SOME(A',choices'') =>
         case match_tp' env tpctx exvars locals ctx con theta A A'
          of NONE => NONE
           | SOME(theta1) => match_choice env tpctx exvars locals ctx con theta1 choices choices'')
  | match_choice env tpctx exvars locals ctx con theta nil ((l',A')::choices') = NONE
  | match_choice env tpctx exvars locals ctx con theta nil nil = SOME(theta)

(* eq_tp' env con seen A A' = true if (A == A') *)

(* main entry point *)
fun eq_tp' env tpctx ctx con seen A A' =
    ( () (* TextIO.print (A.Print.pp_tp A ^ " =?= " ^ A.Print.pp_tp A' ^ "\n") *)
    ; eq_tp env tpctx ctx con seen
            (aggregate_nexts env ctx con A)
            (aggregate_nexts env ctx con A')
    )

and eq_tp env tpctx ctx con seen (A.Plus(choice)) (A.Plus(choice')) =
    eq_choice env tpctx ctx con seen choice choice'
  | eq_tp env tpctx ctx con seen (A.With(choice)) (A.With(choice')) =
    eq_choice env tpctx ctx con seen choice choice'
  
  | eq_tp env tpctx ctx con seen (A.Tensor(A,B)) (A.Tensor(A',B')) =
    eq_tp' env tpctx ctx con seen A A'
    andalso eq_tp' env tpctx ctx con seen B B'
  | eq_tp env tpctx ctx con seen (A.Lolli(A,B)) (A.Lolli(A',B')) =
    eq_tp' env tpctx ctx con seen A A'
    andalso eq_tp' env tpctx ctx con seen B B'

  | eq_tp env tpctx ctx con seen (A.One) (A.One) = true

  | eq_tp env tpctx ctx con seen (A.Exists(phi,A)) (A.Exists(phi',A')) =
    C.equiv ctx con phi phi'
    andalso eq_tp' env tpctx ctx (R.And(con,phi)) seen A A'
    (* for now, require equality even in the presence of contradictory constraints *)
    (* orelse C.contradictory ctx con phi *)
  | eq_tp env tpctx ctx con seen (A.Forall(phi,A)) (A.Forall(phi',A')) =
    C.equiv ctx con phi phi'
    andalso eq_tp' env tpctx ctx (R.And(con,phi)) seen A A'
    (* for now, require equality even in the presence of contradictory constraints *)
    (* orelse C.contradictory ctx con phi *)

  | eq_tp env tpctx ctx con seen (A.ExistsNat(v,A)) (A.ExistsNat(v',A')) =
    eq_tp_bind env tpctx ctx con seen (v,A) (v',A')
  | eq_tp env tpctx ctx con seen (A.ForallNat(v,A)) (A.ForallNat(v',A')) =
    eq_tp_bind env tpctx ctx con seen (v,A) (v',A')

  | eq_tp env tpctx ctx con seen (A.ExistsTp(alpha,A)) (A.ExistsTp(alpha',A')) =
    eq_tp_tpbind env tpctx ctx con seen (alpha,A) (alpha',A')
  | eq_tp env tpctx ctx con seen (A.ForallTp(alpha,A)) (A.ForallTp(alpha',A')) =
    eq_tp_tpbind env tpctx ctx con seen (alpha,A) (alpha',A')

  | eq_tp env tpctx ctx con seen (A.PayPot(p,A)) (A.PayPot(p',A')) =
    eq_id ctx con p p' andalso eq_tp' env tpctx ctx con seen A A'
  | eq_tp env tpctx ctx con seen (A.GetPot(p,A)) (A.GetPot(p',A')) = 
    eq_id ctx con p p' andalso eq_tp' env tpctx ctx con seen A A'

  | eq_tp env tpctx ctx con seen (A.Next(t,A)) (A.Next(t',A')) =
    eq_id ctx con t t' andalso eq_tp' env tpctx ctx con seen A A'
  | eq_tp env tpctx ctx con seen (A.Box(A)) (A.Box(A')) =
    eq_tp' env tpctx ctx con seen A A'
  | eq_tp env tpctx ctx con seen (A.Dia(A)) (A.Dia(A')) =
    eq_tp' env tpctx ctx con seen A A'
  | eq_tp env tpctx ctx con seen (A.TpVar(alpha)) (A.TpVar(alpha')) =
    alpha = alpha'

  (* case prior to polymorphism untouched *)
  | eq_tp env tpctx ctx con seen (A as A.TpName(a,nil,es)) (A' as A.TpName(a',nil,es')) =
    if a = a'
    (* reflexivity *)
    then case !Flags.equality
          of Flags.SubsumeRefl => eq_idx ctx con es es' orelse eq_name_name env tpctx ctx con seen A A' (* both *)
           | Flags.Subsume => eq_name_name env tpctx ctx con seen A A' (* only coinductive equality *)
           | Flags.Refl => eq_idx ctx con es es'                 (* only reflexivity *)
    else eq_name_name env tpctx ctx con seen A A' (* coinductive type equality *)

  (* new case for polymorphism *)
  | eq_tp env tpctx ctx con seen (A as A.TpName(a,As,es)) (A' as A.TpName(a',As',es')) =
    if a = a'
    (* reflexivity *)
    then case !Flags.equality
          of Flags.SubsumeRefl => eq_tp_list env tpctx ctx con seen (tp_def env a) As As'
                                  orelse eq_name_name env tpctx ctx con seen A A'
           | Flags.Subsume => eq_name_name env tpctx ctx con seen A A'
           | Flags.Refl => eq_tp_list env tpctx ctx con seen (tp_def env a) As As'
    else eq_name_name env tpctx ctx con seen A A'
    (*
    then eq_tp_list env tpctx ctx con seen (tp_def env a) As As' (* only reflexivity here *)
    else eq_name_name env tpctx ctx con seen A A' (* coinductive type equality *)
    *)

  | eq_tp env tpctx ctx con seen (A as A.TpName(a,As,es)) A' =
    eq_tp' env tpctx ctx con seen (TU.expd env A) A'
  | eq_tp env tpctx ctx con seen A (A' as A.TpName(a',As',es')) =
    eq_tp' env tpctx ctx con seen A (TU.expd env A')

  | eq_tp env tpctx ctx con seen A A' = false

(* eq_tp_list env tpctx ctx con seen (a, alphas, B) As As'
 * requires |alphas| = |As| = |As'| and a[alphas]{...} = B
 *)
and eq_tp_list env tpctx ctx con seen (a, nil, B) nil nil = true
  | eq_tp_list env tpctx ctx con seen (a, alpha::alphas, B) (A::As) (A'::As') =
    ( () (* TextIO.print ("checking args!\n") *)
    ; invariant env a alpha  (* or a[..,alpha,...] = B does not depend on alpha *)
      orelse eq_tp' env tpctx ctx con seen A A' )               (* A = A' *)
    andalso eq_tp_list env tpctx ctx con seen (a, alphas, B) As As'

and eq_tp_bind env tpctx ctx con seen (v,A) (v',A') =
    let val sigma = R.zip ctx (R.create_idx ctx)
        val w = R.fresh_var sigma v
        val wA = A.apply_tp ((v, R.Var(w))::sigma) A
        val wA' = A.apply_tp ((v', R.Var(w))::sigma) A'
    in eq_tp' env tpctx (w::ctx) con seen wA wA' end

and eq_tp_tpbind env tpctx ctx con seen (alpha,A) (alpha',A') =
    let val theta = ListPair.zipEq (tpctx, List.map A.TpVar tpctx) (* create identity type subst *)
        val beta = A.fresh_tpvar theta alpha
        val B = A.subst_tp ((alpha, A.TpVar(beta))::theta) A
        val B' = A.subst_tp ((alpha', A.TpVar(beta))::theta) A'
    in eq_tp' env (beta::tpctx) ctx con seen B B' end

and eq_choice env tpctx ctx con seen ((l,A)::choices) choices' =
    (case A.lookup_choice_rest choices' l
      of NONE => false
       | SOME(A',choices'') => eq_tp' env tpctx ctx con seen A A'
                               andalso eq_choice env tpctx ctx con seen choices choices'')
  | eq_choice env tpctx ctx con seen nil ((l',A')::choices') = false
  | eq_choice env tpctx ctx con seen nil nil = true

and eq_name_name env tpctx ctx con seen (A as A.TpName(a,As,es)) (A' as A.TpName(a',As',es')) =
    eq_name_name_seen env tpctx ctx con seen (mem_seen env seen a a') A A'
and eq_name_name_seen env tpctx ctx con seen nil (A as A.TpName(a,As,es)) (A' as A.TpName(a',As',es')) =
    eq_name_name_eqs env tpctx ctx con seen (mem_env env a a') A A' (* an instance of global eq decls *)
    orelse eq_tp' env tpctx ctx con ((tpctx,ctx,con,(A,A'))::seen) (* or a local equality loop *)
                  (TU.expd env A) (TU.expd env A')
  | eq_name_name_seen env tpctx ctx con seen seen_eqs (A as A.TpName(a,As,es)) (A' as A.TpName(a',As',es')) =
    (* seen_eqs <> nil, so don't add another equality to help termination issues *)
    eq_name_name_eqs env tpctx ctx con seen (seen_eqs @ mem_env env a a') A A'
and eq_name_name_eqs env tpctx ctx con seen nil A A' = false (* do not recurse *)
  | eq_name_name_eqs env tpctx ctx con seen
                     ((TPCTX,CTX,CON, (W as A.TpName(_,AS,ES), W' as A.TpName(_,AS',ES')))::eqs)
                     (A as A.TpName(a,As,es)) (A' as A.TpName(a',As',es')) =
    (* eq_tp_list env tpctx ctx con seen (tp_def env a) As AS (* no binders, so no change in type context allowed *)
     andalso eq_tp_list env tpctx ctx con seen (tp_def env a') As' AS'
     *)
    (* now there are binders, so we check for substitution instances *)
    (* !!! use of ctx and con here is suspicious/wrong !!! *)
    (case match_tp_list env tpctx TPCTX [] ctx con [] (tp_def env a) AS As
      of NONE => eq_name_name_eqs env tpctx ctx con seen eqs A A'
       | SOME(theta1) => case match_tp_list env tpctx TPCTX [] ctx con theta1 (tp_def env a') AS' As'
                          of NONE => eq_name_name_eqs env tpctx ctx con seen eqs A A'
                           | SOME(theta2) => 
                             (* As = AS andalso As' = AS' *)
                             let val (FCTX,sigma) = gen_fresh CTX
                                 val FCON = R.apply_prop sigma CON
                                 val FES = R.apply_list sigma ES
                                 val FES' = R.apply_list sigma ES'
                                 val phi = gen_prop_eq FCTX FCON FES es FES' es'
                                 val result = C.entails ctx con phi (* could be trusting non-linear *)
                             in
                                 result orelse eq_name_name_eqs env tpctx ctx con seen eqs A A'
                             end)

(* interface *)
(* start algorithm with seen = nil *)
fun eq_tp env tpctx ctx con A B = eq_tp' env tpctx ctx con nil A B

end  (* structure TypeEquality *)
