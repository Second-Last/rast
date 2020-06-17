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
     of SOME(alphas, vs, con, B) => (a, alphas, B)
        (* NONE should be impossible *)

fun invariant env seen alpha (A.Plus(choices)) = invariant_choices env seen alpha choices
  | invariant env seen alpha (A.With(choices)) = invariant_choices env seen alpha choices
  | invariant env seen alpha (A.Tensor(A,B)) = invariant env seen alpha A andalso invariant env seen alpha B
  | invariant env seen alpha (A.Lolli(A,B)) = invariant env seen alpha A andalso invariant env seen alpha B
  | invariant env seen alpha (A.One) = true
  | invariant env seen alpha (A.Exists(phi,A)) = invariant env seen alpha A
  | invariant env seen alpha (A.Forall(phi,A)) = invariant env seen alpha A
  | invariant env seen alpha (A.ExistsNat(v,A)) = invariant env seen alpha A
  | invariant env seen alpha (A.ForallNat(v,A)) = invariant env seen alpha A
  | invariant env seen alpha (A.ExistsTp(alpha',A)) = alpha = alpha' orelse invariant env seen alpha A
  | invariant env seen alpha (A.ForallTp(alpha',A)) = alpha = alpha' orelse invariant env seen alpha A
  | invariant env seen alpha (A.PayPot(p,A)) = invariant env seen alpha A
  | invariant env seen alpha (A.GetPot(p,A)) = invariant env seen alpha A
  | invariant env seen alpha (A.Next(t,A)) = invariant env seen alpha A
  | invariant env seen alpha (A.Dia(A)) = invariant env seen alpha A
  | invariant env seen alpha (A.Box(A)) = invariant env seen alpha A
  | invariant env seen alpha (A.TpVar(beta)) = (alpha <> beta)
  | invariant env seen alpha (A.TpName(a,As,es)) =
    invariant_list env seen alpha (tp_def env a) As
and invariant_choices env seen alpha nil = true
  | invariant_choices env seen alpha ((l,Al)::choices) =
    invariant env seen alpha Al andalso invariant_choices env seen alpha choices
and invariant_list env seen alpha (a, nil, B) nil = true
  | invariant_list env seen alpha (a, beta::betas, B) (A::As) =
    ( List.exists (fn (a',beta') => (a,beta) = (a',beta')) seen
      orelse invariant env ((a,beta)::seen) beta B )
    andalso invariant_list env seen alpha (a, betas, B) As

(*
val invariant = fn env => fn seen => fn alpha => fn A =>
    let val () = TextIO.print ("%inv " ^ alpha ^ " in " ^ A.Print.pp_tp A)
        val r = invariant env seen alpha A
        val () = TextIO.print (" == " ^ (if r then "true" else "false") ^ "\n")
    in r end
*)

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

(* mem_env env a a' => SOME(CTX,CON,TpName(a,As,es),TpName(a',As',es')) if exists in env *)
(* still need to generalize for type arguments *)
fun mem_env (A.TpEq(CTX,CON,A as A.TpName(B,AS,ES),A' as A.TpName(B',AS',ES'),_)::env) a a' =
    if B = a andalso B' = a'
    then SOME(CTX,CON,(A,A'))
    else if B = a' andalso B' = a
    then SOME(CTX,CON,(A',A))   (* flip! *)
    else mem_env env a a'
  | mem_env (_::env) a a' = mem_env env a a'
  | mem_env nil a a' = NONE

(* mem_env env seen a a' => SOME(CTX,CON,TpName(a,As,es),TpName(a',As',es')) if exists in seen *)
fun mem_seen env ((E as (CTX,CON,(A as A.TpName(B,AS,ES), A' as A.TpName(B',AS',ES'))))::seen) a a' =
    if B = a andalso B' = a'
    then SOME(CTX,CON,(A,A'))
    else if B = a' andalso B' = a
    then SOME(CTX,CON,(A',A))
    else mem_seen env seen a a'
  | mem_seen env (_::seen) a a' = mem_seen env seen a a'
  | mem_seen env nil a a' = mem_env env a a'

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
    then eq_tp_list env tpctx ctx con seen (tp_def env a) As As' (* only reflexivity here *)
    else eq_name_name env tpctx ctx con seen A A' (* coinductive type equality *)

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
    ; eq_tp' env tpctx ctx con seen A A'               (* A = A' *)
     orelse invariant env [(a,alpha)] alpha B)  (* or a[..,alpha,...] = B does not depend on alpha *)
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
    in eq_tp' env tpctx ctx con seen B B' end

and eq_choice env tpctx ctx con seen ((l,A)::choices) choices' =
    (case A.lookup_choice_rest choices' l
      of NONE => false
       | SOME(A',choices'') => eq_tp' env tpctx ctx con seen A A'
                               andalso eq_choice env tpctx ctx con seen choices choices'')
  | eq_choice env tpctx ctx con seen nil ((l',A')::choices') = false
  | eq_choice env tpctx ctx con seen nil nil = true

and eq_name_name env tpctx ctx con seen (A as A.TpName(a,As,es)) (A' as A.TpName(a',As',es')) =
    case mem_seen env seen a a'
     of NONE => eq_tp' env tpctx ctx con ((ctx,con,(A,A'))::seen)
                       (TU.expd env A) (TU.expd env A')
      | SOME(CTX,CON, (W as A.TpName(_,AS,ES), W' as A.TpName(_,AS',ES'))) =>
        (* (TextIO.print "found!\n";
            TextIO.print (A.Print.pp_tp W ^ " =!= " ^ A.Print.pp_tp W' ^ "\n") ; *)
        eq_tp_list env tpctx ctx con seen (tp_def env a) As AS (* no binders, so no change in type context allowed *)
        andalso eq_tp_list env tpctx ctx con seen (tp_def env a') As' AS'
         (* As = AS andalso As' = AS' *)
        andalso let val (FCTX,sigma) = gen_fresh CTX
                    val FCON = R.apply_prop sigma CON
                    val FES = R.apply_list sigma ES
                    val FES' = R.apply_list sigma ES'
                    val phi = gen_prop_eq FCTX FCON FES es FES' es'
                    val result = C.entails ctx con phi (* could be trusting non-linear *)
                in
                    result
                end

(* interface *)
(* start algorithm with seen = nil *)
fun eq_tp env tpctx ctx con A B = eq_tp' env tpctx ctx con nil A B

end  (* structure TypeEquality *)
