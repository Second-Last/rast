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

    val eq_tp : Ast.env -> Arith.ctx -> Arith.prop -> Ast.tp -> Ast.tp -> bool

end  (* signature TYPE_EQUALITY *)

structure TypeEquality :> TYPE_EQUALITY =
struct

structure R = Arith
structure A = Ast
structure PP = PPrint
structure TU = TypeUtil
structure C = Constraints

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
  | aggregate_nexts' env ctx con s (A as A.TpName(a,es)) =
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
    eq_tp' env ctx con seen (TU.expd env A) A'
  | eq_tp env ctx con seen A (A' as A.TpName(a',es')) =
    eq_tp' env ctx con seen A (TU.expd env A')

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
                       (TU.expd env A) (TU.expd env A')
      | SOME(CTX,CON, (A.TpName(_,ES), A.TpName(_,ES'))) =>
        let val (FCTX,sigma) = gen_fresh CTX
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
fun eq_tp env ctx con A B = eq_tp' env ctx con nil A B

end  (* structure TypeEquality *)
