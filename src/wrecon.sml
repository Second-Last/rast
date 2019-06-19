(* Work Reconstruction
 * applies to implicit syntax, after approximate and
 * quantifier reconstruction
 *
 * Fill is pay/get potential and additional work{p} expressions
 * The result is not always very clean (e.g., it might insert
 * work{0}), but we believe the algorithm is complete.  The result
 * is not necessarily well-typed, which is later verified via
 * type checking on the reconstructed expression
 *
 * The strategy for reconstruction is the same as for quantifiers:
 * constructs for invertible types are inserted as soon as possible
 * and for noninvertible types as late as possible.  That is, we
 * get potential as soon as we can and pay as late as we can.
 * Calls and cuts provide the main difficult part, since they fix
 * an interface types
 *)

structure WRecon :> RECON =
struct

structure R = Arith
structure A = Ast
structure PP = PPrint
structure C = Constraints
structure E = TpError
structure TC = TypeCheck
val ERROR = ErrorMsg.ERROR

(* skip temporal operations; quantifiers are considered structural here *)
fun skip env (A.Next(_,A')) = skip env A'
  | skip env (A.Dia(A')) = skip env A'
  | skip env (A.Box(A')) = skip env A'
  | skip env (A.TpName(a,es)) = skip env (A.expd_tp env (a,es))
  | skip env A = A

(* copied from qrecon.sml and updated *)
(* is there a simple way to unify these? *)

(* matching_wprefix env A B, where A = <| A' or A = |> A' *)
fun matching_wprefix env A B = matching_wprefix' env (skip env A) (skip env B)
and matching_wprefix' env (A.PayPot(p,A')) (A.PayPot(q,B')) = true
  | matching_wprefix' env (A.GetPot(p,A')) (A.GetPot(q,B')) = true
  | matching_wprefix' env A B = false

(* we insert assumeL if must_postponeL is false *)
fun must_postponeL env A' (A.Id) = false (* need not postpone *)
  | must_postponeL env A' (A.Cut(P,lpot,B,Q)) = must_postponeL env A' P
  | must_postponeL env A' (A.Spawn(P,Q)) = must_postponeL env A' P
  | must_postponeL env A' (A.ExpName(f,es)) =
    matching_wprefix env A' (TC.synL env (f,es))
  (* left interactions *)
  | must_postponeL env A' (A.LabL _) = false
  | must_postponeL env A' (A.CaseL _) = false
  | must_postponeL env A' (A.WaitL _) = false
  | must_postponeL env A' (A.AssumeL _) = false
  | must_postponeL env A' (A.AssertL _) = false
  (* right interactions *)
  | must_postponeL env A' (A.LabR(_, P))  = must_postponeL env A' P
  | must_postponeL env A' (A.CaseR(branches)) = must_postpone_branchesL env A' branches
  | must_postponeL env A' (A.CloseR) = false
  | must_postponeL env A' (A.AssertR(phi, P)) = must_postponeL env A' P
  | must_postponeL env A' (A.AssumeR(phi, P)) = must_postponeL env A' P
  (* neutral *)
  | must_postponeL env A' (A.Imposs) = false
  | must_postponeL env A' (A.Work(p,P)) = must_postponeL env A' P
  | must_postponeL env A' (A.Delay(t,P)) = must_postponeL env A' P
  | must_postponeL env A' (A.Marked(marked_P)) = must_postponeL env A' (Mark.data marked_P)
  (* illegal, catch later *)
  | must_postponeL env A' P = false
(* must postpone if just one branch forces it *)
and must_postpone_branchesL env A' nil = false
  | must_postpone_branchesL env A' ((l,_,P)::branches) =
    must_postponeL env A' P orelse must_postpone_branchesL env A' branches

(* we insert assumeR if must_postponeR is false *)
fun must_postponeR env (A.Id) C' = false (* need not postpone *)
  | must_postponeR env (A.Cut(P, _, _, Q)) C' = must_postponeR env Q C'
  | must_postponeR env (A.Spawn(P,Q)) C' = must_postponeR env Q C'
  | must_postponeR env (A.ExpName(f,es)) C' =
    matching_wprefix env (TC.synR env (f,es)) C'
  (* right interactions *)
  | must_postponeR env (A.LabR _) C' = false
  | must_postponeR env (A.CaseR _) C' = false
  | must_postponeR env (A.CloseR) C' = false
  | must_postponeR env (A.AssertR _) C' = false
  | must_postponeR env (A.AssumeR _) C' = false
  (* left interactions *)
  | must_postponeR env (A.LabL(_, P)) C' = must_postponeR env P C'
  | must_postponeR env (A.CaseL(branches)) C' = must_postpone_branchesR env branches C'
  | must_postponeR env (A.WaitL(P)) C' = must_postponeR env P C'
  | must_postponeR env (A.AssertL(_,P)) C' = must_postponeR env P C'
  | must_postponeR env (A.AssumeL(_,P)) C' = must_postponeR env P C'
  (* neutral *)
  | must_postponeR env (A.Imposs) C' = false
  | must_postponeR env (A.Work(p,P)) C' = must_postponeR env P C'
  | must_postponeR env (A.Delay(t,P)) C' = must_postponeR env P C'
  | must_postponeR env (A.Marked(marked_P)) C' = must_postponeR env (Mark.data marked_P) C'
  (* illegal, catch later *)
  | must_postponeR env P C' = false
(* must postpoint if just one branch forces it *)
and must_postpone_branchesR env nil C' = false
  | must_postpone_branchesR env ((l,_,P)::branches) C' =
    must_postponeR env P C' orelse must_postpone_branchesR env branches C'

(* we insert payL if may_postponeL is false *)
fun may_postponeL env A' (A.Id) = false (* cannot postpone past 'forward' *)
  | may_postponeL env A' (A.Cut(P,lpot,B,Q)) = true
  | may_postponeL env A' (A.Spawn(P,Q)) = may_postponeL env A' P
  | may_postponeL env A' (A.ExpName(f,es)) =
    matching_wprefix env A' (TC.synL env (f,es))
  (* left interactions *)
  | may_postponeL env A' (A.LabL _) = false
  | may_postponeL env A' (A.CaseL _) = false
  | may_postponeL env A' (A.WaitL _) = false
  | may_postponeL env A' (A.AssertL _) = false
  | may_postponeL env A' (A.AssumeL _) = false
  (* right interactions *)
  | may_postponeL env A' (A.LabR(_, P))  = true
  | may_postponeL env A' (A.CaseR(branches)) = true (* push into each branch *)
  | may_postponeL env A' (A.CloseR) = false (* can not postpone past closeR *)
  | may_postponeL env A' (A.AssertR(_,P)) = true
  | may_postponeL env A' (A.AssumeR(_,P)) = true
  (* neutral *)
  | may_postponeL env A' (A.Imposs) = false
  | may_postponeL env A' (A.Work(p,P)) = true
  | may_postponeL env A' (A.Delay(t,P)) = true
  | may_postponeL env A' (A.Marked(marked_P)) = may_postponeL env A' (Mark.data marked_P)
  (* illegal, catch later *)
  | may_postponeL env A' P = true (* default is 'true' *)

(* we insert PayR if may_postponeR is false *)
fun may_postponeR env (A.Id) C' = false (* cannot postpone *)
  | may_postponeR env (A.Cut(P, _, _, Q)) C' = true
  | may_postponeR env (A.Spawn(P,Q)) C' = true
  | may_postponeR env (A.ExpName(f,es)) C' =
    matching_wprefix env (TC.synR env (f,es)) C'
  (* right interactions *)
  | may_postponeR env (A.LabR _) C' = false
  | may_postponeR env (A.CaseR _) C' = false
  | may_postponeR env (A.CloseR) C' = false
  | may_postponeR env (A.AssertR _) C' = false
  | may_postponeR env (A.AssumeR _) C' = false
  (* left interactions *)
  | may_postponeR env (A.LabL(_, P)) C' = true
  | may_postponeR env (A.CaseL(branches)) C' = true
  | may_postponeR env (A.WaitL(P)) C' = true
  | may_postponeR env (A.AssertL _) C' = true
  | may_postponeR env (A.AssumeL _) C' = true
  (* neutral *)
  | may_postponeR env (A.Imposs) C' = false (* TODO: check! *)
  | may_postponeR env (A.Work(p,P)) C' = true
  | may_postponeR env (A.Delay(t,P)) C' = true
  | may_postponeR env (A.Marked(marked_P)) C' = may_postponeR env (Mark.data marked_P) C'
  (* illegal, catch later *)
  | may_postponeR env P C' = true (* default is 'true' *)

(* must_work env P = SOME(p) if must extent some work now, to be left with p
 *                 = NONE if we do not need to work now
 *)
fun must_work env (A.Id) = SOME(R.Int(0)) (* consume all remaining potential to reach 0 *)
  | must_work env (A.ExpName(f,es)) =
    (case A.expd_expdec env (f, es)
      of SOME(_,(_,pot,_)) => SOME(pot) (* consume enough potential to reach pot *)
       | NONE => NONE (* no need to postpone; will raise error later *)
    )
  | must_work env (A.CloseR) = SOME(R.Int(0)) (* consume remaining potential to reach 0 *)
  | must_work env (A.Marked(marked_P)) = must_work env (Mark.data marked_P)
  | must_work env P = NONE

(* recon env ctx con A pot P C ext = P'
 * where P' contains pay/get potential and additional work * where needed
 * 'pot' tracks the available potential
 * Assumes A |- P : C, approximately
 *
 * P' is NOT guaranteed to be well-typed, because constraint solving
 * is left to type checking
 *)
fun recon env ctx con A pot P C ext =
    let
        val A' = skip env A  (* A' is structural or quantifier *)
        val C' = skip env C  (* C' is structural or quantifier *)
    in
        recon' env ctx con A' pot P C' ext
    end

(* recon' env ctx con A pot P C ext = P'
 * receives potential as early as possible and pays
 * potential as late as possible
 * otherwise see recon'
 *)
and recon' env ctx con (A as A.PayPot(pot',A')) pot P C ext =
    if not (must_postponeL env A P)
    then A.GetL(pot', recon env ctx con A' (R.plus(pot',pot)) P C ext)
    else recon'' env ctx con A pot P C ext
  | recon' env ctx con A pot P (C as A.GetPot(pot',C')) ext =
    if not (must_postponeR env P C)
    then A.GetR(pot', recon env ctx con A (R.plus(pot',pot)) P C' ext)
    else recon'' env ctx con A pot P C ext
  | recon' env ctx con (A as A.GetPot(pot',A')) pot P C ext =
    if not (may_postponeL env A P)
    then A.PayL(pot', recon env ctx con A' (R.minus(pot,pot')) P C ext)
    else recon'' env ctx con A pot P C ext
  | recon' env ctx con A pot P (C as A.PayPot(pot',C')) ext =
    if not (may_postponeR env P C)
    then A.PayR(pot', recon env ctx con A (R.minus(pot,pot')) P C' ext)
    else recon'' env ctx con A pot P C ext
  | recon' env ctx con A pot P C ext =
    recon'' env ctx con A pot P C ext

(* recon'' env ctx con A pot P C ext = P'
 * assumes A and C are structural or quantifiers
 * and NOT get/pay potential expressions
 * checks if there is remaining potential that must be spent
 * and insert work{p} it if necessary.  Since we do not track
 * constraints we might insert work{0}.
 *)
and recon'' env ctx con A pot P C ext = (* have pot *)
    (case must_work env P
      of SOME(pot') => (* must have pot' left, pot >= pot' *)
         if C.hardentails ctx con (R.Eq(pot, pot'))
         then recon''' env ctx con A pot P C ext
         else A.Work(R.minus(pot,pot'), (* leaves pot - (pot - pot') = pot' *)
                      recon''' env ctx con A pot' P C ext)
       | NONE => recon''' env ctx con A pot P C ext
    )

(* recon''' env ctx con A pot P C ext = P'
 * assumes A and C are structural or quantifiers and
 * it does not need to insert any terminal work into P
 *)
(* judgmental constructs: id, cut, spawn, call *)
and recon''' env ctx con A pot (A.Id) C ext = A.Id
  | recon''' env ctx con A pot (A.Cut(P,lpot,B,Q)) C ext =
    A.Cut(recon env ctx con A lpot P B ext, lpot, B,
          recon env ctx con B (R.minus (pot,lpot)) Q C ext) (* pot >= lpot *)
  | recon''' env ctx con A pot (A.Spawn(P,Q)) C ext =
    let val (A', pot', P', B) = TC.syn_call env P ext
    in A.Spawn(P', recon env ctx con B (R.minus(pot,pot')) Q C ext) end
  | recon'''  env ctx con A pot (P as A.ExpName(f,es)) C ext = P

  (* begin cases for each action matching their type *)
  | recon''' env ctx con A pot (A.LabR(k,P)) (C as A.Plus(choices)) ext =
    A.LabR(k, recon env ctx con A pot P (TC.syn_alt env choices k) ext)
  | recon''' env ctx con (A.Plus(choices)) pot (A.CaseL(branches)) C ext =
    A.CaseL(recon_branchesL env ctx con choices pot branches C ext)

  | recon''' env ctx con A pot (A.CaseR(branches)) (A.With(choices)) ext =
    A.CaseR(recon_branchesR env ctx con A pot branches choices ext)
  | recon''' env ctx con (A as A.With(choices)) pot (A.LabL(k,Q)) C ext =
    A.LabL(k, recon env ctx con (TC.syn_alt env choices k) pot Q C ext)

  | recon''' env ctx con (A.Dot) pot (A.CloseR) C ext = A.CloseR
  | recon''' env ctx con (A.One) pot (A.WaitL(Q)) C ext =
    A.WaitL(recon env ctx con (A.Dot) pot Q C ext)

  (* quantifiers *)
  | recon''' env ctx con A pot (A.AssertR(phi,P)) (A.Exists(phi',C')) ext =
    A.AssertR(phi,recon env ctx con A pot P C' ext)
  | recon''' env ctx con (A.Exists(phi',A')) pot (A.AssumeL(phi, P)) C ext =
    A.AssumeL(phi,recon env ctx con A' pot P C ext)

  | recon''' env ctx con A pot (A.AssumeR(phi,P)) (A.Forall(phi',C')) ext =
    A.AssumeR(phi, recon env ctx con A pot P C' ext)
  | recon''' env ctx con (A.Forall(phi',A')) pot (A.AssertL(phi,P)) C ext =
    A.AssertL(phi, recon env ctx con A' pot P C ext)
  (* end structural cases *)

  (* impossibility *)
  | recon''' env ctx con A pot (A.Imposs) C ext = A.Imposs

  (* from the cost model *)
  | recon''' env ctx con A pot (A.Work(p,P)) C ext =
    A.Work(p, recon env ctx con A (R.minus (pot,p)) P C ext) (* pot >= p, to be enforced later *)

  (* pass through temporal operator *)
  | recon''' env ctx con A pot (A.Delay(t,P)) C ext =
    A.Delay(t, recon env ctx con A pot P C ext)

  (* traverse but preserve marks *)
  | recon''' env ctx con A pot (A.Marked(marked_P)) C ext =
    A.Marked(Mark.mark'(recon''' env ctx con A pot (Mark.data marked_P) C (Mark.ext marked_P),
                        Mark.ext marked_P))

  (* all other cases are impossible, since we assume approximate typing *)

and recon_branchesL env ctx con nil pot nil C ext = nil
  | recon_branchesL env ctx con ((l,A)::choices) pot ((l',ext',P)::branches) C ext =
    (* after quantifer reconstruction, branches must match choices exactly *)
    (l',ext',recon env ctx con A pot P C ext)::(recon_branchesL env ctx con choices pot branches C ext)

and recon_branchesR env ctx con A pot nil nil ext = nil
  | recon_branchesR env ctx con A pot ((l,ext',P)::branches) ((l',C)::choices) ext =
    (* after quantifer reconstruction, branches must match choices exactly *)
    (l,ext',recon env ctx con A pot P C ext)::(recon_branchesR env ctx con A pot branches choices ext)

(* external interface *)
(* at present, we do not pass through constraints *)
val recon = fn env => fn ctx => fn con => fn A => fn pot => fn P => fn C => fn ext =>
            recon env ctx con A pot P C ext

end (* structure WRecon *)
