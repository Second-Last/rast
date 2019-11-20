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

fun skipW env A =
  case skip env A
  of A.GetPot(p,A') => skipW env A'
   | A.PayPot(p,A') => skipW env A'
   | A' => A'

(* copied from qrecon.sml and updated *)
(* is there a simple way to unify these? *)

(*
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

*)

fun addR_pay env P (z,A.PayPot(p,C)) = A.Pay(z,p,addR_pay env P (z,skip env C))
  | addR_pay env P (z,C) = P

fun addL_pay env (y,A.GetPot(p,A)) P = A.Pay(y,p,addL_pay env (y,skip env A) P)
  | addL_pay env (y,A) P = P

fun addR_get env P (z,A.GetPot(p,C)) = A.Get (z,p,addR_get env P (z,skip env C))
  | addR_get env P (z,C) = P

fun addL_get env (y,A.PayPot(p,A)) P = A.Get(y,p,addL_get env (y,skip env A) P)
  | addL_get env (y,A) P = P

fun addLs_pay env D nil P = P
  | addLs_pay env D (x::xs) P =
    addLs_pay env D xs (addL_pay env (x, TC.lookup_context env x D NONE) P)

fun add_call env D (PQ as A.Spawn(P as A.ExpName(x,f,es,xs),Q)) =
    addLs_pay env D xs PQ
  | add_call env D (A.Spawn(A.Marked(marked_P),Q)) =
    add_call env D (A.Spawn(Mark.data marked_P,Q))

(* must_work env P = SOME(p) if must extent some work now, to be left with p
 *                 = NONE if we do not need to work now
 *)
fun must_work env (A.Id(x,y)) = SOME(R.Int(0)) (* consume all remaining potential to reach 0 *)
  | must_work env (A.ExpName(x,f,es,xs)) =
    (case A.expd_expdec env (f, es)
      of SOME(_,(_,pot,_)) => SOME(pot) (* consume enough potential to reach pot *)
       | NONE => NONE (* no need to postpone; will raise error later *)
    )
  | must_work env (A.Close(x)) = SOME(R.Int(0)) (* consume remaining potential to reach 0 *)
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
  recon''' env ctx con A pot P C ext

(*
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

*)

(* recon'' env ctx con A pot P C ext = P'
 * assumes A and C are structural or quantifiers
 * and NOT get/pay potential expressions
 * checks if there is remaining potential that must be spent
 * and insert work{p} it if necessary.  Since we do not track
 * constraints we might insert work{0}.
 *)
and recon'' env ctx con D pot P C ext = (* have pot *)
    (case must_work env P
      of SOME(pot') => (* must have pot' left, pot >= pot' *)
         if C.hardentails ctx con (R.Eq(pot, pot'))
         then recon''' env ctx con D pot P C ext
         else A.Work(R.minus(pot,pot'), (* leaves pot - (pot - pot') = pot' *)
                      recon''' env ctx con D pot' P C ext)
       | NONE => recon''' env ctx con D pot P C ext
    )

and recon_getR env ctx con D pot P (z,C) ext =
    let val P' = recon env ctx con D pot P (z,C) ext
    in addR_get env P' (z,skip env C) end

and recon_getL env ctx con D (x,A) pot P (z,C) ext =
    let val P' = recon env ctx con D pot P (z,C) ext
    in addL_get env (x,skip env A) P' end

(* recon''' env ctx con A pot P C ext = P'
 * assumes A and C are structural or quantifiers and
 * it does not need to insert any terminal work into P
 *)
(* judgmental constructs: id, cut, spawn, call *)
and recon''' env ctx con D pot (P as A.Id(z',y)) (z,C) ext =
    let val P' = addR_pay env P (z,skip env C)
        val P'' = addL_pay env (y,skip env (TC.lookup_context env y D ext)) P'
    in P'' end
  | recon''' env ctx con D pot (A.Spawn(P,Q)) (z,C) ext =
    let val D' = TC.syn_call env D P ext
        val potP = TC.syn_pot env P ext
        val potQ = R.minus(pot,potP)
        val Q' = recon env ctx con D' potQ Q (z,C) ext
        val PQ' = add_call env D (A.Spawn(P,Q'))
    in PQ' end
  | recon'''  env ctx con D pot (P as A.ExpName(x,f,es,xs)) (z,C) ext =
    addLs_pay env D xs P

  (* begin cases for each action matching their type *)
  | recon''' env ctx con D pot (A.Lab(x,k,P)) (z,C) ext =
    if x = z
    then let val P' = recon_getR env ctx con D pot P (TC.syn_altR env (z,skipW env C) k) ext
             val P'' = addR_pay env (A.Lab(x, k, P')) (z,skip env C)
         in P'' end
    else let val A = TC.lookup_context env x D ext
             val D' = TC.syn_altL env (TC.update_tp (x,skipW env A) D) x k
             val P' = recon_getL env ctx con D' (x,TC.lookup_context env x D' ext) pot P (z,C) ext
             val P'' = addL_pay env (x,skip env A) P'
         in P'' end

  | recon''' env ctx con D pot (A.Case(x,branches)) (z,C) ext =
    if x = z
    then let val branches' = recon_branchesR env ctx con D pot branches (TC.syn_branchesR env (z,skipW env C)) ext
             val P'' = addR_pay env (A.Case(x, branches')) (z, skip env C)
         in P'' end
    else let val A = TC.lookup_context env x D ext
             val choices' = TC.syn_branchesL env (TC.update_tp (x,skipW env A) D) x
             val branches' = recon_branchesL env ctx con D choices' pot branches (z,C) ext
             val P'' = addL_pay env (x,skip env A) (A.Case(x,branches'))
         in P'' end

  | recon''' env ctx con D pot (A.Send(x,y,P)) (z,C) ext =
    if x = z
    then let val B = TC.lookup_context env y D ext
             val P' = recon_getR env ctx con (TC.remove_chan y D ext) pot P (TC.syn_sendR env (z,skipW env C)) ext
             val P'' = addR_pay env (A.Send(x,y,P')) (z,skip env C)
             val P''' = addL_pay env (y,skip env B) P''
         in P''' end
    else let val A = TC.lookup_context env x D ext
             val B = TC.lookup_context env y D ext
             val D' = TC.remove_chan y (TC.syn_sendL env (TC.update_tp (x,skipW env A) D) x) ext
             val P' = recon_getL env ctx con D' (x,TC.lookup_context env x D' ext) pot P (z,C) ext
             val P'' = addL_pay env (x,skip env A) (A.Send(x,y,P'))
             val P''' = addL_pay env (y,skip env B) P''
         in P''' end

  | recon''' env ctx con D pot (A.Recv(x,y,P)) (z,C) ext =
    if x = z
    then let val D' = TC.syn_recvR1 env D (z,skipW env C) y
             val P' = recon_getR env ctx con D' pot P (TC.syn_recvR2 env (z,skipW env C)) ext
             val P'' = P' (* recon_assumeL env D' (y,TC.lookup_context env y D' ext) P' (z,C) ext *)
             val P''' = addR_pay env (A.Recv(x,y,P'')) (z,skip env C)
         in P''' end
    else let val A = TC.lookup_context env x D ext
             val D' = TC.syn_recvL env (TC.update_tp (x,skipW env A) D) x y
             val P' = recon_getL env ctx con D' (x,TC.lookup_context env x D' ext) pot P (z,C) ext
             val P'' = P' (* recon_assumeL env D' (y,TC.lookup_context env y D' ext) P' (z,C) ext *)
             val P''' = addL_pay env (x,skip env A) (A.Recv(x,y,P''))
         in P''' end

  | recon''' env ctx con D pot (P as A.Close(x)) (z,C) ext = (* x = z *)
    addR_pay env P (z,skip env C)
  | recon''' env ctx con D pot (A.Wait(x,P)) (z,C) ext = (* x <> z *)
    let val A = TC.lookup_context env x D ext
        val D' = TC.syn_waitL env (TC.update_tp (x,skipW env A) D) x
        val P' = recon env ctx con D' pot P (z,C) ext
        val P'' = addL_pay env (x,skip env A) (A.Wait(x,P'))
    in P'' end

  (* quantifiers *)
  | recon''' env ctx con D pot (A.Assert(x,phi,P)) (z,C) ext =
    if x = z
    then let val P' = recon_getR env ctx con D pot P (TC.syn_assertR env (z,skipW env C)) ext
             val P'' = addR_pay env (A.Assert(x, phi, P')) (z,skip env C)
         in P'' end
    else let val A = TC.lookup_context env x D ext
             val D' = TC.syn_assertL env (TC.update_tp (x,skipW env A) D) x
             val P' = recon_getL env ctx con D' (x,TC.lookup_context env x D' ext) pot P (z,C) ext
             val P'' = addL_pay env (x,skip env A) (A.Assert(x,phi,P'))
         in P'' end
  | recon''' env ctx con D pot (A.Assume(x,phi, P)) (z,C) ext =
    if x = z
    then let val P' = recon_getR env ctx con D pot P (TC.syn_assumeR env (z,skipW env C)) ext
             val P'' = addR_pay env (A.Assume(x,phi,P')) (z,skip env C)
         in P'' end
    else let val A = TC.lookup_context env x D ext
             val D' = TC.syn_assumeL env (TC.update_tp (x,skipW env A) D) x
             val P' = recon_getL env ctx con D' (x,TC.lookup_context env x D' ext) pot P (z,C) ext
             val P'' = addL_pay env (x,skip env A) (A.Assume(x,phi,P'))
         in P'' end
  (* end structural cases *)

  (* impossibility *)
  | recon''' env ctx con D pot (A.Imposs) (z,C) ext = A.Imposs

  (* from the cost model *)
  | recon''' env ctx con D pot (A.Work(p,P)) (z,C) ext =
    A.Work(p, recon env ctx con D (R.minus (pot,p)) P (z,C) ext) (* pot >= p, to be enforced later *)

  (* pass through temporal operator *)
  | recon''' env ctx con A pot (A.Delay(t,P)) C ext =
    A.Delay(t, recon env ctx con A pot P C ext)

  (* traverse but preserve marks *)
  | recon''' env ctx con A pot (A.Marked(marked_P)) C ext =
    A.Marked(Mark.mark'(recon''' env ctx con A pot (Mark.data marked_P) C (Mark.ext marked_P),
                        Mark.ext marked_P))

  (* all other cases are impossible, since we assume approximate typing *)

and recon_branchesL env ctx con D (x,nil) pot nil (z,C) ext = nil
  | recon_branchesL env ctx con D (x,(l,A)::choices) pot ((l',ext',P)::branches) (z,C) ext =
    (* after quantifer reconstruction, branches must match choices exactly *)
    (l',ext',recon_getL env ctx con (TC.update_tp (x,A) D) (x,A) pot P (z,C) ext)
    ::(recon_branchesL env ctx con D (x,choices) pot branches (z,C) ext)

and recon_branchesR env ctx con D pot nil (z,nil) ext = nil
  | recon_branchesR env ctx con D pot ((l,ext',P)::branches) (z,(l',C)::choices) ext =
    (* after quantifer reconstruction, branches must match choices exactly *)
    (l',ext',recon_getR env ctx con D pot P (z,C) ext)
    ::(recon_branchesR env ctx con D pot branches (z,choices) ext)

(* external interface *)
(* at present, we do not pass through constraints *)
val recon = fn env => fn ctx => fn con => fn A => fn pot => fn P => fn C => fn ext =>
            recon env ctx con A pot P C ext

end (* structure WRecon *)
