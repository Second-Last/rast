(* Work Reconstruction *)

(* Authors: Ankush Das <ankushd@cs.cmu.edu>
 *          Frank Pfenning <fp@cs.cmu.edu>
 *)

(*
 * Applies to implicit syntax, after approximate and
 * quantifier reconstruction
 *
 * Fill in pay/get potential and additional work{p} expressions
 * The result is not always very clean (e.g., it might insert
 * work{0}), but the algorithm is complete.  The result
 * is not necessarily well-typed, which is later verified via
 * type checking on the reconstructed expression
 *
 * The strategy for reconstruction is the same as for quantifiers:
 * constructs for invertible types are inserted as soon as possible
 * and for noninvertible types as late as possible.  That is, we
 * get potential as soon as we can and pay as late as we can.
 * Calls provide the main difficult part, since they fix
 * an interface type.
 *)

structure WRecon :> RECON =
struct

structure R = Arith
structure A = Ast
structure PP = PPrint
structure C = Constraints
structure E = TpError
structure TU = TypeUtil
structure TCU = TypeCheckUtil
val ERROR = ErrorMsg.ERROR

(* skip temporal operations; quantifiers are considered structural here *)
fun skip env (A.Next(_,A')) = skip env A'
  | skip env (A.Dia(A')) = skip env A'
  | skip env (A.Box(A')) = skip env A'
  | skip env (A as A.TpName(a,As,es)) = skip env (TU.expd env A)
  | skip env A = A

fun skipW env A =
  case skip env A
  of A.GetPot(p,A') => skipW env A'
   | A.PayPot(p,A') => skipW env A'
   | A' => A'

(* insert pay/get *)
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
    addLs_pay env D xs (addL_pay env (x, TCU.lookup_context env x D NONE) P)

fun add_call env D (PQ as A.Spawn(P as A.ExpName(x,f,As,es,xs),Q)) =
    addLs_pay env D xs PQ
  | add_call env D (A.Spawn(A.Marked(marked_P),Q)) =
    add_call env D (A.Spawn(Mark.data marked_P,Q))

(* recon env D P C ext = P'
 * where P' contains pay/get potential and additional work * where needed
 * 'pot' tracks the available potential
 * Assumes D |- P : C, approximately
 *
 * P' is NOT guaranteed to be well-typed, because constraint solving
 * is left to type checking
 *)
fun recon env D P zC ext =
  recon' env D P zC ext

and recon_getR env D P (z,C) ext =
    let val P' = recon env D P (z,C) ext
    in addR_get env P' (z,skip env C) end

and recon_getL env D (x,A) P (z,C) ext =
    let val P' = recon env D P (z,C) ext
    in addL_get env (x,skip env A) P' end

(* recon' env A P C ext = P'
 * assumes A and C are structural or quantifiers and
 * it does not need to insert any terminal work into P
 *)
(* judgmental constructs: id, cut, spawn, call *)
and recon' env D (P as A.Id(z',y)) (z,C) ext =
    let val P' = addR_pay env P (z,skip env C)
        val P'' = addL_pay env (y,skip env (TCU.lookup_context env y D ext)) P'
    in P'' end
  | recon' env D (A.Spawn(P,Q)) (z,C) ext =
    let val D' = TCU.syn_call env D P ext
        val Q' = recon env D' Q (z,C) ext
        val PQ' = add_call env D (A.Spawn(P,Q'))
    in PQ' end
  | recon'  env D (P as A.ExpName(x,f,As,es,xs)) (z,C) ext =
    addR_pay env (addLs_pay env D xs P) (z,skip env C)

  (* begin cases for each action matching their type *)
  (* follows the same strategy as proof constraints *)
  | recon' env D (A.Lab(x,k,P)) (z,C) ext =
    if x = z
    then let val P' = recon_getR env D P (TCU.syn_altR env (z,skipW env C) k) ext
             val P'' = addR_pay env (A.Lab(x, k, P')) (z,skip env C)
         in P'' end
    else let val A = TCU.lookup_context env x D ext
             val D' = TCU.syn_altL env (TCU.update_tp (x,skipW env A) D) x k
             val P' = recon_getL env D' (x,TCU.lookup_context env x D' ext) P (z,C) ext
             val P'' = addL_pay env (x,skip env A) (A.Lab(x,k,P'))
         in P'' end

  | recon' env D (A.Case(x,branches)) (z,C) ext =
    if x = z
    then let val branches' = recon_branchesR env D branches (TCU.syn_branchesR env (z,skipW env C)) ext
             val P'' = addR_pay env (A.Case(x, branches')) (z, skip env C)
         in P'' end
    else let val A = TCU.lookup_context env x D ext
             val choices' = TCU.syn_branchesL env (TCU.update_tp (x,skipW env A) D) x
             val branches' = recon_branchesL env D choices' branches (z,C) ext
             val P'' = addL_pay env (x,skip env A) (A.Case(x,branches'))
         in P'' end

  | recon' env D (A.Send(x,y,P)) (z,C) ext =
    if x = z
    then let val B = TCU.lookup_context env y D ext
             val P' = recon_getR env (TCU.remove_chan y D ext) P (TCU.syn_sendR env (z,skipW env C)) ext
             val P'' = addR_pay env (A.Send(x,y,P')) (z,skip env C)
             val P''' = addL_pay env (y,skip env B) P''
         in P''' end
    else let val A = TCU.lookup_context env x D ext
             val B = TCU.lookup_context env y D ext
             val D' = TCU.remove_chan y (TCU.syn_sendL env (TCU.update_tp (x,skipW env A) D) x) ext
             val P' = recon_getL env D' (x,TCU.lookup_context env x D' ext) P (z,C) ext
             val P'' = addL_pay env (x,skip env A) (A.Send(x,y,P'))
             val P''' = addL_pay env (y,skip env B) P''
         in P''' end

  | recon' env D (A.Recv(x,y,P)) (z,C) ext =
    if x = z
    then let val D' = TCU.syn_recvR1 env D (z,skipW env C) y
             val P' = recon_getR env D' P (TCU.syn_recvR2 env (z,skipW env C)) ext
             val P'' = P' (* recon_assumeL env D' (y,TCU.lookup_context env y D' ext) P' (z,C) ext *)
             val P''' = addR_pay env (A.Recv(x,y,P'')) (z,skip env C)
         in P''' end
    else let val A = TCU.lookup_context env x D ext
             val D' = TCU.syn_recvL env (TCU.update_tp (x,skipW env A) D) x y
             val P' = recon_getL env D' (x,TCU.lookup_context env x D' ext) P (z,C) ext
             val P'' = P' (* recon_assumeL env D' (y,TCU.lookup_context env y D' ext) P' (z,C) ext *)
             val P''' = addL_pay env (x,skip env A) (A.Recv(x,y,P''))
         in P''' end

  | recon' env D (P as A.Close(x)) (z,C) ext = (* x = z *)
    addR_pay env P (z,skip env C)
  | recon' env D (A.Wait(x,P)) (z,C) ext = (* x <> z *)
    let val A = TCU.lookup_context env x D ext
        val D' = TCU.syn_waitL env (TCU.update_tp (x,skipW env A) D) x
        val P' = recon env D' P (z,C) ext
        val P'' = addL_pay env (x,skip env A) (A.Wait(x,P'))
    in P'' end

  (* quantifiers *)
  | recon' env D (A.Assert(x,phi,P)) (z,C) ext =
    if x = z
    then let val P' = recon_getR env D P (TCU.syn_assertR env (z,skipW env C)) ext
             val P'' = addR_pay env (A.Assert(x, phi, P')) (z,skip env C)
         in P'' end
    else let val A = TCU.lookup_context env x D ext
             val D' = TCU.syn_assertL env (TCU.update_tp (x,skipW env A) D) x
             val P' = recon_getL env D' (x,TCU.lookup_context env x D' ext) P (z,C) ext
             val P'' = addL_pay env (x,skip env A) (A.Assert(x,phi,P'))
         in P'' end
  | recon' env D (A.Assume(x,phi, P)) (z,C) ext =
    if x = z
    then let val P' = recon_getR env D P (TCU.syn_assumeR env (z,skipW env C)) ext
             val P'' = addR_pay env (A.Assume(x,phi,P')) (z,skip env C)
         in P'' end
    else let val A = TCU.lookup_context env x D ext
             val D' = TCU.syn_assumeL env (TCU.update_tp (x,skipW env A) D) x
             val P' = recon_getL env D' (x,TCU.lookup_context env x D' ext) P (z,C) ext
             val P'' = addL_pay env (x,skip env A) (A.Assume(x,phi,P'))
         in P'' end

  | recon' env D (A.SendNat(x,e,P)) (z,C) ext =
    if x = z
    then let val P' = recon_getR env D P (TCU.syn_sendNatR env e (z, skipW env C)) ext
             val P'' = addR_pay env (A.SendNat(x,e,P')) (z,skip env C)
         in P'' end
    else let val A = TCU.lookup_context env x D ext
             val D' = TCU.syn_sendNatL env (TCU.update_tp (x, skipW env A) D) e x
             val P' = recon_getL env D' (x, TCU.lookup_context env x D' ext) P (z,C) ext
             val P'' = addL_pay env (x,skip env A) (A.SendNat(x,e,P'))
         in P'' end

  | recon' env D (A.RecvNat(x,v,P)) (z,C) ext =
    if x = z
    then let val D' = D (* v goes into index variable context, which we don't track *)
             val P' = recon_getR env D' P (TCU.syn_recvNatR env v (z, skipW env C)) ext
             val P'' = addR_pay env (A.RecvNat(x,v,P')) (x, skip env C)
         in P'' end
    else let val A = TCU.lookup_context env x D ext
             val D' = TCU.syn_recvNatL env (TCU.update_tp (x, skipW env A) D) x v
             val P' = recon_getL env D' (x,TCU.lookup_context env x D' ext) P (z,C) ext
             val P'' = addL_pay env (x,skip env A) (A.RecvNat(x,v,P'))
         in P'' end

  (* end structural cases *)

  (* impossibility *)
  | recon' env D (A.Imposs) (z,C) ext = A.Imposs

  (* from the cost model *)
  | recon' env D (A.Work(p,P)) (z,C) ext =
    A.Work(p, recon env D P (z,C) ext) (* pot >= p, to be enforced later *)

  (* pass through temporal operator *)
  | recon' env A (A.Delay(t,P)) C ext =
    A.Delay(t, recon env A P C ext)

  (* traverse but preserve marks *)
  | recon' env A (A.Marked(marked_P)) C ext =
    A.Marked(Mark.mark'(recon' env A (Mark.data marked_P) C (Mark.ext marked_P),
                        Mark.ext marked_P))

  (* all other cases are impossible, since we assume approximate typing *)

and recon_branchesL env D (x,nil) nil (z,C) ext = nil
  | recon_branchesL env D (x,(l,A)::choices) ((l',ext',P)::branches) (z,C) ext =
    (* after quantifer reconstruction, branches must match choices exactly *)
    (l',ext',recon_getL env (TCU.update_tp (x,A) D) (x,A) P (z,C) ext)
    ::(recon_branchesL env D (x,choices) branches (z,C) ext)

and recon_branchesR env D nil (z,nil) ext = nil
  | recon_branchesR env D ((l,ext',P)::branches) (z,(l',C)::choices) ext =
    (* after quantifer reconstruction, branches must match choices exactly *)
    (l',ext',recon_getR env D P (z,C) ext)
    ::(recon_branchesR env D branches (z,choices) ext)

(* insert_work env pot P = P'
 * checks if there is remaining potential that must be spent
 * and insert work{p} it if necessary.  Since we do not track
 * constraints we might insert work{0}.
 *)
fun last_insert env pot (P as A.Id(x,y)) = A.Work(pot,P)
  | last_insert env pot (P as A.ExpName(x,f,As,es,xs)) =
      (case A.expd_expdec env (f,As,es)
        of SOME(_,(_,potf,_)) => A.Work(R.minus(pot,potf),P))
  | last_insert env pot (P as A.Close(x)) = A.Work(pot,P)

fun insert_work env pot (P as A.Id(z,x)) =
    last_insert env pot P
  | insert_work env pot (A.Spawn(P,Q)) =
    let val potP = TCU.syn_pot env P NONE
        val potQ = R.minus(pot,potP)
    in A.Spawn(P, insert_work env potQ Q) end
  | insert_work env pot (P as A.ExpName(x,f,As,es,xs)) =
    last_insert env pot P
  | insert_work env pot (A.Lab(x,k,P)) =
    A.Lab(x,k, insert_work env pot P)
  | insert_work env pot (A.Case(x,branches)) =
    A.Case(x, insert_work_branches env pot branches)
  | insert_work env pot (A.Send(x,y,P)) =
    A.Send(x,y, insert_work env pot P)
  | insert_work env pot (A.Recv(x,y,P)) =
    A.Recv(x,y, insert_work env pot P)
  | insert_work env pot (P as A.Close(x)) =
    last_insert env pot P
  | insert_work env pot (A.Wait(x,P)) =
    A.Wait(x, insert_work env pot P)
  | insert_work env pot (A.Assert(x,phi,P)) =
    A.Assert(x,phi, insert_work env pot P)
  | insert_work env pot (A.Assume(x,phi,P)) =
    A.Assume(x,phi, insert_work env pot P)
  | insert_work env pot (A.SendNat(x,e,P)) =
    A.SendNat(x,e, insert_work env pot P)
  | insert_work env pot (A.RecvNat(x,v,P)) =
    A.RecvNat(x,v, insert_work env pot P)
  | insert_work env pot (A.Imposs) = A.Imposs
  | insert_work env pot (A.Work(p,P)) =
    A.Work(p, insert_work env (R.minus(pot,p)) P)
  | insert_work env pot (A.Pay(x,p,P)) =
    A.Pay(x,p, insert_work env (R.minus(pot,p)) P)
  | insert_work env pot (A.Get(x,p,P)) =
    A.Get(x,p, insert_work env (R.plus(pot,p)) P)
  | insert_work env pot (A.Delay(t,P)) =
    A.Delay(t, insert_work env pot P)
  | insert_work env pot (A.Marked(marked_P)) =
    A.Marked(Mark.mark'(insert_work env pot (Mark.data marked_P),
                        Mark.ext marked_P))

and insert_work_branches env pot nil = nil
  | insert_work_branches env pot ((l,ext,P)::branches) =
    (l,ext, insert_work env pot P)
    ::(insert_work_branches env pot branches)
    
(* external interface *)
(* at present, we do not pass through constraints *)
val recon = fn env => fn ctx => fn con => fn D => fn pot => fn P => fn zC => fn ext =>
            insert_work env pot (recon env D P zC ext)

end (* structure WRecon *)
