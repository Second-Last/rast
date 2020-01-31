(* Quantifier Reconstruction *)
(* Applies to implicit syntax, after approximate reconstruction
 *
 * Fills in assume, assert, and impossible constructs to match
 * the types. It is complete: if there is a reconstruction, our
 * algorithm will find one. It is not sound: subsequent
 * type checking is necessary to find constraint errors in the
 * reconstructed expression.
 *)

structure QRecon :> RECON =
struct

structure R = Arith
structure A = Ast
structure PP = PPrint
structure C = Constraints
structure E = TpError
structure TU = TypeUtil
structure TCU = TypeCheckUtil
val ERROR = ErrorMsg.ERROR

(* skipping over non-structural types, stopping at quantifiers or
 * structural types *)
fun skip env (A.PayPot(_,A')) = skip env A'
  | skip env (A.GetPot(_,A')) = skip env A'
  | skip env (A.Next(_,A')) = skip env A'
  | skip env (A.Dia(A')) = skip env A'
  | skip env (A.Box(A')) = skip env A'
  | skip env (A as A.TpName(a,es)) = skip env (TU.expd env A)
  | skip env A = A

fun skipQ env A = case skip env A
                   of A.Exists(phi,A') => skipQ env A'
                    | A.Forall(phi,A') => skipQ env A'
                    | A => A

(***********************)
(* Impossible branches *)
(***********************)

(* impossL_assumes env x A = assume x {phi1} ; assume x {phi2} ; ... impossible *)
(* depending on whether A contains Exists(phi, A') *)
fun impossL_assumes env x (A.Exists(phi,A)) = A.Assume(x,phi,impossL_assumes env x A)
  | impossL_assumes env x (A as A.TpName(a,es)) = impossL_assumes env x (TU.expd env A)
  | impossL_assumes env x A = A.Imposs

(* impossL_branch env (l,A) l_opt = impossL_assumes env x A
 * if A = Exists(phi,A'), raises an exception otherwise
 * l_opt is label of the next branch if one (for error messages)
 * Checking unsat(phi) is postponed to type checking
 *)
fun impossL_branch env (x,(l,A.Exists(phi,A'))) l_opt ext' =
    (l, NONE, impossL_assumes env x (A.Exists(phi,A')))
  | impossL_branch env (x,(l,A as A.TpName(a,es))) l_opt ext' =
    impossL_branch env (x,(l,TU.expd env A)) l_opt ext'
  | impossL_branch env (x,(l,A)) NONE ext' = E.error_label_missing_branch (l,ext')
  | impossL_branch env (x,(l,A)) (SOME(l')) ext' = E.error_label_mismatch (l, l', ext')

(* impossR_assumes env x A = assume x {phi1} ; assume x {phi2} ; ... impossible *)
(* depending on whether A contains Forall(phi, A') *)
fun impossR_assumes env x (A.Forall(phi,C)) = A.Assume(x,phi,impossR_assumes env x C)
  | impossR_assumes env x (A as A.TpName(a,es)) = impossR_assumes env x (TU.expd env A)
  | impossR_assumes env x C = A.Imposs

(* impossR_branch env (l,A) = ImpossR(phi)
 * if A = Forall(phi,A'), raises an exception otherwise
 * l_opt is label of the next branch if one (for error messages)
 * Checking unsat(phi) is postponed to type checking
 *)
fun impossR_branch env (z,(l,A.Forall(phi,C'))) l' ext' =
    (l, NONE, impossR_assumes env z (A.Forall(phi,C')))
    (*
      if not (C.contradictory phi)
      then error_label_sat_con phi (l, ext')
      else (l, NONE, A.AssumeR(phi,Imposs))
     *)
  | impossR_branch env (z,(l,A as A.TpName(a,es))) l' ext' =
    impossR_branch env (z,(l,TU.expd env A)) l' ext'
  | impossR_branch env (z,(l,C)) NONE ext' = E.error_label_missing_branch (l,ext')
  | impossR_branch env (z,(l,C)) (SOME(l')) ext' = E.error_label_mismatch (l, l', ext')

(****************************)
(* Lazily inserting asserts *)
(****************************)

(* add assert z {phi} if C is Exists(phi,C') *)
fun addR_assert env P (z,A.Exists(phi,C)) = A.Assert(z,phi,addR_assert env P (z,skip env C))
  | addR_assert env P (z,C) = P

(* add assert y {phi} if A is Forall(phi,A') *)
fun addL_assert env (y,A.Forall(phi,A)) P = A.Assert(y,phi,addL_assert env (y,skip env A) P)
  | addL_assert env (y,A) P = P

(*****************************)
(* Eagerly inserting assumes *)
(*****************************)

(* add assume z {phi} if A is Forall(phi,A') *)
fun addR_assume env P (z,A.Forall(phi,C)) = A.Assume (z,phi,addR_assume env P (z,skip env C))
  | addR_assume env P (z,C) = P

(* add assume y {phi} if C is Exists(phi,C') *)
fun addL_assume env (y,A.Exists(phi,A)) P = A.Assume(y,phi,addL_assume env (y,skip env A) P)
  | addL_assume env (y,A) P = P

fun addLs_assert env D nil P = P
  | addLs_assert env D (x::xs) P =
    addLs_assert env D xs (addL_assert env (x, TCU.lookup_context env x D NONE) P)

fun add_call env D (PQ as A.Spawn(P as A.ExpName(x,f,es,xs),Q)) =
    addLs_assert env D xs PQ
  | add_call env D (A.Spawn(A.Marked(marked_P),Q)) =
    add_call env D (A.Spawn(Mark.data marked_P,Q))

(* recon env D P C ext = P'
 * where P' contains assume, assert, imposs to match all quantified
 * type constructors in A and C
 * Assumes D |- P : C, approximately
 * P' is NOT guaranteed to be well-typed
 *
 * Insert 'assume' as soon as possible and 'assert' as late as possible
 * Reconstruction does not use the variable context or constraints.
 * Checking them is postponed to type checking
 *)

(* recon does some debug printing, then calls recon' *)
fun recon env D P (z,C) ext =
  (if false then TextIO.print (PP.pp_exp_prefix env P ^ " : "
                               ^ PP.pp_tpj_compact env D (R.Int(0)) (z,C) ^ "\n") else ()
  ; recon' env D P (z,C) ext)

(* adds assumes eagerly if possible *)
and recon_assumeR env D P (z,C) ext =
    let val P' = recon env D P (z,C) ext
    in addR_assume env P' (z,skip env C) end

and recon_assumeL env D (x,A) P (z,C) ext =
    let val P' = recon env D P (z,C) ext
    in addL_assume env (x,skip env A) P' end

(* judgmental constructs: id, cut, spawn *)
and recon' env D (P as A.Id(z',y)) (z,C) ext =
    (* about to terminate, add asserts if needed *)
    let val P'  = addR_assert env P (z,skip env C)
        val P'' = addL_assert env (y, skip env (TCU.lookup_context env y D ext)) P'
    in P'' end
  | recon' env D (A.Spawn(P,Q)) (z,C) ext =
    (* D' is the context after the spawn, used to recon tail Q *)
    let val D' = TCU.syn_call env D P ext
        val Q' = recon env D' Q (z,C) ext

        (* add_call adds pending asserts on the channel being used in the spawn *)
        val PQ' = add_call env D (A.Spawn(P,Q'))
    in PQ' end

  | recon' env D (P as A.ExpName(x,f,es,xs)) (z,C) ext =
    (* add pending asserts on D and C *)
    addR_assert env (addLs_assert env D xs P) (z,skip env C)

  (* begin cases for each action matching their type *)
  (* the strategy is straightforward: recon the tail first, adding assumes *)
  (* then insert the structural expression for communication *)
  (* finally, add pending asserts on the channel being communicated, if necessary *)
  | recon' env D (A.Lab(x,k,P)) (z,C) ext =
    if x = z
    then let val P' = recon_assumeR env D P (TCU.syn_altR env (z,skipQ env C) k) ext
             val P'' = addR_assert env (A.Lab(x, k, P')) (z,skip env C)
         in P'' end
    else let val A = TCU.lookup_context env x D ext
             val D' = TCU.syn_altL env (TCU.update_tp (x,skipQ env A) D) x k
             val P' = recon_assumeL env D' (x,TCU.lookup_context env x D' ext) P (z,C) ext
             val P'' = addL_assert env (x,skip env A) (A.Lab(x,k,P'))
         in P'' end

  | recon' env D (A.Case(x,branches)) (z,C) ext =
    if x = z
    then let val branches' = recon_branchesR env D branches (TCU.syn_branchesR env (z,skipQ env C)) ext
             val P'' = addR_assert env (A.Case(x, branches')) (z, skip env C)
         in P'' end
    else let val A = TCU.lookup_context env x D ext
             val choices' = TCU.syn_branchesL env (TCU.update_tp (x,skipQ env A) D) x
             val branches' = recon_branchesL env D choices' branches (z,C) ext
             val P'' = addL_assert env (x,skip env A) (A.Case(x,branches'))
         in P'' end

  | recon' env D (A.Send(x,y,P)) (z,C) ext =
    if x = z
    then let val B = TCU.lookup_context env y D ext
             val P' = recon_assumeR env (TCU.remove_chan y D ext) P (TCU.syn_sendR env (z,skipQ env C)) ext
             val P'' = addR_assert env (A.Send(x,y,P')) (z,skip env C)
             val P''' = addL_assert env (y,skip env B) P''
         in P''' end
    else let val A = TCU.lookup_context env x D ext
             val B = TCU.lookup_context env y D ext
             val D' = TCU.remove_chan y (TCU.syn_sendL env (TCU.update_tp (x,skipQ env A) D) x) ext
             val P' = recon_assumeL env D' (x,TCU.lookup_context env x D' ext) P (z,C) ext
             val P'' = addL_assert env (x,skip env A) (A.Send(x,y,P'))
             val P''' = addL_assert env (y,skip env B) P''
         in P''' end

  | recon' env D (A.Recv(x,y,P)) (z,C) ext =
    if x = z
    then let val D' = TCU.syn_recvR1 env D (z,skipQ env C) y
             val P' = recon_assumeR env D' P (TCU.syn_recvR2 env (z,skipQ env C)) ext
             val P'' = P'
             val P''' = addR_assert env (A.Recv(x,y,P'')) (z,skip env C)
         in P''' end
    else let val A = TCU.lookup_context env x D ext
             val D' = TCU.syn_recvL env (TCU.update_tp (x,skipQ env A) D) x y
             val P' = recon_assumeL env D' (x,TCU.lookup_context env x D' ext) P (z,C) ext
             val P'' = P'
             val P''' = addL_assert env (x,skip env A) (A.Recv(x,y,P''))
         in P''' end

  | recon' env D (P as A.Close(x)) (z,C) ext = (* x = z *)
    addR_assert env P (z,skip env C)

  | recon' env D (A.Wait(x,P)) (z,C) ext = (* x <> z *)
    let val A = TCU.lookup_context env x D ext
        val D' = TCU.syn_waitL env (TCU.update_tp (x,skipQ env A) D) x
        val P' = recon env D' P (z,C) ext
        val P'' = addL_assert env (x,skip env A) (A.Wait(x,P'))
    in P'' end

  | recon' env D (A.SendNat(x,e,P)) (z,C) ext =
    if x = z
    then let val P' = recon_assumeR env D P (TCU.syn_sendNatR env e (z, skipQ env C)) ext
             val P'' = addR_assert env (A.SendNat(x,e,P')) (z, skip env C)
         in P'' end
    else let val A = TCU.lookup_context env x D ext
             val D' = TCU.syn_sendNatL env (TCU.update_tp (x, skipQ env A) D) e x
             val P' = recon_assumeL env D' (x, TCU.lookup_context env x D' ext) P (z,C) ext
             val P'' = addL_assert env (x,skip env A) (A.SendNat(x,e,P'))
         in P'' end

  | recon' env D (A.RecvNat(x,v,P)) (z,C) ext =
    if x = z
    then let val D' = D (* v goes into index variable context, which we don't track *)
             val P' = recon_assumeR env D' P (TCU.syn_recvNatR env v (z, skipQ env C)) ext
             val P'' = addR_assert env (A.RecvNat(x,v,P')) (x, skip env C)
         in P'' end
    else let val A = TCU.lookup_context env x D ext
             val D' = TCU.syn_recvNatL env (TCU.update_tp (x, skipQ env A) D) x v
             val P' = recon_assumeL env D' (x,TCU.lookup_context env x D' ext) P (z,C) ext
             val P'' = addL_assert env (x,skip env A) (A.RecvNat(x,v,P'))
         in P'' end

  (* work, which is allowed before reconstruction *)
  | recon' env D (A.Work(p,P')) zC ext =
    A.Work(p, recon env D P' zC ext)

  (* delay, which is allowed before reconstruction *)
  | recon' env D (A.Delay(t,P')) zC ext =
    A.Delay(t, recon env D P' zC ext)
    
  | recon' env D (A.Marked(marked_P)) zC ext =
    (* preserve marks for later error messages *)
    A.Marked(Mark.mark'(recon' env D (Mark.data marked_P) zC (Mark.ext marked_P),
                        Mark.ext marked_P))

(* all other cases are impossible, by approximate reconstruction *)

(* reconstruct branches *)
and recon_branchesL env D (x,nil) nil (z,C) ext = nil
  | recon_branchesL env D (x,(l,A)::choices) ((l',ext',P)::branches) (z,C) ext =
    if l = l'
    then (l',ext',recon_assumeL env (TCU.update_tp (x,A) D) (x,A) P (z,C) ext)
         ::(recon_branchesL env D (x,choices) branches (z,C) ext)
    else (impossL_branch env (x,(l,A)) (SOME(l')) ext')
         ::(recon_branchesL env D (x,choices) ((l',ext',P)::branches) (z,C) ext)
  | recon_branchesL env D (x,(l,A)::choices) nil (z,C) ext =
    (impossL_branch env (x,(l,A)) NONE ext)
    ::(recon_branchesL env D (x,choices) nil (z,C) ext)

and recon_branchesR env D nil (z,nil) ext = nil
  | recon_branchesR env D ((l,ext',P)::branches) (z,(l',C)::choices) ext =
    if l = l'
    then (l',ext',recon_assumeR env D P (z,C) ext)
         ::(recon_branchesR env D branches (z,choices) ext)
    else (impossR_branch env (z,(l',C)) (SOME(l)) ext')
         ::(recon_branchesR env D ((l,ext',P)::branches) (z,choices) ext)
  | recon_branchesR env D nil (z,(l',C)::choices) ext =
    (impossR_branch env (z,(l',C)) NONE ext)
    ::(recon_branchesR env D nil (z,choices) ext)

(* external interface: ignore potential *)
val recon = fn env => fn ctx => fn con => fn A => fn pot => fn P => fn C => fn ext => recon' env A P C ext

end (* structure QRecon *)
