(* Quantifier Reconstruction *)
(* Applies to implicit syntax, after approximate reconstruction
 *
 * Fills in assume, assert, and impossible constructs to match
 * the types.  We believe this is complete: if there is a reconstruction
 * this algorithm will find one.  It is not sound: subsequent
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
structure TC = TypeCheck
val ERROR = ErrorMsg.ERROR

(* skipping over non-structural types, stopping at quantifiers or
 * structural types *)
fun skip env (A.PayPot(_,A')) = skip env A'
  | skip env (A.GetPot(_,A')) = skip env A'
  | skip env (A.Next(_,A')) = skip env A'
  | skip env (A.Dia(A')) = skip env A'
  | skip env (A.Box(A')) = skip env A'
  | skip env (A.TpName(a,es)) = skip env (A.expd_tp env (a,es))
  | skip env A = A

fun skipQ env A = case skip env A
                   of A.Exists(phi,A') => skipQ env A'
                    | A.Forall(phi,A') => skipQ env A'
                    | A => A

(* impossL_branch env (l,A) l_opt = ImpossL(phi)
 * if A = Exists(phi,A'), raises an exception otherwise
 * l_opt is label of the next branch if one (for error messages)
 * Checking unsat(phi) is postponed to type checking
 *)
fun impossL_branch env (x,(l,A.Exists(phi,A'))) _ ext' =
    (l, NONE, A.Assume(x,phi,A.Imposs))
  | impossL_branch env (x,(l,A.TpName(a,es))) l_opt ext' =
    impossL_branch env (x,(l,A.expd_tp env (a,es))) l_opt ext'
  | impossL_branch env (x,(l,A)) NONE ext' = E.error_label_missing_branch (l,ext')
  | impossL_branch env (x,(l,A)) (SOME(l')) ext' = E.error_label_mismatch (l, l', ext')

(* impossR_branch env (l,A) = ImpossR(phi)
 * if A = Forall(phi,A'), raises an exception otherwise
 * l_opt is label of the next branch if one (for error messages)
 * Checking unsat(phi) is postponed to type checking
 *)
fun impossR_branch env (z,(l,A.Forall(phi,C'))) l' ext' =
    (l, NONE, A.Assume(z,phi,A.Imposs))
    (*
      if not (C.contradictory phi)
      then error_label_sat_con phi (l, ext')
      else (l, NONE, A.AssumeR(phi,Imposs))
     *)
  | impossR_branch env (z,(l,A.TpName(a,es))) l' ext' =
    impossR_branch env (z,(l,A.expd_tp env (a,es))) l' ext'
  | impossR_branch env (z,(l,C)) NONE ext' = E.error_label_missing_branch (l,ext')
  | impossR_branch env (z,(l,C)) (SOME(l')) ext' = E.error_label_mismatch (l, l', ext')

(* matching_qprefix env A B, where A = !{phi}. A' or A = ?{phi}. A' initially *)
fun matching_qprefix env A B = matching_qprefix' env (skip env A) (skip env B)
and matching_qprefix' env (A.Exists(phi,A')) (A.Exists(psi,B')) = true
  | matching_qprefix' env (A.Forall(phi,A')) (A.Forall(psi,B')) = true
  | matching_qprefix' env A B = false


(*
(* we insert assumeL if must_postpone is false *)
fun must_postpone env (w,A) D (A.Id(z,y)) (z',C) = (* z' = z *)
    if w = y then matching_qprefix env A C
    else if w = z then matching_qprefix env A (TC.lookup_context env y D NONE)
    else false (* impossible? *)
  | must_postpone env (w,A) D (A.Spawn(P as A.ExpName(y,f,es,xs),Q)) (z,C) =
    if List.exists (fn x => w = x) xs
    then (* argument to call: compare types *)
        let val Df = TC.synL env (y,f,es,xs)  (* x1:A1,...,xn:An as synthesized from f *)
            val A' = TC.lookup_context env w Df NONE (* A' is expanded; type for w expected by f *)
        in matching_qprefix env A A' end
    else must_postpone env (w,A) (TC.syn_call env D P NONE) Q (z,C)
  | must_postpone env (w,A) D (A.Spawn(A.Marked(marked_P),Q)) (z,C) =
      must_postpone env (w,A) D (A.Spawn(Mark.data marked_P, Q)) (z,C)
  | must_postpone env (w,A) D (A.ExpName(y,f,es,xs)) (z,C) =
    if w = y
    then let val (_,A') = TC.synR env (y,f,es,xs)
         in matching_qprefix env A A' end
    else let val D' = TC.synL env (y,f,es,xs)
             val A' = TC.lookup_context env w D' NONE (* A' is expanded; type for x expected by f *)
         in matching_qprefix env A A' end

  (* structural interactions *)
  | must_postpone env (w,A) D (A.Lab(x,k,P)) (z,C) =
    if w = x then false
    else if x = z then must_postpone env (w,A) D P (TC.syn_altR env (z,C) k)
    else must_postpone env (w,A) (TC.syn_altL env D x k) P (z,C)
  | must_postpone env (w,A) D (A.Case(x,branches)) (z,C) =
    if w = x then false
    else if x = z then must_postpone_branchesR env (w,A) D branches (TC.syn_branchesR env (z,C))
    else must_postpone_branchesL env (w,A) D (TC.syn_branchesL env D x) branches (z,C)
  | must_postpone env (w,A) D (A.Send(x,y,P)) (z,C) =
    if w = x then false
    else if w = y
    then case TC.lookup_context env x D NONE
          of A.Lolli(A',B) => matching_qprefix env A A'
           | A.Tensor(A',B) => matching_qprefix env A A'
    else if x = z then must_postpone env (w,A) (TC.remove_chan y D NONE) P (TC.syn_sendR env (z,C))
    else must_postpone env (w,A) (TC.syn_sendL env (TC.remove_chan y D NONE) x) P (z,C)
  | must_postpone env (w,A) D (A.Recv(x,y,P)) (z,C) =
    if w = x then false
    else if x = z then must_postpone env (w,A) (TC.syn_recvR1 env D (z,C) y) P (TC.syn_recvR2 env (z,C))
    else must_postpone env (w,A) (TC.syn_recvL env D x y) P (z,C)
  | must_postpone env (w,A) D (A.Wait(x,P)) (z,C) =
    if w = x then false
    else must_postpone env (w,A) (TC.syn_waitL env D x) P (z,C)
  | must_postpone env (w,A) D (A.Close(x)) (z,C) = false
  (* neutral *)
  | must_postpone env (w,A) D (A.Delay(t,P)) (z,C) = must_postpone env (w,A) D P (z,C)
  | must_postpone env (w,A) D (A.Work(p,P)) (z,C) = must_postpone env (w,A) D P (z,C)
  | must_postpone env (w,A) D (A.Marked(marked_P)) (z,C) = must_postpone env (w,A) D (Mark.data marked_P) (z,C)
  (* illegal, catch later *)
  | must_postpone env (w,A) D P (z,C) = false
                                     
(* must postpone if just one branch forces it *)
and must_postpone_branchesL env (w,A) D (x,nil) nil (z,C) = false
  | must_postpone_branchesL env (w,A) D (x,(l,Al)::choices) ((l',ext,P)::branches) (z,C) =
    if l = l'
    then must_postpone env (w,A) (TC.update_tp (x,Al) D) P (z,C)
         orelse must_postpone_branchesL env (w,A) D (x,choices) branches (z,C)
    else must_postpone_branchesL env (w,A) D (x,choices) ((l',ext,P)::branches) (z,C)
  | must_postpone_branchesL env (w,A) D (x,(l,Al)::choices) nil (z,C) = false

and must_postpone_branchesR env (w,A) D nil (z,nil) = false
  | must_postpone_branchesR env (w,A) D ((l,ext,P)::branches) (z,(l',Cl)::choices) =
    if l = l'
    then must_postpone env (w,A) D P (z,Cl)
         orelse must_postpone_branchesR env (w,A) D branches (z,choices)
    else must_postpone_branchesR env (w,A) D ((l,ext,P)::branches) (z,choices)
  | must_postpone_branchesR env (w,A) D nil (z,(l',Cl)::choices) = false

(* we insert 'assert' if may_postpone is false *)
fun may_postpone env (w,A) D (A.Id(z',y)) (z,C) = false (* cannot postpone past 'forward' *)
  | may_postpone env (w,A) D (A.Spawn(P as A.ExpName(y,f,es,xs),Q)) (z,C) =
    if List.exists (fn x => w = x) xs
    then (* argument to call: compare types *)
        let val Df = TC.synL env (y,f,es,xs)  (* x1:A1,...,xn:An as synthesized from f *)
            val A' = TC.lookup_context env w Df NONE (* A' is expanded; type for x expected by f *)
        in matching_qprefix env A A' end (* may postpone if the prefix matches, otherwise not *)
    else true (* can push into continuation *)
  | may_postpone env (w,A) D (A.Spawn(A.Marked(marked_P),Q)) (z,C) =
      may_postpone env (w,A) D (A.Spawn(Mark.data marked_P, Q)) (z,C)
  | may_postpone env (w,A) D (A.ExpName(y,f,es,xs)) (z,C) = (* x in xs *)
    let val D' = TC.synL env (y,f,es,xs)
        val A' = TC.lookup_context env w D' NONE (* A' is expanded; type for x expected by f *)
    in matching_qprefix env A A' end (* may postpone if the prefix matches, otherwise not *)

  (* structural interactions *)
  | may_postpone env (w,A) D (A.Lab(x,k,P)) (z,C) =
    if w = x then false else true
  | may_postpone env (w,A) D (A.Case(x,branches)) (z,C) =
    if w = x then false else true
  | may_postpone env (w,A) D (A.Send(x,y,P)) (z,C) =
    if w = x then false
    else if w = y
    then case TC.lookup_context env x D NONE
          of A.Lolli(A',B) => matching_qprefix env A A'
           | A.Tensor(A',B) => matching_qprefix env A A'
    else true
  | may_postpone env (w,A) D (A.Recv(x,y,P)) (z,C) =
    if w = x then false
    else true
  | may_postpone env (w,A) D (A.Wait(x,P)) (z,C) =
    if w = x then false
    else true
  | may_postpone env (w,A) D (A.Close(x)) (z,C) = false
  (* neutral *)
  | may_postpone env (w,A) D (A.Delay(t,P)) (z,C) = true
  | may_postpone env (w,A) D (A.Work(p,P)) (z,C) = true
  | may_postpone env (w,A) D (A.Marked(marked_P)) (z,C) = may_postpone env (w,A) D (Mark.data marked_P) (z,C)
  (* illegal, catch later *)
  | may_postpone env (w,A) D P (z,C) = true

*)


fun addR_assert env P (z,A.Exists(phi,C)) = A.Assert(z,phi,addR_assert env P (z,skip env C))
  | addR_assert env P (z,C) = P

fun addL_assert env (y,A.Forall(phi,A)) P = A.Assert(y,phi,addL_assert env (y,skip env A) P)
  | addL_assert env (y,A) P = P

fun addR_assume env P (z,A.Forall(phi,C)) = A.Assume (z,phi,addR_assume env P (z,skip env C))
  | addR_assume env P (z,C) = P

fun addL_assume env (y,A.Exists(phi,A)) P = A.Assume(y,phi,addL_assume env (y,skip env A) P)
  | addL_assume env (y,A) P = P

fun addLs_assert env D nil P = P
  | addLs_assert env D (x::xs) P =
    addLs_assert env D xs (addL_assert env (x, TC.lookup_context env x D NONE) P)

fun add_call env D (PQ as A.Spawn(P as A.ExpName(x,f,es,xs),Q)) =
    addLs_assert env D xs PQ
  | add_call env D (A.Spawn(A.Marked(marked_P),Q)) =
    add_call env D (A.Spawn(Mark.data marked_P,Q))



(* recon env A P C ext = P'
 * where P' contains assume, assert, imposs to match all quantified
 * type constructors in A and C
 * Assumes A |- P : C, approximately
 * P' is NOT guaranteed to be well-typed
 *
 * Insert 'assume' as soon as possible and 'assert' as late as possible
 * Reconstruction tracks the context and constraints, but does not
 * use them at present.  Checking them is postponed to type checking
 *)
fun recon env D P (z,C) ext =
  (*
  let 
      val D' = List.map (fn (x,A) => (x, skip env A)) D (* skip non-structural constructors *)
      val C' = skip env C (* skip non-structural constructors *)
  in
      recon'' env D' P (z,C') ext
  end
  *)
  (if false then TextIO.print (PP.pp_exp_prefix env P ^ " : "
                               ^ PP.pp_tpj_compact env D (R.Int(0)) (z,C) ^ "\n") else ()
  ; recon'' env D P (z,C) ext)

(*
(* recon' env A P C ext = P'
 * assumes A and C are structural or quantifiers
 * (see recon' for other info)
 *)
and recon' env ((x, A as A.Exists(phi,A'))::D) D' P (z,C) ext =
    if not (must_postpone env (x,A) (((x,A)::D) @ D') P (z,C))
    then A.Assume(x, phi, recon' env ((x,skip env A')::D) D' P (z,C) ext)
    else recon' env D ((x,A)::D') P (z,C) ext
  | recon' env nil D' P (z, C as A.Forall(phi,C')) ext =
    if not (must_postpone env (z,C) D' P (z,C))
    then A.Assume(z, phi, recon' env nil D' P (z,skip env C') ext)
    else recon'' env (List.rev D') P (z,C) ext
  | recon' env ((x,A as A.Forall(phi,A'))::D) D' P (z,C) ext =
    if not (may_postpone env (x,A) (((x,A)::D) @ D') P (z,C))
    then A.Assert(x, phi, recon' env ((x,skip env A')::D) D' P (z,C) ext)
    else recon' env D ((x,A)::D') P (z,C) ext
  | recon' env nil D' P (z, C as A.Exists(phi,C')) ext =
    if not (may_postpone env (z,C) D' P (z,C))
    then A.Assert(z, phi, recon' env nil D' P (z,skip env C') ext)
    else recon'' env D' P (z,C) ext
  | recon' env ((x,A)::D) D' P (z,C) ext = (* type must be structural *)
    recon' env D ((x,A)::D') P (z,C) ext
  | recon' env nil D' P (z,C) ext =
    recon'' env (List.rev D') P (z,C) ext (* reverse, to keep original order *)
*)
(* recon'' env A P C ext
 * assumes A, C are structural
 *)
(* judgmental constructs: id, cut, spawn *)
and recon_assumeR env D P (z,C) ext =
    let val P' = recon env D P (z,C) ext
    in addR_assume env P' (z,skip env C) end

and recon_assumeL env D (x,A) P (z,C) ext =
    let val P' = recon env D P (z,C) ext
    in addL_assume env (x,skip env A) P' end

and recon'' env D (P as A.Id(z',y)) (z,C) ext =
    let val P'  = addR_assert env P (z,skip env C)
        val P'' = addL_assert env (y, skip env (TC.lookup_context env y D ext)) P'
    in P'' end
  | recon'' env D (A.Spawn(P,Q)) (z,C) ext =
    (* obtain intermediate type B, to reconstruct both P and Q *)
    let val D' = TC.syn_call env D P ext
        val Q' = recon env D' Q (z,C) ext
        val PQ' = add_call env D (A.Spawn(P,Q'))
    in PQ' end

  | recon'' env D (P as A.ExpName(x,f,es,xs)) (z,C) ext =
    addLs_assert env D xs P

  (* begin cases for each action matching their type *)
  | recon'' env D (A.Lab(x,k,P)) (z,C) ext =
    if x = z
    then let val P' = recon_assumeR env D P (TC.syn_altR env (z,skipQ env C) k) ext
             val P'' = addR_assert env (A.Lab(x, k, P')) (z,skip env C)
         in P'' end
    else let val A = TC.lookup_context env x D ext
             val D' = TC.syn_altL env (TC.update_tp (x,skipQ env A) D) x k
             val P' = recon_assumeL env D' (x,TC.lookup_context env x D' ext) P (z,C) ext
             val P'' = addL_assert env (x,skip env A) P'
         in P'' end

  | recon'' env D (A.Case(x,branches)) (z,C) ext =
    if x = z
    then let val branches' = recon_branchesR env D branches (TC.syn_branchesR env (z,skipQ env C)) ext
             val P'' = addR_assert env (A.Case(x, branches')) (z, skip env C)
         in P'' end
    else let val A = TC.lookup_context env x D ext
             val choices' = TC.syn_branchesL env (TC.update_tp (x,skipQ env A) D) x
             val branches' = recon_branchesL env D choices' branches (z,C) ext
             val P'' = addL_assert env (x,skip env A) (A.Case(x,branches'))
         in P'' end

  | recon'' env D (A.Send(x,y,P)) (z,C) ext =
    if x = z
    then let val B = TC.lookup_context env y D ext
             val P' = recon_assumeR env (TC.remove_chan y D ext) P (TC.syn_sendR env (z,skipQ env C)) ext
             val P'' = addR_assert env (A.Send(x,y,P')) (z,skip env C)
             val P''' = addL_assert env (y,skip env B) P''
         in P''' end
    else let val A = TC.lookup_context env x D ext
             val B = TC.lookup_context env y D ext
             val D' = TC.remove_chan y (TC.syn_sendL env (TC.update_tp (x,skipQ env A) D) x) ext
             val P' = recon_assumeL env D' (x,TC.lookup_context env x D' ext) P (z,C) ext
             val P'' = addL_assert env (x,skip env A) (A.Send(x,y,P'))
             val P''' = addL_assert env (y,skip env B) P''
         in P''' end

  | recon'' env D (A.Recv(x,y,P)) (z,C) ext =
    if x = z
    then let val D' = TC.syn_recvR1 env D (z,skipQ env C) y
             val P' = recon_assumeR env D' P (TC.syn_recvR2 env (z,skipQ env C)) ext
             val P'' = P' (* recon_assumeL env D' (y,TC.lookup_context env y D' ext) P' (z,C) ext *)
             val P''' = addR_assert env (A.Recv(x,y,P'')) (z,skip env C)
         in P''' end
    else let val A = TC.lookup_context env x D ext
             val D' = TC.syn_recvL env (TC.update_tp (x,skipQ env A) D) x y
             val P' = recon_assumeL env D' (x,TC.lookup_context env x D' ext) P (z,C) ext
             val P'' = P' (* recon_assumeL env D' (y,TC.lookup_context env y D' ext) P' (z,C) ext *)
             val P''' = addL_assert env (x,skip env A) (A.Recv(x,y,P''))
         in P''' end

  | recon'' env D (P as A.Close(x)) (z,C) ext = (* x = z *)
    addR_assert env P (z,skip env C)
  | recon'' env D (A.Wait(x,P)) (z,C) ext = (* x <> z *)
    let val A = TC.lookup_context env x D ext
        val D' = TC.syn_waitL env (TC.update_tp (x,skipQ env A) D) x
        val P' = recon env D' P (z,C) ext
        val P'' = addL_assert env (x,skip env A) (A.Wait(x,P'))
    in P'' end
                                                         
  (* work, which is allowed before reconstruction *)
  | recon'' env D (A.Work(p,P')) zC ext =
    A.Work(p, recon env D P' zC ext)

  (* delay, which is allowed before reconstruction *)
  | recon'' env D (A.Delay(t,P')) zC ext =
    A.Delay(t, recon env D P' zC ext)
    
  | recon'' env D (A.Marked(marked_P)) zC ext =
    (* preserve marks for later error messages *)
    A.Marked(Mark.mark'(recon'' env D (Mark.data marked_P) zC (Mark.ext marked_P),
                        Mark.ext marked_P))

(* all other cases are impossible, by approximate reconstruction *)

and recon_branchesL env D (x,nil) nil (z,C) ext = nil
  | recon_branchesL env D (x,(l,A)::choices) ((l',ext',P)::branches) (z,C) ext =
    if l = l'
    then (l',ext',recon_assumeL env (TC.update_tp (x,A) D) (x,A) P (z,C) ext)
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
val recon = fn env => fn ctx => fn con => fn A => fn pot => fn P => fn C => fn ext => recon'' env A P C ext

end (* structure QRecon *)
