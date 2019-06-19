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

(* begin copied from typecheck.sml *)
fun error_label_sat_con ctx con phi (l, ext) =
    ERROR ext ("label " ^ l ^ " does not appear among the branches\n but " ^ C.pp_jsat con phi)
(* end copied from typecheck.sml *)

(* skipping over non-structural types, stopping at quantifiers or
 * structural types *)
fun skip env (A.PayPot(_,A')) = skip env A'
  | skip env (A.GetPot(_,A')) = skip env A'
  | skip env (A.Next(_,A')) = skip env A'
  | skip env (A.Dia(A')) = skip env A'
  | skip env (A.Box(A')) = skip env A'
  | skip env (A.TpName(a,es)) = skip env (A.expd_tp env (a,es))
  | skip env A = A

(* impossL_branch env ctx con (l,A) l_opt = ImpossL(phi)
 * if A = Exists(phi,A'), raises an exception otherwise
 * l_opt is label of the next branch if one (for error messages)
 * Checking unsat(phi) is postponed to type checking
 *)
fun impossL_branch env ctx con (l,A.Exists(phi,A')) _ ext' =
    (l, NONE, A.AssumeL(phi,A.Imposs))
    (* 
      if not (C.contradictory ctx con phi)
      then error_label_sat_con ctx con phi (l, ext')
      else (l, NONE, A.AssumeL(phi,A.Imposs))
     *)
  | impossL_branch env ctx con (l,A.TpName(a,es)) l_opt ext' =
    impossL_branch env ctx con (l,A.expd_tp env (a,es)) l_opt ext'
  | impossL_branch env ctx con (l,A) NONE ext' = E.error_label_missing_branch (l,ext')
  | impossL_branch env ctx con (l,A) (SOME(l')) ext' = E.error_label_mismatch (l, l', ext')

(* impossR_branch env ctx con (l,A) = ImpossR(phi)
 * if A = Forall(phi,A'), raises an exception otherwise
 * l_opt is label of the next branch if one (for error messages)
 * Checking unsat(phi) is postponed to type checking
 *)
fun impossR_branch env ctx con (l,A.Forall(phi,C')) l' ext' =
    (l, NONE, A.AssumeR(phi,A.Imposs))
    (*
      if not (C.contradictory ctx con phi)
      then error_label_sat_con ctx con phi (l, ext')
      else (l, NONE, A.AssumeR(phi,Imposs))
     *)
  | impossR_branch env ctx con (l,A.TpName(a,es)) l' ext' =
    impossR_branch env ctx con (l,A.expd_tp env (a,es)) l' ext'
  | impossR_branch env ctx con (l,C) NONE ext' = E.error_label_missing_branch (l,ext')
  | impossR_branch env ctx con (l,C) (SOME(l')) ext' = E.error_label_mismatch (l, l', ext')

(* matching_qprefix env A B, where A = !{phi}. A' or A = ?{phi}. A' initially *)
fun matching_qprefix env A B = matching_qprefix' env (skip env A) (skip env B)
and matching_qprefix' env (A.Exists(phi,A')) (A.Exists(psi,B')) = true
  | matching_qprefix' env (A.Forall(phi,A')) (A.Forall(psi,B')) = true
  | matching_qprefix' env A B = false

(* we insert assumeL if must_postponeL is false *)
fun must_postponeL env A' (A.Id) = false (* need not postpone *)
  | must_postponeL env A' (A.Cut(P,lpot,B,Q)) = must_postponeL env A' P
  | must_postponeL env A' (A.Spawn(P,Q)) = must_postponeL env A' P
  | must_postponeL env A' (A.ExpName(f,es)) =
    (* synth left type; more precise than needed *)
    matching_qprefix env A' (TC.synL env (f,es))
  (* left interactions *)
  | must_postponeL env A' (A.LabL _) = false
  | must_postponeL env A' (A.CaseL _) = false
  | must_postponeL env A' (A.WaitL _) = false
  (* right interactions *)
  | must_postponeL env A' (A.LabR(_, P))  = must_postponeL env A' P
  | must_postponeL env A' (A.CaseR(branches)) = must_postpone_branchesL env A' branches
  | must_postponeL env A' (A.CloseR) = false
  (* neutral *)
  | must_postponeL env A' (A.Delay(t,P)) = must_postponeL env A' P
  | must_postponeL env A' (A.Work(p,P)) = must_postponeL env A' P
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
    (* synth right types; more precise than needed *)
    matching_qprefix env (TC.synR env (f,es)) C'
  (* right interactions *)
  | must_postponeR env (A.LabR _) C' = false
  | must_postponeR env (A.CaseR _) C' = false
  | must_postponeR env (A.CloseR) C' = false
  (* left interactions *)
  | must_postponeR env (A.LabL(_, P)) C' = must_postponeR env P C'
  | must_postponeR env (A.CaseL(branches)) C' = must_postpone_branchesR env branches C'
  | must_postponeR env (A.WaitL(P)) C' = must_postponeR env P C'
  (* neutral *)
  | must_postponeR env (A.Delay(t,P)) C' = must_postponeR env P C'
  | must_postponeR env (A.Work(p,P)) C' = must_postponeR env P C'
  | must_postponeR env (A.Marked(marked_P)) C' = must_postponeR env (Mark.data marked_P) C'
  (* illegal, catch later *)
  | must_postponeR env P C' = false
(* must postpoint if just one branch forces it *)
and must_postpone_branchesR env nil C' = false
  | must_postpone_branchesR env ((l,_,P)::branches) C' =
    must_postponeR env P C' orelse must_postpone_branchesR env branches C'

(* we insert assertL if may_postponeL is false *)
fun may_postponeL env A' (A.Id) = false (* cannot postpone past 'forward' *)
  | may_postponeL env A' (A.Cut(P,lpot,B,Q)) = true
  | may_postponeL env A' (A.Spawn(P,Q)) = may_postponeL env A' P
  | may_postponeL env A' (A.ExpName(f,es)) =
    (* synth left type, more precise than needed *)
    matching_qprefix env A' (TC.synL env (f,es))
  (* left interactions *)
  | may_postponeL env A' (A.LabL _) = false
  | may_postponeL env A' (A.CaseL _) = false
  | may_postponeL env A' (A.WaitL _) = false
  (* right interactions *)
  | may_postponeL env A' (A.LabR(_, P))  = true
  | may_postponeL env A' (A.CaseR(branches)) = true (* push into each branch *)
  | may_postponeL env A' (A.CloseR) = false (* can not postpone past closeR *)
  (* neutral *)
  | may_postponeL env A' (A.Delay(t,P)) = true
  | may_postponeL env A' (A.Work(p,P)) = true
  | may_postponeL env A' (A.Marked(marked_P)) = may_postponeL env A' (Mark.data marked_P)
  (* illegal, catch later *)
  | may_postponeL env A' P = true (* default is 'true' *)

(* we insert assertR if may_postponeR is false *)
fun may_postponeR env (A.Id) C' = false (* cannot postpone *)
  | may_postponeR env (A.Cut(P, _, _, Q)) C' = true
  | may_postponeR env (A.Spawn(P,Q)) C' = true
  | may_postponeR env (A.ExpName(f,es)) C' =
    (* synth right type; more precise than needed *)
    matching_qprefix env (TC.synR env (f,es)) C'
  (* right interactions *)
  | may_postponeR env (A.LabR _) C' = false
  | may_postponeR env (A.CaseR _) C' = false
  | may_postponeR env (A.CloseR) C' = false
  (* left interactions *)
  | may_postponeR env (A.LabL(_, P)) C' = true
  | may_postponeR env (A.CaseL(branches)) C' = true
  | may_postponeR env (A.WaitL(P)) C' = true
  (* neutral *)
  | may_postponeR env (A.Delay(t,P)) C' = true
  | may_postponeR env (A.Work(p,P)) C' = true
  | may_postponeR env (A.Marked(marked_P)) C' = may_postponeR env (Mark.data marked_P) C'
  (* illegal, catch later *)
  | may_postponeR env P C' = true (* default is 'true' *)

(* recon env ctx con A P C ext = P'
 * where P' contains assume, assert, imposs to match all quantified
 * type constructors in A and C
 * Assumes A |- P : C, approximately
 * P' is NOT guaranteed to be well-typed
 *
 * Insert 'assume' as soon as possible and 'assert' as late as possible
 * Reconstruction tracks the context and constraints, but does not
 * use them at present.  Checking them is postponed to type checking
 *)
fun recon env ctx con A P C ext =
    let 
        val A' = skip env A (* skip non-structural constructors *)
        val C' = skip env C (* skip non-structural constructors *)
    in
        recon' env ctx con A' P C' ext
    end

(* recon' env ctx con A P C ext = P'
 * assumes A and C are structural or quantifiers
 * (see recon' for other info)
 *)
and recon' env ctx con (A as A.Exists(phi,A')) P C ext =
    if not (must_postponeL env A P)
    then A.AssumeL(phi, recon env ctx (R.And(con,phi)) A' P C ext)
    else recon'' env ctx con A P C ext
  | recon' env ctx con A P (C as A.Forall(phi,C')) ext =
    if not (must_postponeR env P C)
    then A.AssumeR(phi, recon env ctx (R.And(con,phi)) A P C' ext)
    else recon'' env ctx con A P C ext
  | recon' env ctx con (A as A.Forall(phi,A')) P C ext =
    if not (may_postponeL env A P)
    then A.AssertL(phi, recon env ctx (R.And(con,phi)) A' P C ext)
    else recon'' env ctx con A P C ext
  | recon' env ctx con A P (C as A.Exists(phi,C')) ext =
    if not (may_postponeR env P C)
    then A.AssertR(phi, recon env ctx (R.And(con,phi)) A P C' ext)
    else recon'' env ctx con A P C ext
  | recon' env ctx con A P C ext = (* type must be structural *)
    recon'' env ctx con A P C ext

(* recon'' env ctx con A P C ext
 * assumes A, C are structural
 *)
(* judgmental constructs: id, cut, spawn *)
and recon'' env ctx con A (A.Id) C ext = A.Id
  | recon'' env ctx con A (A.Cut(P,pot,B,Q)) C ext =
    let val P' = recon env ctx con A P B ext
        val Q' = recon env ctx con B Q C ext
    in A.Cut(P',pot,B,Q') end
  | recon'' env ctx con A (A.Spawn(P,Q)) C ext =
    (* obtain intermediate type B, to reconstruct both P and Q *)
    let val (A', pot', P', B) = TC.syn_call env P ext
    in A.Spawn(P', recon env ctx con B Q C ext) end
  | recon'' env ctx con A (P as A.ExpName(f,es)) C ext =
    P

  (* begin cases for each action matching their type *)
  | recon'' env ctx con A (A.LabR(k,P)) (C as A.Plus(choices)) ext =
    A.LabR(k, recon env ctx con A P (TC.syn_alt env choices k) ext)
  | recon'' env ctx con A (A.CaseR(branches)) (A.With(choices)) ext =
    let val branches' = recon_branchesR env ctx con A branches choices ext
    in A.CaseR(branches') end
  | recon'' env ctx con (A.Dot) (A.CloseR) (A.One) ext = A.CloseR
                                                         
  | recon'' env ctx con (A as A.With(choices)) (A.LabL(k,Q)) C ext =
    A.LabL(k, recon env ctx con (TC.syn_alt env choices k) Q C ext)
  | recon'' env ctx con (A.Plus(choices)) (A.CaseL(branches)) C ext =
    let val branches' = recon_branchesL env ctx con choices branches C ext
    in A.CaseL(branches') end
  | recon'' env ctx con (A.One) (A.WaitL(Q)) C ext =
    let val Q' = recon env ctx con A.Dot Q C ext
    in A.WaitL(Q') end

  (* work, which is allowed before reconstruction *)
  | recon'' env ctx con A (A.Work(p,P')) C ext =
    A.Work(p, recon env ctx con A P' C ext)

  (* delay, which is allowed before reconstruction *)
  | recon'' env ctx con A (A.Delay(t,P')) C ext =
    A.Delay(t, recon env ctx con A P' C ext)
    
  | recon'' env A ctx con (A.Marked(marked_P)) C ext =
    (* preserve marks for later error messages *)
    A.Marked(Mark.mark'(recon'' env A ctx con (Mark.data marked_P) C (Mark.ext marked_P),
                        Mark.ext marked_P))

(* all other cases are impossible, by approximate reconstruction *)
  
and recon_branchesL env ctx con nil nil C ext = nil
  | recon_branchesL env ctx con ((l,A)::choices) ((l',ext',P)::branches) C ext =
    if l = l'
    then (l',ext',recon env ctx con A P C ext)
         ::(recon_branchesL env ctx con choices branches C ext)
    else (impossL_branch env ctx con (l,A) (SOME(l')) ext')
         ::(recon_branchesL env ctx con choices ((l',ext',P)::branches) C ext)
  | recon_branchesL env ctx con ((l,A)::choices) nil C ext =
    (impossL_branch env ctx con (l,A) NONE ext)
    ::(recon_branchesL env ctx con choices nil C ext)

and recon_branchesR env ctx con A nil nil ext = nil
  | recon_branchesR env ctx con A ((l,ext',P)::branches) ((l',C)::choices) ext =
    if l = l'
    then (l',ext',recon env ctx con A P C ext)
         ::(recon_branchesR env ctx con A branches choices ext)
    else (impossR_branch env ctx con (l',C) (SOME(l)) ext')
         ::(recon_branchesR env ctx con A ((l,ext',P)::branches) choices ext)
  | recon_branchesR env ctx con A nil ((l',C)::choices) ext =
    (impossR_branch env ctx con (l',C) NONE ext)
    ::(recon_branchesR env ctx con A nil choices ext)

(* external interface: ignore potential *)
val recon = fn env => fn ctx => fn con => fn A => fn pot => fn P => fn C => fn ext => recon env ctx con A P C ext

end (* structure QRecon *)
