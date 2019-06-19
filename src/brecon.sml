(* Branch Reconstruction *)
(* Applies to implicit syntax, after approximate reconstruction
 *
 * Fills in imposs constructs for missing branches, establishing
 * the invariant that the branches match the alternatives exactly.
 *
 * This should only be called if quantifier or time/quantifier
 * reconstruction follows.
 *)

structure BRecon :> RECON =
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
    (* (l, NONE, A.ImpossL(phi)) *)
    if not (C.contradictory ctx con phi)
    then error_label_sat_con ctx con phi (l, ext')
    else (l, NONE, A.Imposs) (* only insert A.Imposs; reconstruction will insert AssumeL *)
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
    (* (l, NONE, A.ImpossR(phi)) *)
    if not (C.contradictory ctx con phi)
    then error_label_sat_con ctx con phi (l, ext')
    else (l, NONE, A.Imposs)
  | impossR_branch env ctx con (l,A.TpName(a,es)) l' ext' =
    impossR_branch env ctx con (l,A.expd_tp env (a,es)) l' ext'
  | impossR_branch env ctx con (l,C) NONE ext' = E.error_label_missing_branch (l,ext')
  | impossR_branch env ctx con (l,C) (SOME(l')) ext' = E.error_label_mismatch (l, l', ext')

(* recon env ctx con A P C ext = P'
 * where P' contains imposs to match all missing branches
 * if there is a matching constraint
 * Checking the constraint is postponed to type checking
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
and recon' env ctx con (A.Exists(phi,A')) P C ext =
    recon env ctx (R.And(con,phi)) A' P C ext
  | recon' env ctx con A P (A.Forall(phi,C')) ext =
    recon env ctx (R.And(con,phi)) A P C' ext
  | recon' env ctx con (A.Forall(phi,A')) P C ext =
    recon env ctx (R.And(con,phi)) A' P C ext
  | recon' env ctx con A P (A.Exists(phi,C')) ext =
    recon env ctx (R.And(con,phi)) A P C' ext
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

end (* structure BRecon *)
