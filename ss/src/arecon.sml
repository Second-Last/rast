(* Approximate Reconstruction *)
(* Applied to implicit syntax, ignoring quantifiers, time, and work
 *
 * Ensures the structural types match so this does not need to
 * be checked later, except for internal and external choice, where
 * missing branches are permitted because they may be filled in by
 * quantifier reconstruction.  It also checks adherence to the restrictions
 * of implicit syntax, that is, no quantifier, ergometric, or temporal
 * interactions except for 'work' and 'delay' (which are inserted by
 * the cost model), and that all process variables are declared.
 *)

structure ARecon :> RECON =
struct

structure A = Ast
structure PP = PPrint
structure E = TpError
structure TC = TypeCheck
val ERROR = ErrorMsg.ERROR

(* direction of interaction for structural types
 * for the purpose of error messages
 *)
datatype dir = Left | Right
fun interacts P = case P of
    A.LabR _ => Right | A.CaseR _ => Right | A.CloseR => Right
    (* WhenR, NowR, PayR, GetR, assumeR, assertR, imposs not allowed *)
  | A.LabL _ => Left | A.CaseL _ => Left | A.WaitL _ => Left
    (* WhenL, NowL, PayL, GetL, assumeL, assertL, imposs not allowed *)
  | A.Marked(marked_exp) => interacts (Mark.data marked_exp)
    (* Cut, Id, ExpName not allowed *)

(* skipping over non-structural types, stopping at structural types *)
fun skip env (A.TpName(a,es)) = skip env (A.expd_tp env (a,es))
  | skip env (A.Exists(_,A')) = skip env A'
  | skip env (A.Forall(_,A')) = skip env A'
  | skip env (A.PayPot(_,A')) = skip env A'
  | skip env (A.GetPot(_,A')) = skip env A'
  | skip env (A.Next(_,A')) = skip env A'
  | skip env (A.Dia(A')) = skip env A'
  | skip env (A.Box(A')) = skip env A'
  | skip env A = A

fun check_declared env (f,es) ext =
    (case A.lookup_expdec env f
      of SOME(vs,con,(A,pot,C)) =>
         if List.length es = List.length vs
         then ()
         else ERROR ext ("process " ^ f
                         ^ " called with " ^ Int.toString (List.length es) ^ " indices "
                         ^ "but defined with " ^ Int.toString (List.length vs))
       | NONE => E.error_undeclared (f, ext))

(* recon env ctx con A P C ext = P' where P' == P
 * may raise ErrorMsg.error
 *
 * P' will be approximately well-typed which means all the structural
 * interactions match precisely, but there may be missing branches in
 * 'case' expressions for internal and external choice.  Also, except
 * for A.Work and A.Delay, only judgmental (cut, identity, and call)
 * and structural interactions are permitted.  Furthermore, process
 * variables must be declared.
 *)
fun recon env ctx con A P C ext =
    let 
        val A' = skip env A (* skip non-structural constructors *)
        val C' = skip env C (* skip non-structural constructors *)
    in
        recon' env ctx con A' P C' ext
    end

(* recon' env ctx con A P C ext
 * assumes A, C are structural
 * otherwise see recon
 *)
(* judgmental constructs: id, cut, spawn *)
and recon' env ctx con A (A.Id) C ext = A.Id
  | recon' env ctx con A (A.Cut(P,pot,B,Q)) C ext =
    let val P' = recon env ctx con A P B ext
        val Q' = recon env ctx con B Q C ext
    in A.Cut(P',pot,B,Q') end
  | recon' env ctx con A (A.Spawn(P,Q)) C ext =
    let val (A', pot', P', B) = TC.syn_call env P ext
    in A.Spawn(P', recon env ctx con B Q C ext) end
  | recon' env ctx con A (P as A.ExpName(f,es)) C ext =
    ( check_declared env (f,es) ext
    ; P )

  (* begin cases for each action matching their type *)
  | recon' env ctx con A (A.LabR(k,P)) (C as A.Plus(choices)) ext =
    (case A.lookup_choice choices k
      of SOME(Ck) => A.LabR(k, recon env ctx con A P Ck ext)
       | NONE => E.error_label_invalid env (k, C, ext))
  | recon' env ctx con A (A.CaseR(branches)) (A.With(choices)) ext =
    let val branches' = recon_branchesR env ctx con A branches choices ext
    in A.CaseR(branches') end

  | recon' env ctx con (A as A.With(choices)) (A.LabL(k,Q)) C ext =
    (case A.lookup_choice choices k
      of SOME(Ak) => A.LabL(k, recon env ctx con Ak Q C ext)
       | NONE => E.error_label_invalid env (k, A, ext))
  | recon' env ctx con (A.Plus(choices)) (A.CaseL(branches)) C ext =
    let val branches' = recon_branchesL env ctx con choices branches C ext
    in A.CaseL(branches') end
  
  | recon' env ctx con (A.Dot) (A.CloseR) (A.One) ext = A.CloseR
  | recon' env ctx con (A.One) (A.WaitL(Q)) C ext =
    let val Q' = recon env ctx con A.Dot Q C ext
    in A.WaitL(Q') end

  (* work, which is allowed before reconstruction *)
  | recon' env ctx con A (A.Work(p,P')) C ext =
    A.Work(p, recon env ctx con A P' C ext)

  (* delay, which is allowed before reconstruction *)
  | recon' env ctx con A (A.Delay(t,P')) C ext =
    A.Delay(t, recon env ctx con A P' C ext)

  (* should not be allowed before reconstruction *)
  (* this would be with disjunctive patterns or a separate function *)
  | recon' env ctx con A (P as A.AssertR _) C ext = E.error_implicit (P,ext)
  | recon' env ctx con A (P as A.AssumeL _) C ext = E.error_implicit (P,ext)
  | recon' env ctx con A (P as A.AssumeR _) C ext = E.error_implicit (P,ext)
  | recon' env ctx con A (P as A.AssertL _) C ext = E.error_implicit (P,ext)
  | recon' env ctx con A (P as A.Imposs)    C ext = E.error_implicit (P,ext)

  | recon' env ctx con A (P as A.PayR _) C ext = E.error_implicit (P,ext)
  | recon' env ctx con A (P as A.GetL _) C ext = E.error_implicit (P,ext)
  | recon' env ctx con A (P as A.GetR _) C ext = E.error_implicit (P,ext)
  | recon' env ctx con A (P as A.PayL _) C ext = E.error_implicit (P,ext)

  | recon' env ctx con A (P as A.NowR _) C ext = E.error_implicit (P,ext)
  | recon' env ctx con A (P as A.WhenL _) C ext = E.error_implicit (P,ext)
  | recon' env ctx con A (P as A.WhenR _) C ext = E.error_implicit (P,ext)
  | recon' env ctx con A (P as A.NowL _) C ext = E.error_implicit (P,ext)

  (* traverse, but preserve, marks for downstream error messages *)
  | recon' env A ctx con (A.Marked(marked_P)) C ext =
    (* preserve marks for later error messages *)
    A.Marked(Mark.mark'(recon env A ctx con (Mark.data marked_P) C (Mark.ext marked_P),
                        Mark.ext marked_P))

  (* remaining cases, where process attempts to interact *)
  | recon' env ctx con A P C ext =
    (case (A, interacts P, C)
      of (* interacting right *)
         (A, Right, C) => ERROR ext ("does not match right type " ^ PP.pp_tp_compact env C)
         (* interacting left *)
       | (A, Left, C) => ERROR ext ("does not match left type " ^ PP.pp_tp_compact env A))

(* branchesL for case handling internal choice *)
(* tolerate missing branches *)
and recon_branchesL env ctx con nil nil C ext = nil
  | recon_branchesL env ctx con ((l,A)::choices) ((l',ext',P)::branches) C ext =
    if l = l'
    then (l',ext',recon env ctx con A P C ext)::(recon_branchesL env ctx con choices branches C ext)
    else recon_branchesL env ctx con choices ((l',ext',P)::branches) C ext (* alternative l missing; ignore *)
  | recon_branchesL env ctx con ((l,A)::choices) nil C ext = (* alternative l missing; ignore *)
    recon_branchesL env ctx con choices nil C ext
  | recon_branchesL env ctx con nil ((l', ext', P)::_) C ext =
    (* l' not part of the type *)
    E.error_label_missing_alt (l',ext')

(* branchesR for case handling external choice *)
(* tolerate missing branches *)
and recon_branchesR env ctx con A nil nil ext = nil
  | recon_branchesR env ctx con A ((l,ext',P)::branches) ((l',C)::choices) ext =
    if l = l'
    then (l',ext',recon env ctx con A P C ext)::(recon_branchesR env ctx con A branches choices ext)
    else recon_branchesR env ctx con A ((l,ext',P)::branches) choices ext (* alternative l' missing; ignore *)
  | recon_branchesR env ctx con A ((l,ext',P)::_) nil ext =
    (* l not part of the type *)
    E.error_label_missing_alt (l, ext')
  | recon_branchesR env ctx con A nil ((l',C)::choices) ext = (* alternative l' missing; ignore *)
    recon_branchesR env ctx con A nil choices ext

(* external interface: ignore potential *)
val recon = fn env => fn ctx => fn con => fn A => fn pot => fn P => fn C => fn ext =>
            recon env ctx con A P C ext

end (* structure ARecon *)
