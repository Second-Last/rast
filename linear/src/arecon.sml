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

(* skipping over non-structural types, stopping at structural types *)
fun skip env (A as A.TpName(a,es)) = skip env (TC.expd env A)
  | skip env (A.Exists(_,A')) = skip env A'
  | skip env (A.Forall(_,A')) = skip env A'
  | skip env (A.PayPot(_,A')) = skip env A'
  | skip env (A.GetPot(_,A')) = skip env A'
  | skip env (A.Next(_,A')) = skip env A'
  | skip env (A.Dia(A')) = skip env A'
  | skip env (A.Box(A')) = skip env A'
  | skip env A = A

fun lookup_skip env x D ext = skip env (TC.lookup_context env x D ext)

fun check_declared env (f,es) ext =
    (case A.lookup_expdec env f
      of SOME(vs,con,(A,pot,C)) =>
         if List.length es = List.length vs
         then ()
         else ERROR ext ("process " ^ f ^ " called with wrong number of indices:\n"
                         ^ "expected " ^ Int.toString (List.length vs)
                         ^ "found    " ^ Int.toString (List.length es))
       | NONE => E.error_undeclared (f, ext))

fun pp_channels (nil) = ""
  | pp_channels ((x,A)::nil) = x
  | pp_channels ((x,A)::D) = x ^ " " ^ pp_channels D

fun error_mismatch env x A_expected found ext =
    ERROR ext ("type_mismatch for channel " ^ x ^ ":\n"
               ^ "expected exp of type " ^ PP.pp_tp_compact env A_expected
               ^ "found exp of type    " ^ found)

(* recon env A P C ext = P' where P' == P
 * may raise ErrorMsg.error
 *
 * P' will be approximately well-typed which means all the structural
 * interactions match precisely, but there may be missing branches in
 * 'case' expressions for internal and external choice.  Also, except
 * for A.Work and A.Delay, only judgmental (cut, identity, and call)
 * and structural interactions are permitted.  Furthermore, process
 * variables must be declared.
 *)
fun recon env D P zC ext =
    (* opportunity for tracing here *)
    recon' env D P zC ext

and plusR env D (A.Lab(x,k,P)) (z,C as A.Plus(choices)) ext = (* x = z *)
    (case A.lookup_choice choices k
      of SOME(Ck) => A.Lab(x,k,recon env D P (z,Ck) ext)
       | NONE => E.error_label_invalid env (k, C, ext))
  | plusR env D (A.Lab(x,k,P)) (z,C) ext = (* x = z *)
    error_mismatch env x C ("+{" ^ k ^ ":_, ...}") ext

and withL env D (A as A.With(choices)) (A.Lab(x,k,P)) zC ext =
    (case A.lookup_choice choices k
      of SOME(Ak) => A.Lab(x,k,recon env (TC.update_tp (x,Ak) D) P zC ext)
       | NONE => E.error_label_invalid env (k, A, ext))
  | withL env D A (A.Lab(x,k,P)) zC ext =
    error_mismatch env x A ("&{" ^ k ^ ":_, ...}") ext

and withR env D (A.Case(x,branches)) (z,A.With(choices)) ext = (* x = z *)
    A.Case(x,recon_branchesR env D branches (z,choices) ext)
  | withR env D (A.Case(x,branches)) (z,C) ext =
    error_mismatch env x C ("&{...}") ext

(* branchesR for case handling external choice *)
(* tolerate missing branches *)
and recon_branchesR env D nil (z,nil) ext = nil
  | recon_branchesR env D ((l,ext',P)::branches) (z,(l',C)::choices) ext =
    if l = l'
    then (l',ext',recon env D P (z,C) ext)::(recon_branchesR env D branches (z,choices) ext)
    else recon_branchesR env D ((l,ext',P)::branches) (z,choices) ext (* alternative l' missing; ignore *)
  | recon_branchesR env D ((l,ext',P)::_) (z,nil) ext =
    (* l not part of the type *)
    E.error_label_missing_alt (l, ext')
  | recon_branchesR env D nil (z, (l',C)::choices) ext = (* alternative l' missing; ignore *)
    recon_branchesR env D nil (z, choices) ext

and plusL env D (A.Plus(choices)) (A.Case(x,branches)) zC ext = (* z <> x *)
    A.Case(x,recon_branchesL env D (x,choices) branches zC ext)
  | plusL env D A (A.Case(x,branches)) zC ext =
    error_mismatch env x A ("+{...}") ext

(* branchesL for case handling internal choice *)
(* tolerate missing branches *)
and recon_branchesL env D (x,nil) nil zC ext = nil
  | recon_branchesL env D (x,(l,A)::choices) ((l',ext',P)::branches) zC ext =
    if l = l'
    then (l',ext',recon env (TC.update_tp (x,A) D) P zC ext)::(recon_branchesL env D (x,choices) branches zC ext)
    else recon_branchesL env D (x,choices) ((l',ext',P)::branches) zC ext (* alternative l missing; ignore *)
  | recon_branchesL env D (x,(l,A)::choices) nil zC ext = (* alternative l missing; ignore *)
    recon_branchesL env D (x,choices) nil zC ext
  | recon_branchesL env D (x,nil) ((l', ext', P)::_) (z,C) ext =
    (* l' not part of the type *)
    E.error_label_missing_alt (l',ext')

and tensorR env D (A.Send(x,w,P)) (z,A.Tensor(A,B)) ext = (* x = z *)
    (* do not check type equality here, just remove w *)
    A.Send(x,w,recon env (TC.remove_chan w D ext) P (z,B) ext)
  | tensorR env D (A.Send(x,w,P)) (z,C) ext =
    error_mismatch env x C "(_ * _)" ext

and lolliL env D (A.Lolli(A,B)) (A.Send(x,w,P)) zC ext = (* x <> z *)
    A.Send(x,w,recon env (TC.update_tp (x,B) (TC.remove_chan w D ext)) P zC ext)
  | lolliL env D A (A.Send(x,w,P)) zC ext =
    error_mismatch env x A "(_ -o _)" ext

and lolliR env D (A.Recv(x,y,P)) (z,A.Lolli(A,B)) ext = (* x = z *)
    A.Recv(x,y,recon env ((y,A)::D) P (z,B) ext)        (* check if y is fresh here? *)
  | lolliR env D (A.Recv(x,y,P)) (z,C) ext =
    error_mismatch env x C "(_ -o _)" ext

and tensorL env D (A.Tensor(A,B)) (A.Recv(x,y,P)) zC ext =
    A.Recv(x,y,recon env ((y,A)::TC.update_tp (x,B) D) P zC ext) (* check if y is fresh here? *)
  | tensorL env D A (A.Recv(x,y,P)) zC ext =
    error_mismatch env x A "(_ * _)" ext

and oneR env D (A.Close(x)) (z,A.One) ext = (* x = z *)
    let val () = case D
                  of nil => ()
                   | _ => ERROR ext ("unconsumed channels " ^ pp_channels D ^ " at close")
    in A.Close(x) end
  | oneR env D (A.Close(x)) (z,C) ext =
    error_mismatch env x C "1" ext

and oneL env D (A.One) (A.Wait(x,P)) zC ext = (* x <> z *)
    A.Wait(x,recon env (TC.remove_chan x D ext) P zC ext)
  | oneL env D A (A.Wait(x,P)) zC ext =
    error_mismatch env x A "1" ext

and existsNatR env D (A.SendNat(x,e,P)) (z,A.ExistsNat(v,C)) ext =
    A.SendNat(x,e,recon env D P (z,C) ext) (* Q: any reason to substitute here? *)
  | existsNatR env D (A.SendNat(x,e,P)) (z,C) ext =
    error_mismatch env x C "?v._" ext
and forallNatL env D (A.ForallNat(v,A)) (A.SendNat(x,e,P)) zC ext = (* Q: any reason to substitute here? *)
    A.SendNat(x,e,recon env (TC.update_tp (x,A) D) P zC ext)
  | forallNatL env D A (A.SendNat(x,e,P)) zC ext =
    error_mismatch env x A "!v._" ext
and forallNatR env D (A.RecvNat(x,v,P)) (z,A.ForallNat(v',C)) ext = (* Q: any reason to alpha-convert here? *)
    A.RecvNat(x,v,recon env D P (z,C) ext)
  | forallNatR env D (A.RecvNat(x,v,P)) (z,C) ext =
    error_mismatch env x C "!v._" ext
and existsNatL env D (A.ExistsNat(v',A)) (A.RecvNat(x,v,P)) zC ext = (* Q: any reason to alpha-convert here? *)
    A.RecvNat(x,v,recon env (TC.update_tp (x,A) D) P zC ext)
  | existsNatL env D A (A.RecvNat(x,v,P)) zC ext =
    error_mismatch env x A "?v._" ext

(* recon' env A P C ext
 * assumes A, C are structural
 * otherwise see recon
 *)
(* judgmental constructs: id, cut, spawn *)
and recon' env D (P as A.Id(x,y)) (z,C) ext =
    let val () = if x = z then ()
                 else ERROR ext ("channel mismatch in forward:\n"
                                 ^ "expected " ^ z ^ "\n"
                                 ^ "found    " ^ x)
        val D' = TC.remove_chan y D ext
        val () = case D'
                  of nil => ()
                   | _ => ERROR ext ("unclosed channels " ^ pp_channels D' ^ " at forward")
    in P end
  | recon' env D (A.Spawn(P as A.ExpName(x,f,es,xs),Q)) zC ext =
    let val D' = TC.syn_call env D P ext
    in A.Spawn(P, recon env D' Q zC ext) end
  | recon' env D (P as A.ExpName(x,f,es,xs)) (z,C) ext =
    let val () = if x = z then ()
                 else ERROR ext ("channel mismatch in tail call:\n"
                                 ^ "expected " ^ z ^ "\n"
                                 ^ "found    " ^ x)
        val D' = TC.remove_chans xs D ext
        val () = case D'
                  of nil => ()
                   | _ => ERROR ext ("unclosed channels " ^ pp_channels D' ^ " at tail call")
        val () = check_declared env (f,es) ext
    in P end

  (* begin cases for each action matching their type *)
  | recon' env D (P as A.Lab(x,k,P')) (z,C) ext =
    if x = z
    then plusR env D P (z,skip env C) ext
    else withL env D (lookup_skip env x D ext) P (z,C) ext

  | recon' env D (P as A.Case(x,branches)) (z,C) ext =
    if x = z
    then withR env D P (z,skip env C) ext
    else plusL env D (lookup_skip env x D ext) P (z,C) ext

  | recon' env D (P as A.Send(x,w,P')) (z,C) ext =
    if x = z
    then tensorR env D P (z,skip env C) ext
    else lolliL env D (lookup_skip env x D ext) P (z,C) ext

  | recon' env D (P as A.Recv(x,y,P')) (z,C) ext =
    if x = z
    then lolliR env D P (z,skip env C) ext
    else tensorL env D (lookup_skip env x D ext) P (z,C) ext
         
  | recon' env D (P as A.Close(x)) (z,C) ext =
    if x = z
    then oneR env D P (z,skip env C) ext
    else ERROR ext ("channel mismatch at close:\n"
                    ^ "expected " ^ z ^ "\n"
                    ^ "found    " ^ x)

  | recon' env D (P as A.Wait(x,P')) (z,C) ext =
    if x = z
    then ERROR ext ("cannot wait on provided channel " ^ z)
    else oneL env D (lookup_skip env x D ext) P (z,C) ext

  | recon' env D (P as A.SendNat(x,e,P')) (z,C) ext =
    if x = z
    then existsNatR env D P (z, skip env C) ext
    else forallNatL env D (lookup_skip env x D ext) P (z,C) ext

  | recon' env D (P as A.RecvNat(x,v,P')) (z,C) ext =
    if x = z
    then forallNatR env D P (z, skip env C) ext
    else existsNatL env D (lookup_skip env x D ext) P (z,C) ext

  (* work, which is allowed before reconstruction *)
  | recon' env D (A.Work(p,P')) zC ext =
    A.Work(p, recon env D P' zC ext)

  (* delay, which is allowed before reconstruction *)
  | recon' env D (A.Delay(t,P')) zC ext =
    A.Delay(t, recon env D P' zC ext)

  (* should not be allowed before reconstruction *)
  (* this would be with disjunctive patterns or a separate function *)
  | recon' env D (P as A.Assert _) zC ext = E.error_implicit (P,ext)
  | recon' env D (P as A.Assume _) zC ext = E.error_implicit (P,ext)
  | recon' env D (P as A.Imposs)   zC ext = E.error_implicit (P,ext)

  | recon' env D (P as A.Pay _) zC ext = E.error_implicit (P,ext)
  | recon' env D (P as A.Get _) zC ext = E.error_implicit (P,ext)

  | recon' env D (P as A.Now _) zC ext = E.error_implicit (P,ext)
  | recon' env D (P as A.When _) zC ext = E.error_implicit (P,ext)

  (* traverse, but preserve, marks for downstream error messages *)
  | recon' env D (A.Marked(marked_P)) zC ext =
    (* preserve marks for later error messages *)
    A.Marked(Mark.mark'(recon env D (Mark.data marked_P) zC (Mark.ext marked_P),
                        Mark.ext marked_P))

fun recon_top env ctx con D pot P zC ext =
    recon env D P zC ext

(* external interface: ignore potential *)
fun recon env ctx con D pot P zC ext =
    recon_top env ctx con D pot P zC ext

end (* structure ARecon *)
