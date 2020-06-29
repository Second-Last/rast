(* Type Checking *)
(* Authors: Ankush Das <ankushd@cs.cmu.edu>
 *          Frank Pfenning <fp@cs.cmu.edu>
 *)

(*
 * Use the syntax-directed rules to check the types and
 * raises ErrorMsg.Error if an error is discovered.  This
 * should be applied directly to explicit syntax or after
 * reconstruction with implicit syntax.
 *)

signature TYPE_CHECK =
sig
    (* check_exp trace env ctx con D pot P (z,C) ext = ()
     * checks that D |- P :: (z : C) with potential pot
     * raises ErrorMsg.error if not
     *
     * trace = true means print some tracinng information
     * ctx = context of free index variables
     * con = constraints on index variables
     * D = context of channels with their types (xi : Ai)
     * pot = available potential
     * P = process expression
     * (z : C) = provided channel and its type
     * ext is approximation of source extent for P, if available
     *)
    val check_exp : bool -> Ast.env -> Ast.tp_ctx -> Arith.ctx -> Arith.prop
                    -> Ast.context -> Ast.pot -> Ast.exp -> Ast.chan_tp -> Ast.ext -> unit

end (* signature TYPE_CHECK *)

structure TypeCheck :> TYPE_CHECK =
struct

structure R = Arith
structure A = Ast
structure PP = PPrint
structure E = TpError
structure TU = TypeUtil
structure TEQ = TypeEquality
structure TCU = TypeCheckUtil
structure C = Constraints
val ERROR = ErrorMsg.ERROR

(* Utilities *)
(* these may belong in tc-util.sml *)

fun exists_chan x ((y,A)::D) = if x = y then true else exists_chan x D
  | exists_chan x [] = false

fun gen_context env xs D ext = List.map (fn x => (x,TCU.lookup_context env x D ext)) xs

(*************************************)
(* Type checking process expressions *)
(*************************************)

fun eventually_box_context env [] ext = ()
  | eventually_box_context env ((x,A)::D') ext =
    if TU.eventually_box env A then eventually_box_context env D' ext
    else ERROR ext ("type of " ^ x ^ " : " ^ PP.pp_tp_compact env A ^ " is not patient (ie, not (n)[]A")

(* match_contexts env tpctx ctx con D D' ext = ()
 *
 * D is typing of channels passed to a process f in call
 * D' is typing of parameter channels in declaration of process f
 * Order should match, types should match, channel names may be different
 * match_contexts' env tpctx ctx con D D' ext
 * requires |D| = |D'|
 * with subtyping, for each matching pairs of type A <: A'
 *)
fun match_contexts' env tpctx ctx con ((x,A)::D) ((x',A')::D') ext =
    if TEQ.eq_tp env tpctx ctx con A A.CoVar A' (* check A <: A' *)
    then match_contexts' env tpctx ctx con D D' ext
    else E.error_type_mismatch env "call" ((x',A'), (x,A)) ext
  | match_contexts' env tpctx ctx con nil nil ext = ()

fun match_contexts env tpctx ctx con D D' ext =
    if List.length D = List.length D'
    then match_contexts' env tpctx ctx con D D' ext
    else E.error_channel_number "call" (List.length D', List.length D) ext

(* check_explist_pos ctx con es ext = ()
 * if ctx ; con |= e >= 0 for all e in es
 * raises ErrorMsg.Error otherwise
 *)
fun check_explist_pos ctx con (nil) ext = ()
  | check_explist_pos ctx con (e::es) ext =
    if not(C.entails ctx con (R.Ge(e, R.Int(0))))
    then ERROR ext ("index cannot be shown to be positive: " ^ C.pp_jfail con (R.Ge(e, R.Int(0))))
    else check_explist_pos ctx con es ext

(* check_exp trace env tpctx ctx con D pot P (z,C) = () if tpctx ctx ; con ; D |{pot}- P :: (z : C)
 * raises ErrorMsg.Error otherwise
 * requires tpctx ctx |- con prop
 *          tpctx ctx ; con |= D valid
 *          tpctx ctx ; con |= C valid
 *          tpctx ctx ; con |= pot nat
 *          variables in D, z all distincts
 *
 * trace = true means to print some tracing information
 *
 * entry point is check_exp'
 *)
fun check_exp' trace env tpctx ctx con D pot P zC ext =
    ( if trace
      then TextIO.print (PP.pp_exp_prefix env P ^ " : "
                         ^ PP.pp_tpj_compact env D pot zC ^ "\n")
      else ()

      (* strip zero delays *)
    ; check_exp trace env tpctx ctx con
                (TU.strip_next0_context env ctx con D)
                pot P
                (TU.strip_next0 env ctx con zC) ext
    )

(* the following section has one function per inference rule *)
and fwd trace env tpctx ctx con D pot (A.Id(x,y)) (zC as (z,C)) ext =
    let val () = if x <> z then E.error_channel_mismatch "forward" (z,x) ext else ()
        val A = TCU.lookup_context env y D ext
        val D' = TCU.remove_chan y D ext
        val () = case D' of nil => ()
                          | _ => E.error_channels_open "forward" D' ext
        val () = if TEQ.eq_tp env tpctx ctx con A A.CoVar C then ()  (* check A <: C *)
                 else E.error_type_mismatch env "forward" ((y,C), (y,A)) ext
        val () = if not (C.entails ctx con (R.Eq(pot, R.Int(0))))
                 then ERROR ext ("unconsumed potential: " ^ C.pp_jfail con (R.Eq(pot, R.Int(0))))
                 else ()
    in () end

and spawn trace env tpctx ctx con D pot (A.Spawn(A.ExpName(x,f,As,es,xs),Q)) (zC as (z,C)) ext =
    let val (con',(D',pot',(z',B))) = TCU.expd_expdec_check env tpctx ctx con (f,As,es) ext  (* fix empty type context? *)
        val () = if List.length D' = List.length xs then ()
                 else E.error_channel_number "spawn" (List.length D', List.length xs) ext
        val cutD = gen_context env xs D ext
        val () = match_contexts env tpctx ctx con cutD D' ext
        val () = if not (C.entails ctx con (R.Ge(pot, pot')))
                 then ERROR ext ("insufficient potential to spawn: " ^ C.pp_jfail con (R.Ge(pot, pot')))
                 else ()
        val () = if not (C.entails ctx con (R.Ge(pot',R.Int(0)))) (* and potential >= 0 *)
                 then ERROR ext ("potential not positive: " ^ C.pp_jfail con (R.Ge(pot', R.Int(0))))
                 else ()
        val () = check_explist_pos ctx con es ext
        val () = if not (C.entails ctx con con')
                 then ERROR ext ("constraint not entailed: " ^ C.pp_jfail con con')
                 else ()
        val contD = TCU.remove_chans xs D ext
        val () = if x = z
                 then E.error_channel_mismatch "spawn" ("fresh <id>", x) ext
                 else ()
        val () = if List.exists (fn (x',_) => x = x') contD
                 then E.error_channel_mismatch "spawn" ("fresh <id>", x) ext
                 else ()
    in
        check_exp' trace env tpctx ctx con ((x,B)::contD) (R.minus(pot,pot')) Q zC ext
    end
  | spawn trace env tpctx ctx con D pot (A.Spawn(A.Marked(marked_P),Q)) zC ext =
    spawn trace env tpctx ctx con D pot (A.Spawn(Mark.data marked_P,Q)) zC (Mark.ext marked_P)

and expname trace env tpctx ctx con D pot (A.ExpName(x,f,As,es,xs)) (z,C) ext =
    let val () = if x <> z
                 then E.error_channel_mismatch "tail call" (z,x) ext
                 else ()
        val (con',(D',pot',(z',C'))) = TCU.expd_expdec_check env tpctx ctx con (f,As,es) ext (* fix!!! *)
        val () = if List.length D' = List.length xs then ()
                 else E.error_channel_number "tail call" (List.length D', List.length xs) ext
        val cutD = gen_context env xs D ext
        val () = match_contexts env tpctx ctx con cutD D' ext
        val () = if TEQ.eq_tp env tpctx ctx con C' A.CoVar C then () (* C' <: C *)
                 else E.error_type_mismatch env "tail call" ((z,C), (z,C')) ext
        val () = if not (C.entails ctx con (R.Eq(pot, pot')))
                 then ERROR ext ("potential mismatch: " ^ C.pp_jfail con (R.Eq(pot, pot')))
                 else ()
        val () = check_explist_pos ctx con es ext
        val () = if not (C.entails ctx con con')
                 then ERROR ext ("constraint not entailed: " ^ C.pp_jfail con con')
                 else ()
        val D' = TCU.remove_chans xs D ext
        val () = case D' of nil => ()
                          | _ => E.error_channels_open "tail call" D' ext
    in () end

and plusR trace env tpctx ctx con D pot (A.Lab(x,k,P)) (z,C as A.Plus(choices)) ext (* z = x *) =
    (case A.lookup_choice choices k
      of SOME(Ck) => check_exp' trace env tpctx ctx con D pot P (z,Ck) ext
       | NONE => E.error_label_invalid env (k, C, ext))
  | plusR trace env tpctx ctx con D pot (A.Lab(x,k,P)) (z,C) ext =
    E.error_channel_type_mismatch env ("+{ <choices> }", (z,C)) ext

and withL trace env tpctx ctx con D (A as A.With(choices)) pot (A.Lab(x,k,P)) zC ext (* z != x *) =
    (case A.lookup_choice choices k
      of SOME(Ak) => check_exp' trace env tpctx ctx con (TCU.update_tp (x,Ak) D) pot P zC ext
      | NONE => E.error_label_invalid env (k, A, ext))
  | withL trace env tpctx ctx cond D A pot (A.Lab(x,k,P)) zC ext =
    E.error_channel_type_mismatch env ("&{ <choices> } (external choice)", (x,A)) ext

(* check_branchesR trace env tpctx ctx con A branches choices = ()
 * for provider of external choice &{...}
 *)
and check_branchesR trace env tpctx ctx con D pot nil (z,nil) ext = ()
  | check_branchesR trace env tpctx ctx con D pot ((l,ext',P)::branches) (z,choices) ext =
    (* no longer require exact order *)
    let val () = if trace then TextIO.print ("| " ^ l ^ " => \n") else ()
        val (C, choices') = TCU.get_choice l choices ext'
        val () = check_exp' trace env tpctx ctx con D pot P (z,C) ext
        val () = check_branchesR trace env tpctx ctx con D pot branches (z,choices') ext
    in () end
  | check_branchesR trace env tpctx ctx con D pot nil (z,(l',C)::_) ext = E.error_label_missing_branch (l', ext)

and withR trace env tpctx ctx con D pot (A.Case(x,branches)) (z,A.With(choices)) ext (* z = x *) =
    check_branchesR trace env tpctx ctx con D pot branches (z,choices) ext
  | withR trace env tpctx ctx con D pot (A.Case(x,branches)) (z,C) ext =
    E.error_channel_type_mismatch env ("&{ <choices> } (external choice)", (z,C)) ext

(* check_branchesL env tpctx ctx con choices branches C ext = ()
 * for client of internal choice +{...}
 *)
and check_branchesL trace env tpctx ctx con D (x,nil) pot nil zC ext = ()
  | check_branchesL trace env tpctx ctx con D (x,choices) pot ((l',ext',P)::branches) zC ext =
    (* no longer require exact order *)
    let val () = if trace then TextIO.print ("| " ^ l' ^ " => \n") else ()
        val (A,choices') = TCU.get_choice l' choices ext'
        val () = check_exp' trace env tpctx ctx con (TCU.update_tp (x,A) D) pot P zC ext
        val () = check_branchesL trace env tpctx ctx con D (x,choices') pot branches zC ext
    in () end
  | check_branchesL trace env tpctx ctx con D (x,(l,A)::_) pot nil zC ext = E.error_label_missing_branch (l, ext)

and plusL trace env tpctx ctx con D (A.Plus(choices)) pot (A.Case(x,branches)) zC ext (* z != x *) =
    check_branchesL trace env tpctx ctx con D (x,choices) pot branches zC ext
  | plusL trace env tpctx ctx con D A pot (A.Case(x,branches)) zC ext =
    E.error_channel_type_mismatch env ("+{ <choices> } (internal choice)", (x,A)) ext

and tensorR trace env tpctx ctx con D pot (A.Send(x,w,P)) (z,A.Tensor(A,B)) ext (* z = x *) =
    let val A' = TCU.lookup_context env w D ext
        val () = if TEQ.eq_tp env tpctx ctx con A' A.CoVar A then ()  (* check A' <: A *)
                 else E.error_type_mismatch env "channel send" (("<id>", A), (w, A')) ext
    in
        check_exp' trace env tpctx ctx con (TCU.remove_chan w D ext) pot P (z,B) ext
    end
  | tensorR trace env tpctx ctx con D pot (A.Send(x,w,P)) (z,C) ext =
    E.error_channel_type_mismatch env ("<type> * <type>", (x,C)) ext

and lolliL trace env tpctx ctx con D (A.Lolli(A,B)) pot (A.Send(x,w,Q)) zC ext (* z != x *) =
    let val A' = TCU.lookup_context env w D ext
        val () = if TEQ.eq_tp env tpctx ctx con A' A.CoVar A then () (* check A' <: A *)
                 else E.error_type_mismatch env "channel send" (("<id>",A), (w, A')) ext
    in
        check_exp' trace env tpctx ctx con (TCU.update_tp (x,B) (TCU.remove_chan w D ext)) pot Q zC ext
    end
  | lolliL trace env tpctx ctx con D A pot (A.Send(x,w,Q)) zC ext =
    E.error_channel_type_mismatch env ("<type> -o <type>", (x,A)) ext

and lolliR trace env tpctx ctx con D pot (A.Recv(x,y,P)) (z,A.Lolli(A,B)) ext (* z = x *) =
    if exists_chan y ((z,A.Lolli(A,B))::D)
    then E.error_channel_mismatch "channel receive" ("fresh <id>", y) ext
    else check_exp' trace env tpctx ctx con ((y,A)::D) pot P (z,B) ext
  | lolliR trace env tpctx ctx con D pot (A.Recv(x,y,P)) (z,C) ext =
    E.error_channel_type_mismatch env ("<type> -o <type>", (x,C)) ext

and tensorL trace env tpctx ctx con D (A.Tensor(A,B)) pot (A.Recv(x,y,Q)) zC ext (* z != x *) =
    if exists_chan y (zC::D)
    then E.error_channel_mismatch "channel receive" ("fresh <id>", y) ext
    else check_exp' trace env tpctx ctx con ((y,A)::(TCU.update_tp (x,B) D)) pot Q zC ext
  | tensorL trace env tpctx ctx con D A pot (A.Recv(x,y,Q)) zC ext =
    E.error_channel_type_mismatch env ("<type> * <type>", (x,A)) ext

and oneR trace env tpctx ctx con D pot (A.Close(x)) (z,A.One) ext (* z = x *) =
    if List.length D > 0
    then E.error_channels_open "close" D ext
    else if not (C.entails ctx con (R.Eq(pot, R.Int(0))))
    then ERROR ext ("unconsumed potential: " ^ C.pp_jfail con (R.Eq(pot, R.Int(0))))
    else ()
  | oneR trace env tpctx ctx con D pot (A.Close(x)) (z,C) ext =
    E.error_channel_type_mismatch env ("1", (z,C)) ext

and oneL trace env tpctx ctx con D (A.One) pot (A.Wait(x,Q)) zC ext (* z != x *) =
    check_exp' trace env tpctx ctx con (TCU.remove_chan x D ext) pot Q zC ext
  | oneL trace env tpctx ctx con D A pot (A.Wait(x,Q)) zC ext =
    E.error_channel_type_mismatch env ("1", (x,A)) ext

and existsR trace env tpctx ctx con D pot (A.Assert(x,phi,P)) (z,A.Exists(phi',C)) ext (* z = x *) =
    if not (C.entails ctx con phi)
    then ERROR ext ("assertion not entailed: " ^ C.pp_jfail con phi)
    else if not (C.entails ctx con phi') (* equivalent would be con, phi |= phi' *)
    then ERROR ext ("type constraint not entailed: " ^ C.pp_jfail con phi')
    else check_exp' trace env tpctx ctx con D pot P (z,C) ext
  | existsR trace env tpctx ctx con D pot (A.Assert(x,phi,P)) (z,C) ext =
    E.error_channel_type_mismatch env ("?{ <prop> }", (z,C)) ext

and forallL trace env tpctx ctx con D (A.Forall(phi',A)) pot (A.Assert(x,phi,P)) zC ext (* z != x *) =
    if not (C.entails ctx con phi)
    then ERROR ext ("assertion not entailed: " ^ C.pp_jfail con phi)
    else if not (C.entails ctx con phi') (* equivalent would be con, phi |= phi' *)
    then ERROR ext ("type constraint not entailed: " ^ C.pp_jfail con phi')
    else check_exp' trace env tpctx ctx con (TCU.update_tp (x,A) D) pot P zC ext
  | forallL trace env tpctx ctx con D A pot (A.Assert(x,phi,P)) zC ext =
    E.error_channel_type_mismatch env ("!{ <prop> }", (x,A)) ext

and forallR trace env tpctx ctx con D pot (A.Assume(x,phi,P)) (z,A.Forall(phi',C)) ext (* z = x *) =
    if not (C.entails ctx (R.And(con,phi')) phi)
    then ERROR ext ("assumption not entailed: " ^ C.pp_jfail (R.And(con,phi')) phi)
    else check_exp' trace env tpctx ctx (R.And(con,phi)) D pot P (z,C) ext (* assume only the possibly weaker phi *)
  | forallR trace env tpctx ctx con D pot (A.Assume(x,phi,P)) (z,C) ext =
    E.error_channel_type_mismatch env ("!{ <prop> }", (z,C)) ext
  
and existsL trace env tpctx ctx con D (A.Exists(phi',A)) pot (A.Assume(x,phi,P)) zC ext (* z != x *) =
    if not (C.entails ctx (R.And(con,phi')) phi) (* con, phi' |= phi *)
    then ERROR ext ("assumption not entailed: " ^ C.pp_jfail (R.And(con,phi')) phi)
    else check_exp' trace env tpctx ctx (R.And(con,phi)) (TCU.update_tp (x,A) D) pot P zC ext (* assume the possibly weaker phi *)
  | existsL trace env tpctx ctx con D A pot (A.Assume(x,phi,P)) zC ext =
    E.error_channel_type_mismatch env ("?{ <prop> }", (x,A)) ext

and existsNatR trace env tpctx ctx con D pot (A.SendNat(x,e,P)) (z,A.ExistsNat(v,C)) ext (* z = x *) =
    check_exp' trace env tpctx ctx con D pot P (z, A.apply_tp (R.zip [v] [e]) C) ext
  | existsNatR trace env tpctx ctx con D pot (A.SendNat(x,e,P)) (z,C) ext =
    E.error_channel_type_mismatch env ("?<id>. <type>", (z,C)) ext

and forallNatL trace env tpctx ctx con D (A.ForallNat(v,A)) pot (A.SendNat(x,e,P)) zC ext (* z != x *) =
    check_exp' trace env tpctx ctx con (TCU.update_tp (x, A.apply_tp (R.zip [v] [e]) A) D) pot P zC ext
  | forallNatL trace env tpctx ctx con D A pot (A.SendNat(x,e,P)) zC ext (* z != x *) =
    E.error_channel_type_mismatch env ("!<id>. <type>", (x,A)) ext

and forallNatR trace env tpctx ctx con D pot (A.RecvNat(x,v,P)) (z,A.ForallNat(v',C)) ext (* z = x *) =
    check_exp' trace env tpctx (v::ctx) con D pot P (z, A.apply_tp (R.zip [v'] [R.Var(v)]) C) ext
  | forallNatR trace env tpctx ctx con D pot (A.RecvNat(x,v,P)) (z,C) ext =
    E.error_channel_type_mismatch env ("!<id>. <type>", (z,C)) ext

and existsNatL trace env tpctx ctx con D (A.ExistsNat(v',A)) pot (A.RecvNat(x,v,P)) zC ext (* z != x *) =
    check_exp' trace env tpctx (v::ctx) con (TCU.update_tp (x, A.apply_tp (R.zip [v'] [R.Var(v)]) A) D) pot P zC ext
  | existsNatL trace env tpctx ctx con D A pot (A.RecvNat(x,v,P)) zC ext =
    E.error_channel_type_mismatch env ("?<id>. <type>", (x,A)) ext

and existsTpR trace env tpctx ctx con D pot (A.SendTp(x,A,P)) (z,A.ExistsTp(alpha,C)) ext (* z = x *) =
    check_exp' trace env tpctx ctx con D pot P (z, A.subst_tp [(alpha,A)] C) ext
  | existsTpR trace env tpctx ctx con D pot (A.SendTp(x,A,P)) (z,C) ext =
    E.error_channel_type_mismatch env ("?[<id>]. <type>", (z,C)) ext

and forallTpL trace env tpctx ctx con D (A.ForallTp(alpha,B)) pot (A.SendTp(x,A,P)) zC ext (* z != x *) =
    check_exp' trace env tpctx ctx con (TCU.update_tp (x, A.subst_tp [(alpha,A)] B) D) pot P zC ext
  | forallTpL trace env tpctx ctx con D B pot (A.SendTp(x,A,P)) zC ext (* z != x *) =
    E.error_channel_type_mismatch env ("![<id>]. <type>", (x,B)) ext

and forallTpR trace env tpctx ctx con D pot (A.RecvTp(x,alpha,P)) (z,A.ForallTp(alpha',C)) ext (* z = x *) =
    check_exp' trace env (alpha::tpctx) ctx con D pot P (z, A.subst_tp [(alpha',A.TpVar(alpha))] C) ext
  | forallTpR trace env tpctx ctx con D pot (A.RecvTp(x,alpha,P)) (z,C) ext =
    E.error_channel_type_mismatch env ("![<id>]. <type>", (z,C)) ext

and existsTpL trace env tpctx ctx con D (A.ExistsTp(alpha',A)) pot (A.RecvTp(x,alpha,P)) zC ext (* z != x *) =
    check_exp' trace env (alpha::tpctx) ctx con (TCU.update_tp (x, A.subst_tp [(alpha',A.TpVar(alpha))] A) D) pot P zC ext
  | existsTpL trace env tpctx ctx con D A pot (A.RecvTp(x,alpha,P)) zC ext =
    E.error_channel_type_mismatch env ("?[<id>]. <type>", (x,A)) ext

and work trace env tpctx ctx con D pot (A.Work(p,P)) zC ext =
    if not (C.entails ctx con (R.Ge(p,R.Int(0))))
    then ERROR ext ("potential not positive: " ^ C.pp_jfail con (R.Ge(p,R.Int(0))))
    else if not (C.entails ctx con (R.Ge(pot,p)))
    then ERROR ext ("insufficient potential: " ^ C.pp_jfail con (R.Ge (pot, p)))
    else check_exp' trace env tpctx ctx con D (R.minus(pot,p)) P zC ext

and paypotR trace env tpctx ctx con D pot (A.Pay(x,p',P)) (z,A.PayPot(p,C)) ext (* z = x *) =
    (* con |= p >= 0 since type is valid *)
    if not (C.entails ctx con (R.Ge(pot,p')))
    then ERROR ext ("insufficient potential: " ^ C.pp_jfail con (R.Ge(pot, p')))
    else if not (C.entails ctx con (R.Eq(p',p)))
    then ERROR ext ("potential mismatch: " ^ C.pp_jfail con (R.Eq(p',p)))
    else check_exp' trace env tpctx ctx con D (R.minus (pot,p)) P (z,C) ext
  | paypotR trace env tpctx ctx con D pot (A.Pay(x,p',P)) (z,C) ext =
    E.error_channel_type_mismatch env ("|> <type>", (z,C)) ext

and getpotL trace env tpctx ctx con D (A.GetPot(p,A)) pot (A.Pay(x,p',P)) zC ext (* z != x *) =
    (* con |= p >= 0 since type is valid *)
    if not (C.entails ctx con (R.Ge(pot,p)))
    then ERROR ext ("insufficient potential: " ^ C.pp_jfail con (R.Ge (pot, p)))
    else if not (C.entails ctx con (R.Eq(p,p')))
    then ERROR ext ("potential mismatch: " ^ C.pp_jfail con (R.Eq(p,p')))
    else check_exp' trace env tpctx ctx con (TCU.update_tp (x,A) D) (R.minus (pot,p)) P zC ext
  | getpotL trace env tpctx ctx con D A pot (A.Pay(x,p',P)) zC ext =
    E.error_channel_type_mismatch env ("<| <type>", (x,A)) ext

and getpotR trace env tpctx ctx con D pot (A.Get(x,p',P)) (z,A.GetPot(p,C)) ext (* z = x *) =
    (* con |= p >= 0 since type is valid *)
    if not (C.entails ctx con (R.Eq(p',p)))
    then ERROR ext ("potential mismatch: " ^ C.pp_jfail con (R.Eq(p',p)))
    else check_exp' trace env tpctx ctx con D (R.plus (pot,p)) P (z,C) ext
  | getpotR trace env tpctx ctx con D pot (A.Get(x,p',P)) (z,C) ext =
    E.error_channel_type_mismatch env ("|> <type>", (z,C)) ext

and paypotL trace env tpctx ctx con D (A.PayPot(p,A)) pot (A.Get(x,p',P)) zC ext (* z != x *) =
    (* con |= p >= 0 since type is valid *)
    if not (C.entails ctx con (R.Eq(p,p')))
    then ERROR ext ("potential mismatch: " ^ C.pp_jfail con (R.Eq(p,p')))
    else check_exp' trace env tpctx ctx con (TCU.update_tp (x,A) D) (R.plus (pot,p)) P zC ext
  | paypotL trace env tpctx ctx con D A pot (A.Get(x,p',P)) zC ext =
    E.error_channel_type_mismatch env ("<| <type>", (x,A)) ext

and delay trace env tpctx ctx con D pot (A.Delay(t,P)) (z,C) ext =
    if not(C.entails ctx con (R.Ge(t,R.Int(0))))
    then ERROR ext ("delay cannot be shown to be positive : " ^ C.pp_jfail con (R.Ge(t,R.Int(0))))
    else check_exp' trace env tpctx ctx con (TU.decrement_context env ctx con D t ext) pot P
                    (z,TU.decrementR env ctx con C t ext) ext

and diaR trace env tpctx ctx con D pot (A.Now(x,P)) (z,A.Dia(C)) ext (* z = x *) =
    check_exp' trace env tpctx ctx con D pot P (z,C) ext
  | diaR trace env tpctx ctx con D pot (A.Now(x,P)) (z,C) ext =
    E.error_channel_type_mismatch env ("<> <type>", (z,C)) ext

and boxL trace env tpctx ctx con D (A.Box(A)) pot (A.Now(x,P)) zC ext (* z != x *) =
    check_exp' trace env tpctx ctx con (TCU.update_tp (x,A) D) pot P zC ext
  | boxL trace env tpctx ctx con D A pot (A.Now(x,P)) zC ext =
    E.error_channel_type_mismatch env ("[] <type>", (x,A)) ext

and boxR trace env tpctx ctx con D pot (A.When(x,P)) (z,A.Box(C)) ext (* z = x *) =
    let val () = eventually_box_context env D ext
    in
        check_exp' trace env tpctx ctx con D pot P (z,C) ext
    end
  | boxR trace env tpctx ctx con D pot (A.When(x,P)) (z,C) ext =
    E.error_channel_type_mismatch env ("[] <type>", (z,C)) ext

and diaL trace env tpctx ctx con D (A.Dia(A)) pot (A.When(x,P)) (z,C) ext (* z != x *) =
    let val () = if TU.eventually_dia env C then ()
                 else ERROR ext ("type " ^ PP.pp_tp_compact env C ^ " is not patient (ie, not (n)<>A")
    in
        check_exp' trace env tpctx ctx con (TCU.update_tp (x,A) D) pot P (z,C) ext
    end
  | diaL trace env tpctx ctx con D A pot (A.When(x,P)) (z,C) ext =
    E.error_channel_type_mismatch env ("<> <type>", (x,A)) ext

  (* judgmental constructs: id, cut, spawn, call *)
and check_exp trace env tpctx ctx con D pot (A.Id(x,y)) zC ext =
    fwd trace env tpctx ctx con D pot (A.Id(x,y)) zC ext
  | check_exp trace env tpctx ctx con D pot (A.Spawn(P,Q)) zC ext =
    spawn trace env tpctx ctx con D pot (A.Spawn(P,Q)) zC ext
  | check_exp trace env tpctx ctx con D pot (A.ExpName(x,f,As,es,xs)) (z,C) ext =
    expname trace env tpctx ctx con D pot (A.ExpName(x,f,As,es,xs)) (z,C) ext
    
  (* structural types +{...}, &{...}, 1 *)
  | check_exp trace env tpctx ctx con D pot (A.Lab(x,k,P)) (z,C) ext =
    if x = z
    then plusR trace env tpctx ctx con D pot (A.Lab(x,k,P)) (z,TU.expand env C) ext
    else withL trace env tpctx ctx con D (TCU.lookup_context env x D ext) pot (A.Lab(x,k,P)) (z,C) ext
  | check_exp trace env tpctx ctx con D pot (A.Case(x,branches)) (z,C) ext =
    if x = z
    then withR trace env tpctx ctx con D pot (A.Case(x,branches)) (z,TU.expand env C) ext
    else plusL trace env tpctx ctx con D (TCU.lookup_context env x D ext) pot (A.Case(x,branches)) (z,C) ext

  | check_exp trace env tpctx ctx con D pot (A.Send(x,w,P)) (z,C) ext =
    if x = z
    then tensorR trace env tpctx ctx con D pot (A.Send(x,w,P)) (z,TU.expand env C) ext
    else lolliL trace env tpctx ctx con D (TCU.lookup_context env x D ext) pot (A.Send(x,w,P)) (z,C) ext
  | check_exp trace env tpctx ctx con D pot (A.Recv(x,y,Q)) (z,C) ext =
    if x = z
    then lolliR trace env tpctx ctx con D pot (A.Recv(x,y,Q)) (z,TU.expand env C) ext
    else tensorL trace env tpctx ctx con D (TCU.lookup_context env x D ext) pot (A.Recv(x,y,Q)) (z,C) ext

  | check_exp trace env tpctx ctx con D pot (A.Close(x)) (z,C) ext =
    if x = z
    then oneR trace env tpctx ctx con D pot (A.Close(x)) (z,TU.expand env C) ext
    else E.error_channel_mismatch "close" (z,x) ext
  | check_exp trace env tpctx ctx con D pot (A.Wait(x,Q)) (z,C) ext =
    if x = z
    then E.error_channel_mismatch "wait" ("<id> not equal " ^ z, x) ext
    else oneL trace env tpctx ctx con D (TCU.lookup_context env x D ext) pot (A.Wait(x,Q)) (z,C) ext

  (* quantified types ?{phi}.A, !{phi}.A *)
  | check_exp trace env tpctx ctx con D pot (A.Assert(x,phi,P)) (z,C) ext =
    if x = z
    then existsR trace env tpctx ctx con D pot (A.Assert(x,phi,P)) (z,TU.expand env C) ext
    else forallL trace env tpctx ctx con D (TCU.lookup_context env x D ext) pot (A.Assert(x,phi,P)) (z,C) ext

  | check_exp trace env tpctx ctx con D pot (A.Assume(x,phi,Q)) (z,C) ext =
    if x = z
    then forallR trace env tpctx ctx con D pot (A.Assume(x,phi,Q)) (z,TU.expand env C) ext
    else existsL trace env tpctx ctx con D (TCU.lookup_context env x D ext) pot (A.Assume(x,phi,Q)) (z,C) ext    

  (* quantified types ?v.A, !v.A *)
  | check_exp trace env tpctx ctx con D pot (A.SendNat(x,e,P)) (z,C) ext =
    if x = z
    then existsNatR trace env tpctx ctx con D pot (A.SendNat(x,e,P)) (z,TU.expand env C) ext
    else forallNatL trace env tpctx ctx con D (TCU.lookup_context env x D ext) pot (A.SendNat(x,e,P)) (z,C) ext

  | check_exp trace env tpctx ctx con D pot (A.RecvNat(x,v,P)) (z,C) ext =
    if x = z
    then forallNatR trace env tpctx ctx con D pot (A.RecvNat(x,v,P)) (z,TU.expand env C) ext
    else existsNatL trace env tpctx ctx con D (TCU.lookup_context env x D ext) pot (A.RecvNat(x,v,P)) (z,C) ext

  (* quantified types ?[alpha].A, ![alpha].A *)
  | check_exp trace env tpctx ctx con D pot (A.SendTp(x,A,P)) (z,C) ext =
    if x = z
    then existsTpR trace env tpctx ctx con D pot (A.SendTp(x,A,P)) (z,TU.expand env C) ext
    else forallTpL trace env tpctx ctx con D (TCU.lookup_context env x D ext) pot (A.SendTp(x,A,P)) (z,C) ext

  | check_exp trace env tpctx ctx con D pot (A.RecvTp(x,alpha,P)) (z,C) ext =
    if x = z
    then forallTpR trace env tpctx ctx con D pot (A.RecvTp(x,alpha,P)) (z,TU.expand env C) ext
    else existsTpL trace env tpctx ctx con D (TCU.lookup_context env x D ext) pot (A.RecvTp(x,alpha,P)) (z,C) ext

  (* impossibility *)
  | check_exp trace env tpctx ctx con D pot (A.Imposs) zC ext =
    if not (C.contradictory ctx con R.True) (* TODO: fix interface *)
    then ERROR ext ("constraints not contradictory: " ^ C.pp_jsat con R.True)
    else ()

  (* ergometric types |>, <| *)
  | check_exp trace env tpctx ctx con D pot (A.Work(p,P)) zC ext =
    work trace env tpctx ctx con D pot (A.Work(p,P)) zC ext
  | check_exp trace env tpctx ctx con D pot (A.Pay(x,p',P)) (z,C) ext =
    if x = z
    then paypotR trace env tpctx ctx con D pot (A.Pay(x,p',P)) (z,TU.expand env C) ext
    else getpotL trace env tpctx ctx con D (TCU.lookup_context env x D ext) pot (A.Pay(x,p',P)) (z,C) ext
  | check_exp trace env tpctx ctx con D pot (A.Get(x,p',P)) (z,C) ext =
    if x = z
    then getpotR trace env tpctx ctx con D pot (A.Get(x,p',P)) (z,TU.expand env C) ext
    else paypotL trace env tpctx ctx con D (TCU.lookup_context env x D ext) pot (A.Get(x,p',P)) (z,C) ext

  (* temporal types (), [], <> *)
  | check_exp trace env tpctx ctx con D pot (A.Delay(t,P)) (z,C) ext =
    delay trace env tpctx ctx con D pot (A.Delay(t,P)) (z,C) ext
  
  | check_exp trace env tpctx ctx con D pot (A.Now(x,P)) (z,C) ext =
    if x = z
    then diaR trace env tpctx ctx con D pot (A.Now(x,P)) (z,TU.expand env C) ext
    else boxL trace env tpctx ctx con D (TCU.lookup_context env x D ext) pot (A.Now(x,P)) (z,C) ext
  | check_exp trace env tpctx ctx con D pot (A.When(x,P)) (z,C) ext =
    if x = z
    then boxR trace env tpctx ctx con D pot (A.When(x,P)) (z,TU.expand env C) ext
    else diaL trace env tpctx ctx con D (TCU.lookup_context env x D ext) pot (A.When(x,P)) (z,C) ext

  (* marked expressions *)
  | check_exp trace env tpctx ctx con D pot (A.Marked(marked_P)) zC ext =
    check_exp trace env tpctx ctx con D pot (Mark.data marked_P) zC (Mark.ext marked_P)

fun check_exp_top trace env tpctx ctx con D pot P zC ext =
    check_exp' trace env tpctx ctx con D pot P zC ext

(* external interface *)
fun check_exp trace env tpctx ctx con D pot P zC ext =
    check_exp_top trace env tpctx ctx con D pot P zC ext

end (* structure TypeCheck *)
