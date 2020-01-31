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
    (* check_exp trace env ctx con D pot P zC ext = ()
     * checks that D |- P : (z : C) with potential pot
     * trace = true means print some tracinng information
     * ctx = context of free index variables
     * con = constraints on index variables
     * D = context of channels
     * pot = available potential
     * P = process expression
     * zC = (z : C) = provided channel and type
     * ext is approximation of source extent for P, if available
     * may raise ErrorMsg.Error
    *)
    val check_exp : bool -> Ast.env -> Arith.ctx -> Arith.prop
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

(* match_contexts env ctx con D D' ext = ()
 * D is typing of channels passed to a process f in call
 * D' is typing of parameter channels in declaration of process f
 * Order should match, types should match, channel names may be different
 *)
fun match_contexts env ctx con ((x,A)::D) ((x',A')::D') ext =
    if TEQ.eq_tp env ctx con A A'
    then match_contexts env ctx con D D' ext
    else let val (x_len,x'_len) = (String.size x, String.size x')
             val var_len = Int.max(x_len, x'_len)
             val (x_str,x'_str) = (StringCvt.padRight #" " var_len x,
                                   StringCvt.padRight #" " var_len x')
         in
             ERROR ext ("type mismatch in call:\n"
                        ^ "expected " ^ x'_str ^ " : " ^ PP.pp_tp_compact env A' ^ "\n"
                        ^ "found    " ^ x_str ^ " : " ^ PP.pp_tp_compact env A)
         end
  | match_contexts env ctx con nil nil ext = ()
  | match_contexts env ctx con D D' ext =
    ERROR ext ("wrong number of arguments in call:\n"
               ^ "expected " ^ PP.pp_context_compact env D' ^ "\n"
               ^ "found    " ^ PP.pp_context_compact env D)


(* check_explist_pos ctx con es ext = ()
 * if ctx ; con |= e >= 0 for all e in es
 * raises ErrorMsg.Error otherwise
 *)
fun check_explist_pos ctx con (nil) ext = ()
  | check_explist_pos ctx con (e::es) ext =
    if not(C.entails ctx con (R.Ge(e, R.Int(0))))
    then ERROR ext ("index cannot be shown to be positive: " ^ C.pp_jfail con (R.Ge(e, R.Int(0))))
    else check_explist_pos ctx con es ext

(* check_exp trace env ctx con D pot P C = () if ctx ; con ; D |{pot}- P : C
 * raises ErrorMsg.Error otherwise
 * assumes ctx ; con |= D valid
 *         ctx ; con |= C valid
 *         ctx ; con |= pot nat
 *
 * trace = true means to print some tracing information
 *
 * entry point is check_exp'
 *)
fun check_exp' trace env ctx con D pot P zC ext =
    ( if trace
      then TextIO.print (PP.pp_exp_prefix env P ^ " : "
                         ^ PP.pp_tpj_compact env D pot zC ^ "\n")
      else ()

      (* strip zero delays *)
    ; check_exp trace env ctx con (TU.strip_next0_context env ctx con D) pot P
                (TU.strip_next0 env ctx con zC) ext
    )

and fwd trace env ctx con D pot (A.Id(x,y)) zC ext =
    let val A = TCU.lookup_context env y D ext
        val C = TCU.lookup_context env x [zC] ext
        val () = if TEQ.eq_tp env ctx con A C then ()
                 else ERROR ext ("type mismatch in forward:\n"
                                 ^ "expected " ^ y ^ " : " ^ PP.pp_tp_compact env C ^ "\n"
                                 ^ "found    " ^ y ^ " : " ^ PP.pp_tp_compact env A)
        val () = if not (C.entails ctx con (R.Eq(pot, R.Int(0))))
                 then ERROR ext ("unconsumed potential: " ^ C.pp_jfail con (R.Eq(pot, R.Int(0))))
                 else ()
        val () = if List.length D <> 1
                 then ERROR ext ("context " ^ PP.pp_context_compact env D ^ " not singleton for fwd")
                 else ()
    in () end

and spawn trace env ctx con D pot (A.Spawn(A.ExpName(x,f,es,xs),Q)) zC ext =
    (case TCU.expd_expdec_check env (f,es) ext
      of (con',(D',pot',(z',B))) =>
         let val () = if List.length D' = List.length xs then ()
                      else ERROR ext ("incorrect number of arguments in call:\n"
                                      ^ "expected " ^ Int.toString (List.length D') ^ "\n"
                                      ^ "found    " ^ Int.toString (List.length xs))
             val cutD = gen_context env xs D ext
             val () = match_contexts env ctx con cutD D' ext (* should this be after entails? *)
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
             val () = if exists_chan x (zC::D) then ERROR ext ("variable " ^ x ^ " not fresh") else ()
         in
             check_exp' trace env ctx con ((x,B)::contD) (R.minus(pot,pot')) Q zC ext
         end
    )
  | spawn trace env ctx con D pot (A.Spawn(A.Marked(marked_P),Q)) zC ext =
    spawn trace env ctx con D pot (A.Spawn(Mark.data marked_P,Q)) zC (Mark.ext marked_P)


and expname trace env ctx con D pot (A.ExpName(x,f,es,xs)) (z,C) ext =
    (* verify the type, but also make sure f is defined somewhere *)
    (* eq_context expects lists in the same order, no reordering *)
    if x <> z
    then ERROR ext ("name mismatch: " ^ x ^ " <> " ^ z)
    else
    (case TCU.expd_expdec_check env (f,es) ext
      of (con',(D',pot',(z',C'))) =>
         let val () = if List.length D' = List.length xs then ()
                      else ERROR ext ("incorrect number of arguments in tail call:\n"
                                      ^ "expected " ^ Int.toString (List.length D')
                                      ^ "found    " ^ Int.toString (List.length xs))
             val cutD = gen_context env xs D ext
             val () = match_contexts env ctx con cutD D' ext
             val () = if TEQ.eq_tp env ctx con C' C then ()
                      else ERROR ext ("type mismatch in tail call:\n"
                                      ^ "expected " ^ z ^ " : " ^ PP.pp_tp_compact env C' ^ "\n"
                                      ^ "found    " ^ z ^ " : " ^ PP.pp_tp_compact env C)
             val () = if not (C.entails ctx con (R.Eq(pot, pot')))
                      then ERROR ext ("potential mismatch: " ^ C.pp_jfail con (R.Eq(pot, pot')))
                      else ()
             val () = check_explist_pos ctx con es ext
             val () = if not (C.entails ctx con con')
                      then ERROR ext ("constraint not entailed: " ^ C.pp_jfail con con')
                      else ()
             val contD = TCU.remove_chans xs D ext
             val () = if List.length contD > 0
                      then ERROR ext ("unconsumed channels " ^ PP.pp_context_compact env contD ^ " at tail call")
                      else ()
         in () end
    )

and plusR trace env ctx con D pot (A.Lab(x,k,P)) (z,C as A.Plus(choices)) ext (* z = x *) =
    (case A.lookup_choice choices k
      of SOME(Ck) => check_exp' trace env ctx con D pot P (z,Ck) ext
      | NONE => E.error_label_invalid env (k, C, ext))
  | plusR trace env ctx con D pot (A.Lab(x,k,P)) (z,C) ext =
    ERROR ext ("type mismatch for " ^ x ^ ": expected internal choice, found: " ^ PP.pp_tp_compact env C)

and withL trace env ctx con D (A as A.With(choices)) pot (A.Lab(x,k,P)) zC ext (* z != x *) =
    (case A.lookup_choice choices k
      of SOME(Ak) => check_exp' trace env ctx con (TCU.update_tp (x,Ak) D) pot P zC ext
      | NONE => E.error_label_invalid env (k, A, ext))
  | withL trace env ctx cond D A pot (A.Lab(x,k,P)) zC ext =
    ERROR ext ("type mismatch for " ^ x ^ ": expected external choice, found: " ^ PP.pp_tp_compact env A)

(* check_branchesR trace env ctx con A branches choices = ()
 * for provider of external choice &{...}
 *)
and check_branchesR trace env ctx con D pot nil (z,nil) ext = ()
  | check_branchesR trace env ctx con D pot ((l,ext',P)::branches) (z,(l',C)::choices) ext =
    (* require exact order *)
    ( if trace then TextIO.print ("| " ^ l ^ " => \n") else ()
    ; if l = l' then () else E.error_label_mismatch (l, l', ext')
    ; check_exp' trace env ctx con D pot P (z,C) ext
    ; check_branchesR trace env ctx con D pot branches (z,choices) ext )
  | check_branchesR trace env ctx con D pot ((l,ext',P)::_) (z,nil) ext = E.error_label_missing_alt (l, ext')
  | check_branchesR trace env ctx con D pot nil (z,(l',C)::_) ext = E.error_label_missing_branch (l', ext)

and withR trace env ctx con D pot (A.Case(x,branches)) (z,A.With(choices)) ext (* z = x *) =
    check_branchesR trace env ctx con D pot branches (z,choices) ext
  | withR trace env ctx con D pot (A.Case(x,branches)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected external choice, found: " ^ PP.pp_tp_compact env C)

(* check_branchesL env ctx con choices branches C ext = ()
 * for client of internal choice +{...}
 *)
and check_branchesL trace env ctx con D (x,nil) pot nil zC ext = ()
  | check_branchesL trace env ctx con D (x,(l,A)::choices) pot ((l',ext',P)::branches) zC ext =
    (* require exact order *)
    ( if trace then TextIO.print ("| " ^ l' ^ " => \n") else ()
    ; if l = l' then () else E.error_label_mismatch (l, l', ext')
    ; check_exp' trace env ctx con (TCU.update_tp (x,A) D) pot P zC ext
    ; check_branchesL trace env ctx con D (x,choices) pot branches zC ext )
  | check_branchesL trace env ctx con D (x,(l,A)::_) pot nil zC ext = E.error_label_missing_branch (l, ext)
  | check_branchesL trace env ctx con D (x,nil) pot ((l',ext',P)::_) zC ext = E.error_label_missing_alt (l', ext')

and plusL trace env ctx con D (A.Plus(choices)) pot (A.Case(x,branches)) zC ext (* z != x *) =
    check_branchesL trace env ctx con D (x,choices) pot branches zC ext
  | plusL trace env ctx con D A pot (A.Case(x,branches)) zC ext =
    ERROR ext ("type mismatch for " ^ x ^ ": expected internal choice, found: " ^ PP.pp_tp_compact env A)

and tensorR trace env ctx con D pot (A.Send(x,w,P)) (z,A.Tensor(A,B)) ext (* z = x *) =
    let val A' = TCU.lookup_context env w D ext
        val () = if TEQ.eq_tp env ctx con A A' then ()
                 else ERROR ext ("type of " ^ w ^ ": " ^ PP.pp_tp_compact env A ^
                                 " not equal " ^ PP.pp_tp_compact env A')
    in
    check_exp' trace env ctx con (TCU.remove_chan w D ext) pot P (z,B) ext
    end
  | tensorR trace env ctx con D pot (A.Send(x,w,P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected tensor, found: " ^ PP.pp_tp_compact env C)

and lolliL trace env ctx con D (A.Lolli(A,B)) pot (A.Send(x,w,Q)) zC ext (* z != x *) =
    let val A' = TCU.lookup_context env w D ext
        val () = if TEQ.eq_tp env ctx con A A' then ()
                 else ERROR ext ("type of " ^ w ^ ": " ^ PP.pp_tp_compact env A ^
                                 " not equal " ^ PP.pp_tp_compact env A')
    in
    check_exp' trace env ctx con (TCU.update_tp (x,B) (TCU.remove_chan w D ext)) pot Q zC ext
    end
  | lolliL trace env ctx con D A pot (A.Send(x,w,Q)) zC ext =
    ERROR ext ("type mismatch for " ^ x ^ ": expected lolli, found: " ^ PP.pp_tp_compact env A)

and lolliR trace env ctx con D pot (A.Recv(x,y,P)) (z,A.Lolli(A,B)) ext (* z = x *) =
    if exists_chan y ((z,A.Lolli(A,B))::D)
    then ERROR ext ("variable " ^ y ^ " not fresh")
    else check_exp' trace env ctx con ((y,A)::D) pot P (z,B) ext
  | lolliR trace env ctx con D pot (A.Recv(x,y,P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected lolli, found: " ^ PP.pp_tp_compact env C)

and tensorL trace env ctx con D (A.Tensor(A,B)) pot (A.Recv(x,y,Q)) zC ext (* z != x *) =
    if exists_chan y (zC::D)
    then ERROR ext ("variable " ^ y ^ " not fresh")
    else check_exp' trace env ctx con ((y,A)::(TCU.update_tp (x,B) D)) pot Q zC ext
  | tensorL trace env ctx con D A pot (A.Recv(x,y,Q)) zC ext =
    ERROR ext ("type mismatch for " ^ x ^ ": expected tensor, found: " ^ PP.pp_tp_compact env A)

and oneR trace env ctx con D pot (A.Close(x)) (z,A.One) ext (* z = x *) =
    if List.length D > 0
    then ERROR ext ("context " ^ PP.pp_context_compact env D ^ " not empty while closing")
    else if not (C.entails ctx con (R.Eq(pot, R.Int(0))))
    then ERROR ext ("unconsumed potential: " ^ C.pp_jfail con (R.Eq(pot, R.Int(0))))
    else ()
  | oneR trace env ctx con D pot (A.Close(x)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected one, found: " ^ PP.pp_tp_compact env C)

and oneL trace env ctx con D (A.One) pot (A.Wait(x,Q)) zC ext (* z != x *) =
    check_exp' trace env ctx con (TCU.remove_chan x D ext) pot Q zC ext
  | oneL trace env ctx con D A pot (A.Wait(x,Q)) zC ext =
    ERROR ext ("type mismatch for " ^ x ^ ": expected one, found: " ^ PP.pp_tp_compact env A)

and existsR trace env ctx con D pot (A.Assert(x,phi,P)) (z,A.Exists(phi',C)) ext (* z = x *) =
    if not (C.entails ctx con phi)
    then ERROR ext ("assertion not entailed: " ^ C.pp_jfail con phi)
    else if not (C.entails ctx con phi') (* equivalent would be con, phi |= phi' *)
    then ERROR ext ("type constraint not entailed: " ^ C.pp_jfail con phi')
    else check_exp' trace env ctx con D pot P (z,C) ext
  | existsR trace env ctx con D pot (A.Assert(x,phi,P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected exists, found: " ^ PP.pp_tp_compact env C)

and forallL trace env ctx con D (A.Forall(phi',A)) pot (A.Assert(x,phi,P)) zC ext (* z != x *) =
    if not (C.entails ctx con phi)
    then ERROR ext ("assertion not entailed: " ^ C.pp_jfail con phi)
    else if not (C.entails ctx con phi') (* equivalent would be con, phi |= phi' *)
    then ERROR ext ("type constraint not entailed: " ^ C.pp_jfail con phi')
    else check_exp' trace env ctx con (TCU.update_tp (x,A) D) pot P zC ext
  | forallL trace env ctx con D A pot (A.Assert(x,phi,P)) zC ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected forall, found: " ^ PP.pp_tp_compact env A)

and forallR trace env ctx con D pot (A.Assume(x,phi,P)) (z,A.Forall(phi',C)) ext (* z = x *) =
    if not (C.entails ctx (R.And(con,phi')) phi)
    then ERROR ext ("assumption not entailed: " ^ C.pp_jfail (R.And(con,phi')) phi)
    else check_exp' trace env ctx (R.And(con,phi)) D pot P (z,C) ext (* assume only the possibly weaker phi *)
 | forallR trace env ctx con D pot (A.Assume(x,phi,P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected forall, found: " ^ PP.pp_tp_compact env C)
  
and existsL trace env ctx con D (A.Exists(phi',A)) pot (A.Assume(x,phi,P)) zC ext (* z != x *) =
    if not (C.entails ctx (R.And(con,phi')) phi) (* con, phi' |= phi *)
    then ERROR ext ("assumption not entailed: " ^ C.pp_jfail (R.And(con,phi')) phi)
    else check_exp' trace env ctx (R.And(con,phi)) (TCU.update_tp (x,A) D) pot P zC ext (* assume the possibly weaker phi *)
  | existsL trace env ctx con D A pot (A.Assume(x,phi,P)) zC ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected exists, found: " ^ PP.pp_tp_compact env A)

and existsNatR trace env ctx con D pot (A.SendNat(x,e,P)) (z,A.ExistsNat(v,C)) ext (* z = x *) =
    check_exp' trace env ctx con D pot P (z, A.apply_tp (R.zip [v] [e]) C) ext
  | existsNatR trace env ctx con D pot (A.SendNat(x,e,P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected ?<id>._, found: " ^ PP.pp_tp_compact env C)

and forallNatL trace env ctx con D (A.ForallNat(v,A)) pot (A.SendNat(x,e,P)) zC ext (* z != x *) =
    check_exp' trace env ctx con (TCU.update_tp (x, A.apply_tp (R.zip [v] [e]) A) D) pot P zC ext
  | forallNatL trace env ctx con D A pot (A.SendNat(x,e,P)) zC ext (* z != x *) =
    ERROR ext ("type mismatch of " ^ x ^ ": expected !<id>._, found: " ^ PP.pp_tp_compact env A)

and forallNatR trace env ctx con D pot (A.RecvNat(x,v,P)) (z,A.ForallNat(v',C)) ext (* z = x *) =
    check_exp' trace env (v::ctx) con D pot P (z, A.apply_tp (R.zip [v'] [R.Var(v)]) C) ext
  | forallNatR trace env ctx con D pot (A.RecvNat(x,v,P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected !<id>._, found: " ^ PP.pp_tp_compact env C)

and existsNatL trace env ctx con D (A.ExistsNat(v',A)) pot (A.RecvNat(x,v,P)) zC ext (* z != x *) =
    check_exp' trace env (v::ctx) con (TCU.update_tp (x, A.apply_tp (R.zip [v'] [R.Var(v)]) A) D) pot P zC ext
  | existsNatL trace env ctx con D A pot (A.RecvNat(x,v,P)) zC ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected ?<id>._, found: " ^ PP.pp_tp_compact env A)

and work trace env ctx con D pot (A.Work(p,P)) zC ext =
    if not (C.entails ctx con (R.Ge(p,R.Int(0))))
    then ERROR ext ("potential not positive: " ^ C.pp_jfail con (R.Ge(p,R.Int(0))))
    else if not (C.entails ctx con (R.Ge(pot,p)))
    then ERROR ext ("insufficient potential: " ^ C.pp_jfail con (R.Ge (pot, p)))
    else check_exp' trace env ctx con D (R.minus(pot,p)) P zC ext

and paypotR trace env ctx con D pot (A.Pay(x,p',P)) (z,A.PayPot(p,C)) ext (* z = x *) =
    (* con |= p >= 0 since type is valid *)
    if not (C.entails ctx con (R.Ge(pot,p')))
    then ERROR ext ("insufficient potential: " ^ C.pp_jfail con (R.Ge(pot, p')))
    else if not (C.entails ctx con (R.Eq(p',p)))
    then ERROR ext ("potential mismatch: " ^ C.pp_jfail con (R.Eq(p',p)))
    else check_exp' trace env ctx con D (R.minus (pot,p)) P (z,C) ext
  | paypotR trace env ctx con D pot (A.Pay(x,p',P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected paypot, found: " ^ PP.pp_tp_compact env C)

and getpotL trace env ctx con D (A.GetPot(p,A)) pot (A.Pay(x,p',P)) zC ext (* z != x *) =
    (* con |= p >= 0 since type is valid *)
    if not (C.entails ctx con (R.Ge(pot,p)))
    then ERROR ext ("insufficient potential: " ^ C.pp_jfail con (R.Ge (pot, p)))
    else if not (C.entails ctx con (R.Eq(p,p')))
    then ERROR ext ("potential mismatch: " ^ C.pp_jfail con (R.Eq(p,p')))
    else check_exp' trace env ctx con (TCU.update_tp (x,A) D) (R.minus (pot,p)) P zC ext
  | getpotL trace env ctx con D A pot (A.Pay(x,p',P)) zC ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected getpot, found: " ^ PP.pp_tp_compact env A)

and getpotR trace env ctx con D pot (A.Get(x,p',P)) (z,A.GetPot(p,C)) ext (* z = x *) =
    (* con |= p >= 0 since type is valid *)
    if not (C.entails ctx con (R.Eq(p',p)))
    then ERROR ext ("potential mismatch: " ^ C.pp_jfail con (R.Eq(p',p)))
    else check_exp' trace env ctx con D (R.plus (pot,p)) P (z,C) ext
  | getpotR trace env ctx con D pot (A.Get(x,p',P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected paypot, found: " ^ PP.pp_tp_compact env C)

and paypotL trace env ctx con D (A.PayPot(p,A)) pot (A.Get(x,p',P)) zC ext (* z != x *) =
    (* con |= p >= 0 since type is valid *)
    if not (C.entails ctx con (R.Eq(p,p')))
    then ERROR ext ("potential mismatch: " ^ C.pp_jfail con (R.Eq(p,p')))
    else check_exp' trace env ctx con (TCU.update_tp (x,A) D) (R.plus (pot,p)) P zC ext
  | paypotL trace env ctx con D A pot (A.Get(x,p',P)) zC ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected getpot, found: " ^ PP.pp_tp_compact env A)

and delay trace env ctx con D pot (A.Delay(t,P)) (z,C) ext =
    if not(C.entails ctx con (R.Ge(t,R.Int(0))))
    then ERROR ext ("delay cannot be shown to be positive : " ^ C.pp_jfail con (R.Ge(t,R.Int(0))))
    else check_exp' trace env ctx con (TU.decrement env ctx con D t ext) pot P
                    (z,TU.decrementR env ctx con C t ext) ext

and diaR trace env ctx con D pot (A.Now(x,P)) (z,A.Dia(C)) ext (* z = x *) =
    check_exp' trace env ctx con D pot P (z,C) ext
  | diaR trace env ctx con D pot (A.Now(x,P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected diamond, found: " ^ PP.pp_tp_compact env C)

and boxL trace env ctx con D (A.Box(A)) pot (A.Now(x,P)) zC ext (* z != x *) =
    check_exp' trace env ctx con (TCU.update_tp (x,A) D) pot P zC ext
  | boxL trace env ctx con D A pot (A.Now(x,P)) zC ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected box, found: " ^ PP.pp_tp_compact env A)

and boxR trace env ctx con D pot (A.When(x,P)) (z,A.Box(C)) ext (* z = x *) =
    let val () = TU.eventually_box_ctx env D ext
    in
        check_exp' trace env ctx con D pot P (z,C) ext
    end
  | boxR trace env ctx con D pot (A.When(x,P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected box, found: " ^ PP.pp_tp_compact env C)

and diaL trace env ctx con D (A.Dia(A)) pot (A.When(x,P)) (z,C) ext (* z != x *) =
    let val () = if TU.eventually_dia env C then ()
                 else ERROR ext ("type " ^ PP.pp_tp_compact env C ^ " is not patient (ie, not (n)<>A")
    in
        check_exp' trace env ctx con (TCU.update_tp (x,A) D) pot P (z,C) ext
    end
  | diaL trace env ctx con D A pot (A.When(x,P)) (z,C) ext =
    ERROR ext ("type mismatch of " ^ x ^ ": expected diamond, found: " ^ PP.pp_tp_compact env A)

  (* judgmental constructs: id, cut, spawn, call *)
and check_exp trace env ctx con D pot (A.Id(x,y)) zC ext =
    fwd trace env ctx con D pot (A.Id(x,y)) zC ext
  | check_exp trace env ctx con D pot (A.Spawn(P,Q)) zC ext =
    spawn trace env ctx con D pot (A.Spawn(P,Q)) zC ext
  | check_exp trace env ctx con D pot (A.ExpName(x,f,es,xs)) (z,C) ext =
    expname trace env ctx con D pot (A.ExpName(x,f,es,xs)) (z,C) ext
    
  (* structural types +{...}, &{...}, 1 *)
  | check_exp trace env ctx con D pot (A.Lab(x,k,P)) (z,C) ext =
    if x = z
    then plusR trace env ctx con D pot (A.Lab(x,k,P)) (z,TU.expand env C) ext
    else withL trace env ctx con D (TCU.lookup_context env x D ext) pot (A.Lab(x,k,P)) (z,C) ext
  | check_exp trace env ctx con D pot (A.Case(x,branches)) (z,C) ext =
    if x = z
    then withR trace env ctx con D pot (A.Case(x,branches)) (z,TU.expand env C) ext
    else plusL trace env ctx con D (TCU.lookup_context env x D ext) pot (A.Case(x,branches)) (z,C) ext

  | check_exp trace env ctx con D pot (A.Send(x,w,P)) (z,C) ext =
    if x = z
    then tensorR trace env ctx con D pot (A.Send(x,w,P)) (z,TU.expand env C) ext
    else lolliL trace env ctx con D (TCU.lookup_context env x D ext) pot (A.Send(x,w,P)) (z,C) ext
  | check_exp trace env ctx con D pot (A.Recv(x,y,Q)) (z,C) ext =
    if x = z
    then lolliR trace env ctx con D pot (A.Recv(x,y,Q)) (z,TU.expand env C) ext
    else tensorL trace env ctx con D (TCU.lookup_context env x D ext) pot (A.Recv(x,y,Q)) (z,C) ext

  | check_exp trace env ctx con D pot (A.Close(x)) (z,C) ext =
    if x = z
    then oneR trace env ctx con D pot (A.Close(x)) (z,TU.expand env C) ext
    else ERROR ext ("name mismatch on right: " ^ x ^ " <> " ^ z)
  | check_exp trace env ctx con D pot (A.Wait(x,Q)) (z,C) ext =
    if x = z
    then ERROR ext ("name mismatch on left: " ^ x ^ " = " ^ z)
    else oneL trace env ctx con D (TCU.lookup_context env x D ext) pot (A.Wait(x,Q)) (z,C) ext

  (* quantified types ?{phi}.A, !{phi}.A *)
  | check_exp trace env ctx con D pot (A.Assert(x,phi,P)) (z,C) ext =
    if x = z
    then existsR trace env ctx con D pot (A.Assert(x,phi,P)) (z,TU.expand env C) ext
    else forallL trace env ctx con D (TCU.lookup_context env x D ext) pot (A.Assert(x,phi,P)) (z,C) ext
  | check_exp trace env ctx con D pot (A.Assume(x,phi,Q)) (z,C) ext =
    if x = z
    then forallR trace env ctx con D pot (A.Assume(x,phi,Q)) (z,TU.expand env C) ext
    else existsL trace env ctx con D (TCU.lookup_context env x D ext) pot (A.Assume(x,phi,Q)) (z,C) ext    

  (* quantified types ?v.A, !v.A *)
  | check_exp trace env ctx con D pot (A.SendNat(x,e,P)) (z,C) ext =
    if x = z
    then existsNatR trace env ctx con D pot (A.SendNat(x,e,P)) (z,TU.expand env C) ext
    else forallNatL trace env ctx con D (TCU.lookup_context env x D ext) pot (A.SendNat(x,e,P)) (z,C) ext
  | check_exp trace env ctx con D pot (A.RecvNat(x,v,P)) (z,C) ext =
    if x = z
    then forallNatR trace env ctx con D pot (A.RecvNat(x,v,P)) (z,TU.expand env C) ext
    else existsNatL trace env ctx con D (TCU.lookup_context env x D ext) pot (A.RecvNat(x,v,P)) (z,C) ext

  (* impossibility *)
  | check_exp trace env ctx con D pot (A.Imposs) zC ext =
    if not (C.contradictory ctx con R.True) (* TODO: fix interface *)
    then ERROR ext ("constraints not contradictory: " ^ C.pp_jsat con R.True)
    else ()

  (* ergometric types |>, <| *)
  | check_exp trace env ctx con D pot (A.Work(p,P)) zC ext =
    work trace env ctx con D pot (A.Work(p,P)) zC ext
  | check_exp trace env ctx con D pot (A.Pay(x,p',P)) (z,C) ext =
    if x = z
    then paypotR trace env ctx con D pot (A.Pay(x,p',P)) (z,TU.expand env C) ext
    else getpotL trace env ctx con D (TCU.lookup_context env x D ext) pot (A.Pay(x,p',P)) (z,C) ext
  | check_exp trace env ctx con D pot (A.Get(x,p',P)) (z,C) ext =
    if x = z
    then getpotR trace env ctx con D pot (A.Get(x,p',P)) (z,TU.expand env C) ext
    else paypotL trace env ctx con D (TCU.lookup_context env x D ext) pot (A.Get(x,p',P)) (z,C) ext

  (* temporal types (), [], <> *)
  | check_exp trace env ctx con D pot (A.Delay(t,P)) (z,C) ext =
    delay trace env ctx con D pot (A.Delay(t,P)) (z,C) ext
  
  | check_exp trace env ctx con D pot (A.Now(x,P)) (z,C) ext =
    if x = z
    then diaR trace env ctx con D pot (A.Now(x,P)) (z,TU.expand env C) ext
    else boxL trace env ctx con D (TCU.lookup_context env x D ext) pot (A.Now(x,P)) (z,C) ext
  | check_exp trace env ctx con D pot (A.When(x,P)) (z,C) ext =
    if x = z
    then boxR trace env ctx con D pot (A.When(x,P)) (z,TU.expand env C) ext
    else diaL trace env ctx con D (TCU.lookup_context env x D ext) pot (A.When(x,P)) (z,C) ext

  (* marked expressions *)
  | check_exp trace env ctx con D pot (A.Marked(marked_P)) zC ext =
    check_exp trace env ctx con D pot (Mark.data marked_P) zC (Mark.ext marked_P)

fun check_exp_top trace env ctx con D pot P zC ext =
    check_exp' trace env ctx con D pot P zC ext

(* external interface *)
fun check_exp trace env ctx con D pot P zC ext =
    check_exp_top trace env ctx con D pot P zC ext

end (* structure TypeCheck *)
