(* Elaboration *)

(*
 * Perform validity checks for types, reconstruction, type checking
 * and return an environment with elaborated declarations
 *
 * We use a two-pass algorithm.  In the first pass we check types
 * for validity and also create internal names following every
 * type constructor.  These internal names are used in the type
 * equality algorithm to detect cycles.
 *
 * Because we allow mutual recursion for both types and programs
 * many of the functions take an (unvarying) copy of the complete
 * environment in addition to the list of declarations to be elaborated.
 *)

signature ELAB =
sig

    (* elab_decls env decls = SOME(env') where decls are elaborated in
     * environment env (initially expected to be a copy of decls) *)
    val elab_decls : Ast.env -> Ast.decl list -> Ast.env option

    (* check_redecl env decls = () if there are no multiple declarations
     * for any type or process, otherwise raise ErrorMsg.Error *)
    val check_redecl : Ast.env -> Ast.decl list -> unit (* may raise ErrorMsg.Error *)

end (* signature ELAB *)

structure Elab :> ELAB =
struct

structure R = Arith
structure A = Ast
structure PP = PPrint
structure C = Constraints
structure TC = TypeCheck
structure AR = ARecon
(*
structure BR = BRecon
*)
structure QR = QRecon
structure WR = WRecon
(*
structure TR = TRecon
structure TRBT = TReconBT
structure TQR = TQRecon
*)
val ERROR = ErrorMsg.ERROR

fun postponed (A.Exec _) = "% "
  | postponed _ = ""

(*********************)
(* Validity of Types *)
(*********************)

(* constraints are valid if closed *)
fun valid_con env ctx con ext =
    ( TC.closed_prop ctx con ext )

(* valid left types are either empty (A.Dot)
 * or closed and valid *)
fun validL env ctx con [] ext = ()
  | validL env ctx con ((x,A)::D) ext =
    ( TC.closed_tp ctx A ext
    ; TC.valid env ctx con A ext
    ; validL env ctx con D ext )

(* valid right types are closed and valid *)
fun validR env ctx con A ext =
    ( TC.closed_tp ctx A ext
    ; TC.valid env ctx con A ext )

fun pp_costs () =
    "--work=" ^ Flags.pp_cost (!Flags.work) ^ " "
    ^ "--time=" ^ Flags.pp_cost (!Flags.time)

(* only for testing purposes *)
fun arecon env ctx con A pot P C ext =
    let val P' = AR.recon env ctx con A pot P C ext (* P' = P *)
    in P' end

(* quantifier reconstruction: first do approximate type checking *)
fun qrecon env ctx con A pot P C ext =
    let val P' = AR.recon env ctx con A pot P C ext (* P' = P *)
        (* add brecon here to simplify qrecon? *)
        val P'' = QR.recon env ctx con A pot P' C ext
    in P'' end

(* work reconstruction: first do quantifier reconstruction *)
fun wrecon env ctx con A pot P C ext =
    let val P = qrecon env ctx con A pot P C ext
        val P = Cost.apply_cost_work P
        val P = WR.recon env ctx con A pot P C ext
    in P end

(*
(* time reconstruction: first do quantifier reconstruction *)
fun trecon env ctx con A pot P C ext =
    let val P = qrecon env ctx con A pot P C ext
        val P = Cost.apply_cost_time P
        val P' = TR.recon env ctx con A pot P C ext 
        val _ = TRBT.recon env ctx con A pot P C ext (* redundant; to check backtracking reconstruction *)
    in P' end 

fun tqrecon env ctx con A pot P C ext =
    let val P = AR.recon env ctx con A pot P C ext 
        val P = BR.recon env ctx con A pot P C ext (* fill in missing branches *)
        val P = Cost.apply_cost_time P
        val P = TQR.recon env ctx con A pot P C ext
    in
        P
    end

fun twrecon env ctx con A pot P C ext =
    let val P = wrecon env ctx con A pot P C ext
        val P = Cost.apply_cost_time P
        val P' = TR.recon env ctx con A pot P C ext
        val _ = TRBT.recon env ctx con A pot P C ext (* redundant; to check backtracking reconstruction *)
    in P' end
*)

(* reconstruct syntax work time A pot P C ext = P'
 * where P' is the reconstructed version of P
 * syntax = explicit: just return P
 * syntax = implicit: reconstruct work and/or time based on values
 * of 'work' and 'time' (None: don't, otherwise do)
 * We assume the cost model has already been applied
 *)
fun reconstruct Flags.Explicit _          _          env ctx con A pot P C ext = Cost.apply_cost_model P
  | reconstruct Flags.Implicit Flags.None Flags.None env ctx con A pot P C ext = qrecon env ctx con A pot P C ext
  | reconstruct Flags.Implicit _          Flags.None env ctx con A pot P C ext = wrecon env ctx con A pot P C ext
  | reconstruct Flags.Implicit _          _          env ctx con A pot P C ext = ERROR ext ("only explicit syntax allowed")
(*
  | reconstruct Flags.Implicit Flags.None _          env ctx con A pot P C ext = tqrecon env ctx con A pot P C ext
  | reconstruct Flags.Implicit _          _          env ctx con A pot P C ext = twrecon env ctx con A pot P C ext
*)


(* dups vs = true if there is a duplicate variable in vs *)
fun dups (nil:R.varname list) = false
  | dups (v::vs) = List.exists (fn v' => v = v') vs orelse dups vs

(***************************)
(* Creating Internal Names *)
(***************************)

(* fresh typename generation *)
local
  val n = ref 0
in
  fun fresh_name () = "%" ^ Int.toString (!n) before n := !n+1
end

fun apply_fst f (A,env) = (f A, env)

fun exists (A.TpDef(a,vs,con,A,ext)) nil = false
  | exists (A.TpDef(a,vs,con,A,ext)) (A.TpDef(a',vs',con',A',ext')::env) =
    a = a' orelse exists (A.TpDef(a,vs,con,A,ext)) env

fun combine nil env = env
  | combine (decl::env1) env2 =
    if exists decl env2
    then combine env1 env2
    else combine env1 (decl::env2)

(* tp_naming ("type a = A") = env where env contains
 * a new definition "type a = A'" with A' == A and
 * also definitions for all internal names in A'
 *)
fun tp_naming (A.TpDef(a,vs,con,A,ext)) =
  let val (A',env) = tp_name_subtp vs con A []
  in
    A.TpDef(a,vs,con,A',ext)::env
  end

(* tp_name_subtp ctx con A env = (A', env')
 * assumes A neither empty nor name
 * A' == A uses internal names whose definitions are
 * added to env to yield env'
 *)
and tp_name_subtp ctx con (A.Plus(choices)) env = apply_fst A.Plus (tp_name_subchoices ctx con choices env)
  | tp_name_subtp ctx con (A.With(choices)) env = apply_fst A.With (tp_name_subchoices ctx con choices env)
  | tp_name_subtp ctx con (A.Tensor(A',B')) env =
      let val (nameB, envB) = tp_name_subtp' ctx con B' env
          val (nameA, envA) = tp_name_subtp' ctx con A' env
      in
      (A.Tensor(nameA, nameB), (combine envA envB))
      end
  | tp_name_subtp ctx con (A.Lolli(A',B')) env =
      let val (nameB, envB) = tp_name_subtp' ctx con B' env
          val (nameA, envA) = tp_name_subtp' ctx con A' env
      in
      (A.Lolli(nameA, nameB), (combine envA envB))
      end
  | tp_name_subtp ctx con (A.One) env = (A.One, env)
  | tp_name_subtp ctx con (A.Exists(phi,A')) env =
    apply_fst (fn A => (A.Exists(phi,A))) (tp_name_subtp' ctx (R.And(con,phi)) A' env)
  | tp_name_subtp ctx con (A.Forall(phi,A')) env =
    apply_fst (fn A => (A.Forall(phi,A))) (tp_name_subtp' ctx (R.And(con,phi)) A' env)
  | tp_name_subtp ctx con (A.ExistsNat(v,A')) env =
    apply_fst (fn A => (A.ExistsNat(v,A))) (tp_name_subtp' (v::ctx) con A' env)
  | tp_name_subtp ctx con (A.ForallNat(v,A')) env =
    apply_fst (fn A => (A.ForallNat(v,A))) (tp_name_subtp' (v::ctx) con A' env)
  | tp_name_subtp ctx con (A.PayPot(p,A')) env = apply_fst (fn A => (A.PayPot(p,A))) (tp_name_subtp' ctx con A' env)
  | tp_name_subtp ctx con (A.GetPot(p,A')) env = apply_fst (fn A => (A.GetPot(p,A))) (tp_name_subtp' ctx con A' env)
  | tp_name_subtp ctx con (A.Next(t,A')) env = apply_fst (fn A => (A.Next(t,A))) (tp_name_subtp' ctx con A' env)
  | tp_name_subtp ctx con (A.Box(A')) env = apply_fst A.Box (tp_name_subtp' ctx con A' env)
  | tp_name_subtp ctx con (A.Dia(A')) env = apply_fst A.Dia (tp_name_subtp' ctx con A' env)

and tp_name_subchoices ctx con nil env = (nil, env)
  | tp_name_subchoices ctx con ((l,A)::choices) env =
    let val (A',env') = tp_name_subtp' ctx con A env
        val (choices', env'') = tp_name_subchoices ctx con choices env'
    in
      ((l,A')::choices', env'')
    end

(* tp_name_subtp' ctx con A env = (A', env')
 * like tp_name_subtp except A may be a type name
 *)
and tp_name_subtp' ctx con (A as A.TpName(_,_)) env = (A, env)
  | tp_name_subtp' ctx con (A.One) env = (A.One, env)
  | tp_name_subtp' ctx con A env =
    let val (A', env') = tp_name_subtp ctx con A env
        val new_tpname = fresh_name ()
        val decl = A.TpDef(new_tpname,ctx,con,A',NONE)
    in
      (A.TpName(new_tpname, List.map (fn v => R.Var(v)) ctx), decl::env')
    end

(***************************)
(* Elaboration, First Pass *)
(***************************)

(* subst es (vs,con,(A,pot,C)) = [es/vs](con,(A,pot,C)) *)
(* requires |es| = |vs| *)
fun subst es (vs,con,(D,pot,(z,C))) =
    let
        val sg = R.zip vs es
    in
        (R.apply_prop sg con, (A.apply_context sg D, R.apply sg pot, (z,A.apply_tp sg C)))
    end

fun subst_chan (y,t) x = (x,t)

fun subst_chans (yt::D) (x::xs)  = (subst_chan yt x)::(subst_chans D xs)
  | subst_chans nil nil = nil

(* elab_tps env decls = env'
 * elaborates all type definitions in decls to generate env'
 * This checks them for validity and creates internal names.
 * Expressions are passed through unchanged, but process declarations
 * are checked for the validity of the types used.
 *)
fun elab_tps env nil = nil
  | elab_tps env ((decl as A.TpDef(a,vs,con,A,ext))::decls) =
    let
        val () = if !Flags.verbosity >= 1
                  then TextIO.print (postponed decl ^ PP.pp_decl env decl ^ "\n")
                  else ()
        val () = if dups vs then ERROR ext ("duplicate index variable in type definition") else ()
        val () = if Arith.closed_prop vs con then ()
                 else ERROR ext ("constraint " ^ PP.pp_prop con ^ " not closed")
        val () = validR env vs con A ext
        val () = if TC.contractive env A then () (* do not abbreviate type! *)
                 else ERROR ext ("type " ^ PP.pp_tp env A ^ " not contractive")
        val tp_defs = tp_naming decl
    in
         tp_defs @ elab_tps env decls
    end
  | elab_tps env ((decl as A.TpEq([],con,A as A.TpName(a,es),A' as A.TpName(a',es'),ext))::decls) =
    (* variables are implicitly quantified; collect here *)
    (* because we have not yet elaborated type definitions
     * we cannot check the equality here; wait for the second pass
     *)
    (* in current syntax, no explicit quantifiers and con = True *)
    let
        val () = if !Flags.verbosity >= 1
                 then TextIO.print (postponed decl ^ PP.pp_decl env decl ^ "\n")
                 else ()
        val ctx0 = R.free_prop con nil (* always nil, in current syntax *)
        val ctx1 = R.free_varlist es ctx0
        val ctx2 = R.free_varlist es' ctx1
        val () = TC.valid env ctx2 con A ext
        val () = TC.valid env ctx2 con A' ext
        val decl' = A.TpEq(ctx2,con,A,A',ext)
    in
        decl'::elab_tps env decls
    end
  | elab_tps env ((decl as A.ExpDec(f,vs,con,(D,pot,(z,C)),ext))::decls) =
    (* do not print process declaration so they are printed close to their use *)
    let
        val () = if dups vs then ERROR ext ("duplicate index variable in process declaration") else ()
        val () = valid_con env vs con ext
        val () = validL env vs con D ext
        val () = validR env vs con C ext
        val () = TC.closed vs pot ext
    in
        decl::elab_tps env decls
    end
  | elab_tps env (decl::decls) = decl::elab_tps env decls

(****************************)
(* Elaboration, Second Pass *)
(****************************)

val recon_time : LargeInt.int ref = ref (LargeInt.fromInt 0)
val tc_time : LargeInt.int ref = ref (LargeInt.fromInt 0)

(* elab_env env decls = env' if all declarations in decls
 * are well-typed with respect to env, elaborating to env'
 * raises exception otherwise.
 * Assumes that types have already been elaborated in the first pass
 *)
fun elab_exps' env nil = nil
  | elab_exps' env (decls as A.TpDef _::_) = (* do not print type definition again *)
    elab_exps env decls
  | elab_exps' env (decls as decl::_) =
    ( if !Flags.verbosity >= 1
      then TextIO.print (postponed decl ^ PP.pp_decl env decl ^ "\n")
      else () ;
      elab_exps env decls )
and elab_exps env nil = nil
  | elab_exps env ((decl as A.TpDef _)::decls) =
    (* already checked validity during first pass *)
    decl::elab_exps' env decls
  | elab_exps env ((decl as A.TpEq(ctx,con,A as A.TpName(a,es),A' as A.TpName(a',es'), ext))::decls) =
    (* already checked validity during first pass; now check type equality *)
    let
        val B = A.expd_tp env (a,es)
        val B' = A.expd_tp env (a',es')
        val () = if TC.eq_tp env ctx con B B'
                 then ()
                 else ERROR ext ("type " ^ PP.pp_tp env A ^ " not equal " ^ PP.pp_tp env A')
    in 
        decl::elab_exps' env decls
    end
  | elab_exps env ((decl as A.ExpDec _)::decls) =
    (* already checked validity during first pass *)
    decl::elab_exps' env decls
  | elab_exps env ((decl as A.ExpDef(f,vs,(xs,P,x),ext))::decls) =
    (case A.lookup_expdec env f
      of NONE => ERROR ext ("process " ^ f ^ " undeclared")
       | SOME(vs',con',(D',pot',zC')) =>
         let 
             val () = if dups vs then ERROR ext ("duplicate index variable in process definition") else ()
             val () = if List.length vs = List.length vs' then ()
                      else ERROR ext ("process defined with " ^ Int.toString (List.length vs) ^ " indices and "
                                      ^ "declared with " ^ Int.toString (List.length vs'))
             val () = if List.length xs = List.length D' then ()
                      else ERROR ext ("process defined with " ^ Int.toString (List.length xs) ^ " arguments and "
                                      ^ "declared with " ^ Int.toString (List.length D'))
             val (con, (D,pot,zC)) = subst (R.create_idx vs) (vs',con',(D',pot',zC'))
             val (D,zC) = (subst_chans D xs, subst_chan zC x)
             val () = TC.closed_exp vs P ext
             (* val P' = Cost.apply_cost_model P *) (* cost model now applied during reconstruction *)
             val trecon_init = Time.toMicroseconds (Time.now ())
             val P' = reconstruct (!Flags.syntax) (!Flags.work) (!Flags.time) env vs con D pot P zC ext
             val trecon_final = Time.toMicroseconds (Time.now ())
             val trecon = trecon_final - trecon_init
             val () = recon_time := !recon_time + trecon
             val () = case !Flags.syntax                     (* print reconstructed term *)
                       of Flags.Implicit =>                  (* if syntax implicit *)
                          if !Flags.verbosity >= 2           (* and verbose *)
                          then ( TextIO.print ("% after reconstruction with cost model " ^ pp_costs () ^ "\n")
                               ; TextIO.print (PP.pp_decl env (A.ExpDef(f,vs,(xs,P',x),ext)) ^ "\n") )
                          else ()
                        | Flags.Explicit => (* maybe only if there is a cost model... *)
                          if !Flags.verbosity >= 2
                          then ( TextIO.print ("% with cost model " ^ pp_costs () ^ "\n")
                               ; TextIO.print (PP.pp_decl env (A.ExpDef(f,vs,(xs,P',x),ext)) ^ "\n") )
                          else ()
             (* is necessary for implicit syntax, since reconstruction is approximate *)
             val tc_init = Time.toMicroseconds (Time.now ())
             val () = TC.check_exp false env vs con D pot P' zC ext (* type check *)
                 handle ErrorMsg.Error =>
                        (* if verbosity >= 2, type-check again, this time with tracing *)
                        if !Flags.verbosity >= 2
                        then ( TextIO.print ("% tracing type checking...\n")
                             ; TC.check_exp true env vs con D pot P' zC ext ) (* will re-raise ErrorMsg.Error *)
                        else raise ErrorMsg.Error (* re-raise if not in verbose mode *)
             val tc_final = Time.toMicroseconds (Time.now ())
             val tc = tc_final - tc_init
             val () = tc_time := !tc_time + tc
             val P' = A.strip_exts P' (* always strip extents whether implicit or explicit syntax *)
         in
             A.ExpDef(f,vs,(xs,P',x),ext)::elab_exps' env decls
         end)
  | elab_exps env ((decl as A.Exec(f,ext))::decls) =
    (case A.lookup_expdef env f
      of SOME(vs,P) => A.Exec(f,ext)::elab_exps' env decls
       | NONE => ERROR ext ("process " ^ f ^ " undefined"))
  | elab_exps env ((decl as A.Pragma(p,line,ext))::decls) =
    ERROR ext ("unexpected pragma:\n" ^ PP.pp_decl env decl ^ "\n"
               ^ "pragmas must precede all other declarations\n")

(* elab_decls env decls = SOME(env')
 * if elaboration of decls succeeds with respect to env, yielding env'
 * Returns NONE if there is a static error
 *)
fun elab_decls env decls =
    let
        (* first pass: check validity of types and create internal names *)
        val env' = elab_tps env decls
        (* second pass: perform reconstruction and type checking *)
        (* pass env' which has types with internal names as first argument *)
        val env'' = elab_exps' env' env'
        val () = if !Flags.verbosity = ~1 then TextIO.print "\n" else ()
        val () = if !Flags.verbosity = ~1 orelse !Flags.verbosity >= 2
                 then ( TextIO.print ("% recon time: " ^ LargeInt.toString (!recon_time) ^ " us\n")
                      ; TextIO.print ("% check time: " ^ LargeInt.toString (!tc_time) ^ " us\n") )
                 else ()
        (*
        val () = case !Flags.terminate
                  of NONE => ()
                   | SOME(recursion) => Termination.terminates env'' env'' (* check termination on elaborated form *)
        *)
    in
        SOME(env'')
    end
    handle ErrorMsg.Error => NONE

(**************************)
(* Checking Redeclaration *)
(**************************)

(* Because of mutual recursion, we cannot redefine or
 * redeclare types or processes
 *)

fun is_tpdef env a = case A.lookup_tp env a of NONE => false | SOME _ => true
fun is_expdec env f = case A.lookup_expdec env f of NONE => false | SOME _ => true
fun is_expdef env f = case A.lookup_expdef env f of NONE => false | SOME _ => true

fun check_redecl env nil = ()
  | check_redecl env (A.TpDef(a,_,_,_,ext)::decls) =
    if is_tpdef env a orelse is_tpdef decls a
    then ERROR ext ("type name " ^ a ^ " defined more than once")
    else check_redecl env decls
  | check_redecl env (A.ExpDec(f,_,_,_,ext)::decls) =
    if is_expdec env f orelse is_expdec decls f
    then ERROR ext ("process name " ^ f ^ " declared more than once")
    else check_redecl env decls
  | check_redecl env (A.ExpDef(f,_,_,ext)::decls) =
    if is_expdef env f orelse is_expdef decls f
    then ERROR ext ("process name " ^ f ^ " defined more than once")
    else check_redecl env decls
  | check_redecl env (_::decls) = check_redecl env decls

end (* structure Elab *)
