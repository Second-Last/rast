(* Elaboration *)

(* Authors: Ankush Das <ankushd@cs.cmu.edu>
 *          Frank Pfenning <fp@cs.cmu.edu>
 *)

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
structure E = TpError
structure TV = TypeValid
structure TEQ = TypeEquality
structure TC = TypeCheck
structure AR = ARecon
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
    ( TV.closed_prop ctx con ext )

(* valid left types are closed and valid *)
fun validL env tpctx ctx con [] ext = ()
  | validL env tpctx ctx con ((x,A)::D) ext =
    ( TV.closed_tp tpctx ctx A ext
    ; TV.valid env tpctx ctx con A ext
    ; validL env tpctx ctx con D ext )

(* valid right types are closed and valid *)
fun validR env tpctx ctx con A ext =
    ( TV.closed_tp tpctx ctx A ext
    ; TV.valid env tpctx ctx con A ext )

fun pp_costs () =
    "--work=" ^ Flags.pp_cost (!Flags.work) ^ " "
    ^ "--time=" ^ Flags.pp_cost (!Flags.time)

(* quantifier reconstruction: first do approximate type checking *)
fun qrecon env ctx con A pot P C ext =
    let val P' = AR.recon env ctx con A pot P C ext (* P' = P *)
        val P'' = QR.recon env ctx con A pot P' C ext
    in P'' end

(* work reconstruction: first do quantifier reconstruction *)
fun wrecon env ctx con A pot P C ext =
    let val P = qrecon env ctx con A pot P C ext
        val P = Cost.apply_cost_work P
        val P = WR.recon env ctx con A pot P C ext
    in P end

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

(* dups vs = true if there is a duplicate variable in vs *)
fun dups (nil:R.varname list) = false
  | dups (v::vs) = List.exists (fn v' => v = v') vs orelse dups vs

(*******************)
(* Resolving Names *)
(*******************)

(* recognize local type variables vs global type definitions *)

fun resolve tpctx (A.Plus(choices)) = A.Plus(resolve_choices tpctx choices)
  | resolve tpctx (A.With(choices)) = A.With(resolve_choices tpctx choices)
  | resolve tpctx (A.Tensor(A,B)) = A.Tensor(resolve tpctx A, resolve tpctx B)
  | resolve tpctx (A.Lolli(A,B)) = A.Lolli(resolve tpctx A, resolve tpctx B)
  | resolve tpctx (A.One) = A.One
  | resolve tpctx (A.Exists(phi,A)) = A.Exists(phi,resolve tpctx A)
  | resolve tpctx (A.Forall(phi,A)) = A.Forall(phi,resolve tpctx A)
  | resolve tpctx (A.ExistsNat(v,A)) = A.ExistsNat(v,resolve tpctx A)
  | resolve tpctx (A.ForallNat(v,A)) = A.ForallNat(v,resolve tpctx A)
  | resolve tpctx (A.PayPot(p,A)) = A.PayPot(p,resolve tpctx A)
  | resolve tpctx (A.GetPot(p,A)) = A.GetPot(p,resolve tpctx A)
  | resolve tpctx (A.Next(t,A)) = A.Next(t,resolve tpctx A)
  | resolve tpctx (A.Dia(A)) = A.Dia(resolve tpctx A)
  | resolve tpctx (A.Box(A)) = A.Box(resolve tpctx A)
  | resolve tpctx (A.TpName(a,nil,nil)) =
    (* type parameters cannot have any arguments, at present *)
    (* they may shadow global definitions *)
    if List.exists (fn alpha => a = alpha) tpctx
    then A.TpVar(a)
    else A.TpName(a,nil,nil)
  | resolve tpctx (A.TpName(a,As,es)) =
    A.TpName(a, List.map (fn A => resolve tpctx A) As, es)
  (* A.TpVar should be impossible since it is never generated by the parser *)
and resolve_choices tpctx nil = nil
  | resolve_choices tpctx ((l,A)::choices) =
    (l, resolve tpctx A)::resolve_choices tpctx choices

fun valid_args env tpctx vs (A.Plus(choices)) ext = valid_args_choices env tpctx vs choices ext
  | valid_args env tpctx vs (A.With(choices)) ext = valid_args_choices env tpctx vs choices ext
  | valid_args env tpctx vs (A.Tensor(A,B)) ext = ( valid_args env tpctx vs A ext ; valid_args env tpctx vs B ext )
  | valid_args env tpctx vs (A.Lolli(A,B)) ext = ( valid_args env tpctx vs A ext ; valid_args env tpctx vs B ext )
  | valid_args env tpctx vs (A.One) ext = ()
  | valid_args env tpctx vs (A.Exists(phi,A)) ext = valid_args env tpctx vs A ext
  | valid_args env tpctx vs (A.Forall(phi,A)) ext = valid_args env tpctx vs A ext
  | valid_args env tpctx vs (A.ExistsNat(v,A)) ext = valid_args env tpctx vs A ext
  | valid_args env tpctx vs (A.ForallNat(v,A)) ext = valid_args env tpctx vs A ext
  | valid_args env tpctx vs (A.PayPot(p,A)) ext = valid_args env tpctx vs A ext
  | valid_args env tpctx vs (A.GetPot(p,A)) ext = valid_args env tpctx vs A ext
  | valid_args env tpctx vs (A.Next(t,A)) ext = valid_args env tpctx vs A ext
  | valid_args env tpctx vs (A.Dia(A)) ext = valid_args env tpctx vs A ext
  | valid_args env tpctx vs (A.Box(A)) ext = valid_args env tpctx vs A ext
  | valid_args env tpctx vs (A.TpVar(alpha)) ext = ()
  | valid_args env tpctx vs (A.TpName(a,As,es)) ext =
    ( case A.lookup_tp env a
       of SOME(alphas', vs', con', _) =>
          ( if List.length alphas' = List.length As then ()
            else E.error_tparam_number ("parameterized type " ^ a) (List.length alphas', List.length As) ext
          ; if List.length vs' = List.length es then ()
            else E.error_index_number ("indexed type" ^ a) (List.length vs', List.length es) ext )
        | NONE => ERROR ext ("type " ^ a ^ " undefined")
    ; List.app (fn A => valid_args env tpctx vs A ext) As )
and valid_args_choices env tpctx vs nil ext = ()
  | valid_args_choices env tpctx vs ((l,A)::choices) ext =
    ( valid_args env tpctx vs A ext ; valid_args_choices env tpctx vs choices ext )

fun resolve_args env tpctx vs A ext =
    let val A' = resolve tpctx A
        val () = valid_args env tpctx vs A' ext
    in A' end

fun resolve_exp env tpctx vs (A as A.Id(x,y)) ext = A
  | resolve_exp env tpctx vs (A.Spawn(P,Q)) ext = A.Spawn (resolve_exp env tpctx vs P ext, resolve_exp env tpctx vs Q ext)
  | resolve_exp env tpctx vs (A.ExpName(x,f,As,es,ys)) ext =
    A.ExpName(x,f,List.map (fn A => resolve_args env tpctx vs A ext) As,es,ys)
  | resolve_exp env tpctx vs (A.Lab(x,k,P)) ext = A.Lab(x,k,resolve_exp env tpctx vs P ext)
  | resolve_exp env tpctx vs (A.Case(x,branches)) ext = A.Case(x,resolve_branches env tpctx vs branches ext)
  | resolve_exp env tpctx vs (A.Send(x,w,P)) ext = A.Send(x,w,resolve_exp env tpctx vs P ext)
  | resolve_exp env tpctx vs (A.Recv(x,y,P)) ext = A.Recv(x,y,resolve_exp env tpctx vs P ext)
  | resolve_exp env tpctx vs (A as A.Close(x)) ext = A
  | resolve_exp env tpctx vs (A.Wait(x,P)) ext = A.Wait(x,resolve_exp env tpctx vs P ext)
  | resolve_exp env tpctx vs (A.Assert(x,phi,P)) ext = A.Assert(x,phi,resolve_exp env tpctx vs P ext)
  | resolve_exp env tpctx vs (A.Assume(x,phi,P)) ext = A.Assume(x,phi,resolve_exp env tpctx vs P ext)
  | resolve_exp env tpctx vs (A.SendNat(x,e,P)) ext = A.SendNat(x,e,resolve_exp env tpctx vs P ext)
  | resolve_exp env tpctx vs (A.RecvNat(x,v,P)) ext = A.RecvNat(x,v,resolve_exp env tpctx vs P ext)
  | resolve_exp env tpctx vs (A as A.Imposs) ext = A
  | resolve_exp env tpctx vs (A.Work(p,P)) ext = A.Work(p,resolve_exp env tpctx vs P ext)
  | resolve_exp env tpctx vs (A.Pay(x,p,P)) ext = A.Pay(x,p,resolve_exp env tpctx vs P ext)
  | resolve_exp env tpctx vs (A.Get(x,p,P)) ext = A.Get(x,p,resolve_exp env tpctx vs P ext)
  | resolve_exp env tpctx vs (A.Delay(t,P)) ext = A.Delay(t,resolve_exp env tpctx vs P ext)
  | resolve_exp env tpctx vs (A.Now(x,P)) ext = A.Now(x,resolve_exp env tpctx vs P ext)
  | resolve_exp env tpctx vs (A.When(x,P)) ext = A.When(x,resolve_exp env tpctx vs P ext)
  | resolve_exp env tpctx vs (A.Marked(marked_P)) ext =
    A.Marked(Mark.mark' (resolve_exp env tpctx vs (Mark.data marked_P) (Mark.ext marked_P),
                         Mark.ext marked_P))
and resolve_branches env tpctx vs branches ext =
    List.map (fn (l,ext',P) => (l,ext,resolve_exp env tpctx vs P ext')) branches

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

fun exists (A.TpDef(a,alphas,vs,con,A,ext)) nil = false
  | exists (A.TpDef(a,alphas,vs,con,A,ext)) (A.TpDef(a',alphas',vs',con',A',ext')::env) =
    a = a' orelse exists (A.TpDef(a,alphas,vs,con,A,ext)) env

fun combine nil env = env
  | combine (decl::env1) env2 =
    if exists decl env2
    then combine env1 env2
    else combine env1 (decl::env2)

(* tp_naming ("type a = A") = env where env contains
 * a new definition "type a = A'" with A' == A and
 * also definitions for all internal names in A'
 *)
fun tp_naming (A.TpDef(a,alphas,vs,con,A,ext)) =
  let val (A',env) = tp_name_subtp alphas vs con A []
  in
    A.TpDef(a,alphas,vs,con,A',ext)::env
  end

(* tp_name_subtp ctx con A env = (A', env')
 * assumes A neither empty nor name
 * A' == A uses internal names whose definitions are
 * added to env to yield env'
 *)
and tp_name_subtp tpctx ctx con (A.Plus(choices)) env =
    apply_fst A.Plus (tp_name_subchoices tpctx ctx con choices env)
  | tp_name_subtp tpctx ctx con (A.With(choices)) env =
    apply_fst A.With (tp_name_subchoices tpctx ctx con choices env)
  | tp_name_subtp tpctx ctx con (A.Tensor(A',B')) env =
      let val (nameB, envB) = tp_name_subtp' tpctx ctx con B' env
          val (nameA, envA) = tp_name_subtp' tpctx ctx con A' env
      in
      (A.Tensor(nameA, nameB), (combine envA envB))
      end
  | tp_name_subtp tpctx ctx con (A.Lolli(A',B')) env =
      let val (nameB, envB) = tp_name_subtp' tpctx ctx con B' env
          val (nameA, envA) = tp_name_subtp' tpctx ctx con A' env
      in
      (A.Lolli(nameA, nameB), (combine envA envB))
      end
  | tp_name_subtp tpctx ctx con (A.One) env = (A.One, env)
  | tp_name_subtp tpctx ctx con (A.Exists(phi,A')) env =
    apply_fst (fn A => (A.Exists(phi,A))) (tp_name_subtp' tpctx ctx (R.And(con,phi)) A' env)
  | tp_name_subtp tpctx ctx con (A.Forall(phi,A')) env =
    apply_fst (fn A => (A.Forall(phi,A))) (tp_name_subtp' tpctx ctx (R.And(con,phi)) A' env)
  | tp_name_subtp tpctx ctx con (A.ExistsNat(v,A')) env =
    apply_fst (fn A => (A.ExistsNat(v,A))) (tp_name_subtp' tpctx (v::ctx) con A' env)
  | tp_name_subtp tpctx ctx con (A.ForallNat(v,A')) env =
    apply_fst (fn A => (A.ForallNat(v,A))) (tp_name_subtp' tpctx (v::ctx) con A' env)
  | tp_name_subtp tpctx ctx con (A.PayPot(p,A')) env =
    apply_fst (fn A => (A.PayPot(p,A))) (tp_name_subtp' tpctx ctx con A' env)
  | tp_name_subtp tpctx ctx con (A.GetPot(p,A')) env =
    apply_fst (fn A => (A.GetPot(p,A))) (tp_name_subtp' tpctx ctx con A' env)
  | tp_name_subtp tpctx ctx con (A.Next(t,A')) env =
    apply_fst (fn A => (A.Next(t,A))) (tp_name_subtp' tpctx ctx con A' env)
  | tp_name_subtp tpctx ctx con (A.Box(A')) env = apply_fst A.Box (tp_name_subtp' tpctx ctx con A' env)
  | tp_name_subtp tpctx ctx con (A.Dia(A')) env = apply_fst A.Dia (tp_name_subtp' tpctx ctx con A' env)
  | tp_name_subtp tpctx ctx con (A.TpVar(alpha)) env = (A.TpVar(alpha), env)

and tp_name_subchoices tpctx ctx con nil env = (nil, env)
  | tp_name_subchoices tpctx ctx con ((l,A)::choices) env =
    let val (A',env') = tp_name_subtp' tpctx ctx con A env
        val (choices', env'') = tp_name_subchoices tpctx ctx con choices env'
    in
      ((l,A')::choices', env'')
    end

(* tp_name_subtp' tpctx ctx con A env = (A', env')
 * like tp_name_subtp except A may be a type name
 * Still need a new internal name above a type variables
 * for correct substitution, so they are not singled out here
 *)
and tp_name_subtp' tpctx ctx con (A as A.TpName(_,_,_)) env = (A, env)
  | tp_name_subtp' tpctx ctx con (A.One) env = (A.One, env)
  | tp_name_subtp' tpctx ctx con A env =
    let val (A', env') = tp_name_subtp tpctx ctx con A env
        val new_tpname = fresh_name ()
        val decl = A.TpDef(new_tpname,tpctx,ctx,con,A',NONE) (* we take here all type variables *)
    in
      (A.TpName(new_tpname, List.map A.TpVar tpctx, List.map R.Var ctx), decl::env')
    end

(***************************)
(* Elaboration, First Pass *)
(***************************)

fun id_tp_subst alphas = List.map A.TpVar alphas

(* subst As es (alphas,vs,con,(A,pot,C)) = [As/alphas][es/vs](con,(A,pot,C)) *)
(* requires |es| = |vs|, |As| = |alphas|  *)
fun subst As es (alphas,vs,con,(D,pot,(z,C))) =
    let
        val theta = ListPair.zipEq (alphas, As)
        val sg = R.zip vs es
        val con' = R.apply_prop sg con
        val D' = A.subst_context theta (A.apply_context sg D)
        val pot' = R.apply sg pot
        val C' = A.subst_tp theta (A.apply_tp sg C)
    in
        (con', (D', pot', (z,C')))
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
  | elab_tps env ((decl as A.TpDef(a,alphas,vs,con,A,ext))::decls) =
    let
        val () = if !Flags.verbosity >= 1
                  then TextIO.print (postponed decl ^ PP.pp_decl env decl ^ "\n")
                  else ()
        val () = if dups alphas then ERROR ext ("duplicate type parameter in type definition") else ()
        val () = if dups vs then ERROR ext ("duplicate index variable in type definition") else ()
        val () = if Arith.closed_prop vs con then ()
                 else ERROR ext ("constraint " ^ PP.pp_prop con ^ " not closed")
        val A' = resolve alphas A
        val () = validR env alphas vs con A' ext
        val () = if TV.contractive env A' then () (* do not abbreviate type! *)
                 else ERROR ext ("type " ^ PP.pp_tp env A' ^ " not contractive")
        val decl' = A.TpDef(a,alphas,vs,con,A',ext)
        val tp_defs = tp_naming decl'
    in
         tp_defs @ elab_tps env decls
    end
  | elab_tps env ((decl as A.TpEq([],con,A as A.TpName(a,As,es),A' as A.TpName(a',As',es'),ext))::decls) =
    (* variables are implicitly quantified; collect here *)
    (* because we have not yet elaborated type definitions
     * we cannot check the equality here; wait for the second pass
     *)
    (* in current syntax, no explicit quantifiers and con = True *)
    (* also no free type variables allowed *)
    let
        val () = if !Flags.verbosity >= 1
                 then TextIO.print (postponed decl ^ PP.pp_decl env decl ^ "\n")
                 else ()
        val ctx0 = R.free_prop con nil (* always nil, in current syntax *)
        val ctx1 = R.free_varlist es ctx0
        val ctx2 = R.free_varlist es' ctx1
        val () = TV.valid env [] ctx2 con A ext
        val () = TV.valid env [] ctx2 con A' ext
        val decl' = A.TpEq(ctx2,con,A,A',ext)
    in
        decl'::elab_tps env decls
    end
  | elab_tps env ((decl as A.ExpDec(f,alphas,vs,con,(D,pot,(z,C)),ext))::decls) =
    (* do not print process declaration so they are printed close to their use *)
    (* check for duplicates and validity *)
    let
        val () = if dups alphas then ERROR ext ("duplicate type parameter in process declaration") else ()
        val chs = z::List.map (fn (y,_) => y) D
        val () = if dups chs then ERROR ext ("duplicate variable in process declaration") else ()
        val () = if dups vs then ERROR ext ("duplicate index variable in process declaration") else ()
        val D' = List.map (fn (x,A) => (x,resolve alphas A)) D
        val C' = resolve alphas C
        val () = valid_con env vs con ext
        val () = validL env alphas vs con D' ext
        val () = validR env alphas vs con C' ext
        val () = TV.closed vs pot ext
        val decl' = A.ExpDec(f,alphas,vs,con,(D',pot,(z,C')),ext)
    in
        decl'::elab_tps env decls
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
  | elab_exps env ((decl as A.TpEq(ctx,con,A as A.TpName(a,As,es),A' as A.TpName(a',As',es'), ext))::decls) =
    (* already checked validity during first pass; now check type equality *)
    let
        val B = A.expd_tp env (a,As,es)
        val B' = A.expd_tp env (a',As',es')
        val () = if TEQ.eq_tp env ctx con B B'
                 then ()
                 else ERROR ext ("type " ^ PP.pp_tp env A ^ " not equal " ^ PP.pp_tp env A')
    in 
        decl::elab_exps' env decls
    end
  | elab_exps env ((decl as A.ExpDec _)::decls) =
    (* already checked validity during first pass *)
    decl::elab_exps' env decls
  | elab_exps env ((decl as A.ExpDef(f,alphas,vs,(xs,P,x),ext))::decls) =
    (* type check the process now *)
    (case A.lookup_expdec env f
      of NONE => ERROR ext ("process " ^ f ^ " undeclared")
       | SOME(alphas',vs',con',(D',pot',zC')) =>
         (* check validity, duplicates, corresponds with the declaration *)
         let
             val () = if dups (x::xs) then ERROR ext ("duplicate variable in process definition") else ()
             val () = if dups alphas then ERROR ext ("duplicate type parameter in process definition") else ()
             val () = if dups vs then ERROR ext ("duplicate index variable in process definition") else ()
             val () = if List.length alphas = List.length alphas' then ()
                      else E.error_tparam_number "process definition" (List.length alphas', List.length alphas) ext
             val () = if List.length vs = List.length vs' then ()
                      else E.error_index_number "process definition" (List.length vs', List.length vs) ext
             val () = if List.length xs = List.length D' then ()
                      else E.error_channel_number "Process definition" (List.length D', List.length xs) ext
             val P' = resolve_exp env alphas vs P ext
             val () = TV.closed_exp alphas vs P' ext
             (* substitution in the declaration *)
             val (con, (D,pot,zC)) = subst (id_tp_subst alphas) (R.create_idx vs) (alphas', vs',con',(D',pot',zC'))
             val (D,zC) = (subst_chans D xs, subst_chan zC x)
             (* cost model now applied during reconstruction *)
             val trecon_init = Time.toMicroseconds (Time.now ())
             (* reconstruction will insert assert, assume, pay, get, work *)
             val P'' = reconstruct (!Flags.syntax) (!Flags.work) (!Flags.time) env vs con D pot P' zC ext
             val trecon_final = Time.toMicroseconds (Time.now ())
             val trecon = trecon_final - trecon_init
             val () = recon_time := !recon_time + trecon
             val () = case !Flags.syntax                     (* print reconstructed term *)
                       of Flags.Implicit =>                  (* if syntax implicit *)
                          if !Flags.verbosity >= 2           (* and verbose *)
                          then ( TextIO.print ("% after reconstruction with cost model " ^ pp_costs () ^ "\n")
                               ; TextIO.print (PP.pp_decl env (A.ExpDef(f,alphas,vs,(xs,P'',x),ext)) ^ "\n") )
                          else ()
                        | Flags.Explicit => (* maybe only if there is a cost model... *)
                          if !Flags.verbosity >= 2
                          then ( TextIO.print ("% with cost model " ^ pp_costs () ^ "\n")
                               ; TextIO.print (PP.pp_decl env (A.ExpDef(f,alphas,vs,(xs,P'',x),ext)) ^ "\n") )
                          else ()
             (* is necessary for implicit syntax, since reconstruction is approximate *)
             val tc_init = Time.toMicroseconds (Time.now ())
             (* type check now *)
             val () = TC.check_exp false env vs con D pot P'' zC ext (* type check *)
                 handle ErrorMsg.Error =>
                        (* if verbosity >= 2, type-check again, this time with tracing *)
                        if !Flags.verbosity >= 2
                        then ( TextIO.print ("% tracing type checking...\n")
                             ; TC.check_exp true env vs con D pot P'' zC ext ) (* will re-raise ErrorMsg.Error *)
                        else raise ErrorMsg.Error (* re-raise if not in verbose mode *)
             val tc_final = Time.toMicroseconds (Time.now ())
             val tc = tc_final - tc_init
             val () = tc_time := !tc_time + tc
         in
             A.ExpDef(f,alphas,vs,(xs,P'',x),ext)::elab_exps' env decls
         end)
  | elab_exps env ((decl as A.Exec(f,ext))::decls) =
    (case A.lookup_expdef env f
      of SOME([],[],([],P,x)) => A.Exec(f,ext)::elab_exps' env decls
         (* cannot run processes with non-empty context *)
       | SOME(alphas,vs,(ys,P,x)) => ERROR ext ("process " ^ f ^ " with non-empty context")
       | NONE => ERROR ext ("process " ^ f ^ " undefined"))
  | elab_exps env ((decl as A.Pragma(p,line,ext))::decls) =
    ERROR ext ("unexpected pragma:\n" ^ PP.pp_decl env decl ^ "\n"
               ^ "pragmas must precede all other declarations\n")

(* elab_decls env decls = SOME(env')
 * if elaboration of decls succeeds with respect to env, yielding env'
 * Returns NONE if there is a static error
 *)
fun elab_decls env decls =
    (* first pass: check validity of types and create internal names *)
    let val () = recon_time := LargeInt.fromInt 0
        val () = tc_time := LargeInt.fromInt 0
        val env' = elab_tps env decls
        val () = PP.Abbrev.reset ()
        (* second pass: perform reconstruction and type checking *)
        (* pass env' which has types with internal names as first argument *)
        val env'' = elab_exps' env' env'
        val () = if !Flags.verbosity >= 2 then List.app (fn decl => TextIO.print (A.Print.pp_decl decl ^ "\n")) env'' else ()
        val () = if !Flags.verbosity = ~1 then TextIO.print "\n" else ()
        val () = if !Flags.verbosity = ~1 orelse !Flags.verbosity >= 2
                 then ( TextIO.print ("% recon time: " ^ LargeInt.toString (!recon_time) ^ " us\n")
                      ; TextIO.print ("% check time: " ^ LargeInt.toString (!tc_time) ^ " us\n") )
                 else ()
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
  | check_redecl env (A.TpDef(a,_,_,_,_,ext)::decls) =
    if is_tpdef env a orelse is_tpdef decls a
    then ERROR ext ("type name " ^ a ^ " defined more than once")
    else check_redecl env decls
  | check_redecl env (A.ExpDec(f,_,_,_,_,ext)::decls) =
    if is_expdec env f orelse is_expdec decls f
    then ERROR ext ("process name " ^ f ^ " declared more than once")
    else check_redecl env decls
  | check_redecl env (A.ExpDef(f,_,_,_,ext)::decls) =
    if is_expdef env f orelse is_expdef decls f
    then ERROR ext ("process name " ^ f ^ " defined more than once")
    else check_redecl env decls
  | check_redecl env (_::decls) = check_redecl env decls

end (* structure Elab *)
