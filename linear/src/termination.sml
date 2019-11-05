signature TERMINATION =
sig

    val terminates : Ast.env -> Ast.decl list -> unit
    (* may raise ErrorMsg.Error *)
    
end

structure Termination :> TERMINATION =
struct

structure R = Arith
structure A = Ast
structure P = Ast.Print
structure PP = PPrint
structure C = Constraints
structure TC = TypeCheck
val ERROR = ErrorMsg.ERROR
datatype ductivity = CO | IND

datatype polarity = POS | NEG

local
    val n = ref 0
in
fun fresh_name polarity =
    (case polarity of POS => "_" | NEG => "_")
    ^ Int.toString(!n) before n := !n+1
end

fun is_internal a = String.sub (a,0) = #"%"

fun insert_fold POS a A = A.Plus[("mu_" ^ a, A)]
  | insert_fold NEG a A = A.With[("nu_" ^ a, A)]

fun polarity_defn env (A.Plus _) = POS
  | polarity_defn env (A.With _) = NEG
  | polarity_defn env (A.One) = POS
  | polarity_defn env (A.Exists _) = POS
  | polarity_defn env (A.Forall _) = NEG
  | polarity_defn env (A.PayPot _) = POS
  | polarity_defn env (A.GetPot _) = NEG
  | polarity_defn env (A.Next(t,A)) = polarity_defn env A
  | polarity_defn env (A.Dia _) = POS
  | polarity_defn env (A.Box _) = NEG
  | polarity_defn env (A.TpName(a,es)) = polarity_defn env (A.expd_tp env (a,es))
  (* A.Dot and A.TpName should be impossible *)

fun apply_fst f (A,env) = (f A, env)

fun polarize env0 ctx con pol (A.Next(t,A)) env = (* neutral: continue *)
    apply_fst (fn A => A.Next(t, A)) (polarize env0 ctx con pol A env)

  (* positive types *)
  | polarize env0 ctx con POS (A.Plus(alts)) env = apply_fst A.Plus (polarize_alts env0 ctx con POS alts env)
  | polarize env0 ctx con POS (A.One) env = (A.One, env)
  | polarize env0 ctx con POS (A.Exists(phi,A)) env = apply_fst (fn A => A.Exists(phi, A)) (polarize env0 ctx (R.And(con,phi)) POS A env)
  | polarize env0 ctx con POS (A.PayPot(p,A)) env = apply_fst (fn A => A.PayPot(p,A)) (polarize env0 ctx con POS A env)
  | polarize env0 ctx con POS (A.Dia(A)) env = apply_fst A.Dia (polarize env0 ctx con POS A env)
  | polarize env0 ctx con POS (A as A.TpName(a, es)) env =
    if is_internal a
    then polarize env0 ctx con POS (A.expd_tp env0 (a,es)) env
    else (A,env) (* pos or neg? *)
  (* negative: introduce new definition *)
  | polarize env0 ctx con POS A env = polarize_name env0 ctx con NEG A env

  (* negative types *)
  | polarize env0 ctx con NEG (A.With(alts)) env = apply_fst A.With (polarize_alts env0 ctx con NEG alts env)
  | polarize env0 ctx con NEG (A.Forall(phi,A)) env = apply_fst (fn A => A.Forall(phi,A)) (polarize env0 ctx (R.And(con,phi)) NEG A env)
  | polarize env0 ctx con NEG (A.GetPot(p,A)) env = apply_fst (fn A => A.GetPot(p,A)) (polarize env0 ctx con NEG A env)
  | polarize env0 ctx con NEG (A.Box(A)) env = apply_fst A.Box (polarize env0 ctx con NEG A env)
  | polarize env0 ctx con NEG (A as A.TpName(a, es)) env =
    if is_internal a
    then polarize env0 ctx con NEG (A.expd_tp env0 (a,es)) env
    else (A,env) (* pos or neg? *)
  | polarize env0 ctx con NEG A env = polarize_name env0 ctx con POS A env
    
and polarize_alts env0 ctx con polarity nil env = (nil, env)
  | polarize_alts env0 ctx con polarity ((l,A)::alts) env =
    let val (A',env') = polarize env0 ctx con polarity A env
        val (alts',env'') = polarize_alts env0 ctx con polarity alts env'
    in
        ((l,A')::alts', env'')
    end

and polarize_name env0 ctx con polarity A env =
    let 
        val (A', env') = polarize env0 ctx con polarity A env
        val new_tpname = fresh_name polarity
        val A'' = insert_fold polarity new_tpname A'
        val decl = A.TpDef(new_tpname, ctx, con, A'', NONE)
    in
        (A.TpName(new_tpname, List.map (fn v => R.Var(v)) ctx), decl::env')
    end

fun polarize_decl env0 (decl as A.TpDef(a, vs, con, A, ext)) =
    (* do not polarize internal names *)
    if is_internal a
    then [decl]
    else let val polarity = polarity_defn env0 A
             val (A', env') = polarize env0 vs con polarity A nil
             val A'' = insert_fold polarity a A'
         in
             A.TpDef(a, vs, con, A'', ext)::env'
         end

fun polarize_decls env0 nil = nil
  | polarize_decls env0 ((decl as A.TpDef _)::decls) =
    let
        val tpdefs = polarize_decl env0 decl
    in
        tpdefs @ polarize_decls env0 decls
    end 
  | polarize_decls env0 (decl::decls) = decl::polarize_decls env0 decls

(* copied from wrecon.sml and updated *)

fun matching_tprefix env (A.TpName(a,_)) (A.TpName(a',_)) = a = a'
  | matching_tprefix env A B = false

(* we insert caseL mu_* if must_postponeL is false *)
fun must_postponeL env A' (A.Id) = false (* need not postpone *)
  | must_postponeL env A' (A.Cut(P,lpot,B,Q)) = must_postponeL env A' P
  | must_postponeL env A' (A.Spawn(P,Q)) = must_postponeL env A' P
  | must_postponeL env A' (A.ExpName(f,es)) =
    matching_tprefix env A' (TC.synL env (f,es))
  (* left interactions *)
  | must_postponeL env A' (A.LabL _) = false
  | must_postponeL env A' (A.CaseL _) = false
  | must_postponeL env A' (A.WaitL _) = false
  | must_postponeL env A' (A.AssumeL _) = false
  | must_postponeL env A' (A.AssertL _) = false
  | must_postponeL env A' (A.GetL _) = false
  | must_postponeL env A' (A.PayL _) = false
  | must_postponeL env A' (A.WhenL _) = false
  | must_postponeL env A' (A.NowL _) = false
  (* right interactions *)
  | must_postponeL env A' (A.LabR(_, P))  = must_postponeL env A' P
  | must_postponeL env A' (A.CaseR(branches)) = must_postpone_branchesL env A' branches
  | must_postponeL env A' (A.CloseR) = false
  | must_postponeL env A' (A.AssertR(phi, P)) = must_postponeL env A' P
  | must_postponeL env A' (A.AssumeR(phi, P)) = must_postponeL env A' P
  | must_postponeL env A' (A.PayR(p,P)) = must_postponeL env A' P
  | must_postponeL env A' (A.GetR(p,P)) = must_postponeL env A' P
  | must_postponeL env A' (A.NowR(P)) = must_postponeL env A' P
  | must_postponeL env A' (A.WhenR(P)) = false (* left must be (n)[] *)
  (* neutral *)
  | must_postponeL env A' (A.Imposs) = false
  | must_postponeL env A' (A.Work(p,P)) = must_postponeL env A' P
  | must_postponeL env A' (A.Delay(t,P)) = false (* both left and right types must be decrementable *)
  | must_postponeL env A' (A.Marked(marked_P)) = must_postponeL env A' (Mark.data marked_P)
(* must postpone if just one branch forces it *)
and must_postpone_branchesL env A' nil = false
  | must_postpone_branchesL env A' ((l,_,P)::branches) =
    must_postponeL env A' P orelse must_postpone_branchesL env A' branches

(* we insert caseR nu_* if must_postponeR is false *)
fun must_postponeR env (A.Id) C' = false (* need not postpone *)
  | must_postponeR env (A.Cut(P, _, _, Q)) C' = must_postponeR env Q C'
  | must_postponeR env (A.Spawn(P,Q)) C' = must_postponeR env Q C'
  | must_postponeR env (A.ExpName(f,es)) C' =
    matching_tprefix env (TC.synR env (f,es)) C'
  (* right interactions *)
  | must_postponeR env (A.LabR _) C' = false
  | must_postponeR env (A.CaseR _) C' = false
  | must_postponeR env (A.CloseR) C' = false
  | must_postponeR env (A.AssertR _) C' = false
  | must_postponeR env (A.AssumeR _) C' = false
  | must_postponeR env (A.PayR _) C' = false
  | must_postponeR env (A.GetR _) C' = false
  | must_postponeR env (A.NowR _) C' = false
  | must_postponeR env (A.WhenR _) C' = false
  (* left interactions *)
  | must_postponeR env (A.LabL(_, P)) C' = must_postponeR env P C'
  | must_postponeR env (A.CaseL(branches)) C' = must_postpone_branchesR env branches C'
  | must_postponeR env (A.WaitL(P)) C' = must_postponeR env P C'
  | must_postponeR env (A.AssertL(_,P)) C' = must_postponeR env P C'
  | must_postponeR env (A.AssumeL(_,P)) C' = must_postponeR env P C'
  | must_postponeR env (A.GetL(p,P)) C' = must_postponeR env P C'
  | must_postponeR env (A.PayL(p,P)) C' = must_postponeR env P C'
  | must_postponeR env (A.WhenL(P)) C' = false (* right type must be (n)<> *)
  | must_postponeR env (A.NowL(P)) C' = must_postponeR env P C'
  (* neutral *)
  | must_postponeR env (A.Imposs) C' = false
  | must_postponeR env (A.Work(p,P)) C' = must_postponeR env P C'
  | must_postponeR env (A.Delay(t,P)) C' = false (* left/right types must be decrementable *)
  | must_postponeR env (A.Marked(marked_P)) C' = must_postponeR env (Mark.data marked_P) C'
(* must postpoint if just one branch forces it *)
and must_postpone_branchesR env nil C' = false
  | must_postpone_branchesR env ((l,_,P)::branches) C' =
    must_postponeR env P C' orelse must_postpone_branchesR env branches C'

(* we insert L.nu_* if may_postponeL is false *)
fun may_postponeL env A' (A.Id) = false (* cannot postpone past 'forward' *)
  | may_postponeL env A' (A.Cut(P,lpot,B,Q)) = true
  | may_postponeL env A' (A.Spawn(P,Q)) = may_postponeL env A' P
  | may_postponeL env A' (A.ExpName(f,es)) =
    matching_tprefix env A' (TC.synL env (f,es))
  (* left interactions *)
  | may_postponeL env A' (A.LabL _) = false
  | may_postponeL env A' (A.CaseL _) = false
  | may_postponeL env A' (A.WaitL _) = false
  | may_postponeL env A' (A.AssertL _) = false
  | may_postponeL env A' (A.AssumeL _) = false
  | may_postponeL env A' (A.GetL _) = false
  | may_postponeL env A' (A.PayL _) = false
  | may_postponeL env A' (A.WhenL _) = false
  | may_postponeL env A' (A.NowL _) = false

  (* right interactions *)
  | may_postponeL env A' (A.LabR(_, P))  = true
  | may_postponeL env A' (A.CaseR(branches)) = true (* push into each branch *)
  | may_postponeL env A' (A.CloseR) = false (* can not postpone past closeR *)
  | may_postponeL env A' (A.AssertR(_,P)) = true
  | may_postponeL env A' (A.AssumeR(_,P)) = true
  | may_postponeL env A' (A.PayR(_,P)) = true
  | may_postponeL env A' (A.GetR(_,P)) = true
  | may_postponeL env A' (A.NowR(P)) = true
  | may_postponeL env A' (A.WhenR(P)) = false (* left type must be (n)[] *)
  (* neutral *)
  | may_postponeL env A' (A.Imposs) = false
  | may_postponeL env A' (A.Work(p,P)) = true
  | may_postponeL env A' (A.Delay(t,P)) = false (* delay has effect on both sides: may not postpone *)
  | may_postponeL env A' (A.Marked(marked_P)) = may_postponeL env A' (Mark.data marked_P)

(* we insert PayR if may_postponeR is false *)
fun may_postponeR env (A.Id) C' = false (* cannot postpone *)
  | may_postponeR env (A.Cut(P, _, _, Q)) C' = true
  | may_postponeR env (A.Spawn(P,Q)) C' = true
  | may_postponeR env (A.ExpName(f,es)) C' =
    matching_tprefix env (TC.synR env (f,es)) C'
  (* right interactions *)
  | may_postponeR env (A.LabR _) C' = false
  | may_postponeR env (A.CaseR _) C' = false
  | may_postponeR env (A.CloseR) C' = false
  | may_postponeR env (A.AssertR _) C' = false
  | may_postponeR env (A.AssumeR _) C' = false
  | may_postponeR env (A.PayR _) C' = false
  | may_postponeR env (A.GetR _) C' = false
  | may_postponeR env (A.NowR _) C' = false
  | may_postponeR env (A.WhenR _) C' = false
  (* left interactions *)
  | may_postponeR env (A.LabL(_, P)) C' = true
  | may_postponeR env (A.CaseL(branches)) C' = true
  | may_postponeR env (A.WaitL(P)) C' = true
  | may_postponeR env (A.AssertL _) C' = true
  | may_postponeR env (A.AssumeL _) C' = true
  | may_postponeR env (A.GetL _) C' = true
  | may_postponeR env (A.PayL _) C' = true
  | may_postponeR env (A.WhenL _) C' = false (* right type must be (n)<> *)
  | may_postponeR env (A.NowL _) C' = true
  (* neutral *)
  | may_postponeR env (A.Imposs) C' = false (* TODO: check! *)
  | may_postponeR env (A.Work(p,P)) C' = true
  | may_postponeR env (A.Delay(t,P)) C' = false (* delay has effect on both sides: may not postpone *)
  | may_postponeR env (A.Marked(marked_P)) C' = may_postponeR env (Mark.data marked_P) C'

(* strip_next0 ctx con A = A' preserves external definitions
 * because of their significance with iso-recursive types
 * purposes but strips off all prefixes (t)A' if con |= t = 0
 * and expands internal definitions
 *)
fun strip_next0 env ctx con (A as A.Next(t,A')) =
    if C.entails ctx con (R.Eq(t,R.Int(0)))
    then strip_next0 env ctx con A'
    else A
  | strip_next0 env ctx con (A as A.TpName(a,es)) =
    if is_internal a
    then strip_next0 env ctx con (A.expd_tp env (a,es))
    else A
  | strip_next0 env ctx con A = A

(* recon env ctx con A P C ext = P'
 * where P' contains additional constructs for sending or
 * receiving folds/unfolds
 * Assumes A |- P : C, in the original types without additional unfolding
 *
 *)
fun recon env ctx con A P C ext =
    let
        val A' = strip_next0 env ctx con A
        val C' = strip_next0 env ctx con C
    in
        recon' env ctx con A' P C' ext
    end

(* recon' env ctx con A P C ext = P' see recon *)
(* A and C cannot be internal definitions *)
and recon' env ctx con (A as A.TpName(a,es)) P C ext =
    (* receive if a is positive, unless we need to postpone *)
    (* send if a is negative, unless we may postpone *)
    (case A.expd_tp env (a,es)
      of A.Plus[(l,A')] =>
         if not (must_postponeL env A P)
         then A.CaseL[(l,ext,recon env ctx con A' P C ext)]
         else recon'' env ctx con A P C ext
       | A.With[(l,A')] =>
         if not (may_postponeL env A P)
         then A.LabL(l, recon env ctx con A' P C ext)
         else recon'' env ctx con A P C ext
    )
  | recon' env ctx con A P C ext =
    recon'' env ctx con A P C ext

and recon'' env ctx con A P (C as A.TpName(c,es)) ext =
    (* send if a is positive, unless we may postpone *)
    (* receive if a is negative, unless we need to postpone *)
    (case A.expd_tp env (c,es)
      of A.Plus[(l,C')] =>
         if not (may_postponeR env P C)
         then A.LabR(l, recon env ctx con A P C' ext)
         else recon''' env ctx con A P C ext
       | A.With[(l,C')] =>
         if not (must_postponeR env P C)
         then A.CaseR[(l,ext,recon env ctx con A P C' ext)]
         else recon''' env ctx con A P C ext
    )
  | recon'' env ctx con A P C ext =
    recon''' env ctx con A P C ext

(* recon''' env ctx con A P C ext = P'
 * assumes A and C are structural or quantifiers and
 * it does not need to insert any terminal work into P
 *)
(* judgmental constructs: id, cut, spawn, call *)
and recon''' env ctx con A (A.Id) C ext = A.Id
  | recon''' env ctx con A (A.Cut(P,lpot,B,Q)) C ext =
    A.Cut(recon env ctx con A P B ext, lpot, B,
          recon env ctx con B Q C ext)
  | recon''' env ctx con A (A.Spawn(P,Q)) C ext =
    let val (A', pot', P', B) = TC.syn_call env P ext
    in A.Spawn(P', recon env ctx con B Q C ext) end
  | recon'''  env ctx con A (P as A.ExpName(f,es)) C ext = P

  (* begin cases for each action matching their type *)
  | recon''' env ctx con A (A.LabR(k,P)) (C as A.Plus(choices)) ext =
    A.LabR(k, recon env ctx con A P (TC.syn_alt env choices k) ext)
  | recon''' env ctx con (A.Plus(choices)) (A.CaseL(branches)) C ext =
    A.CaseL(recon_branchesL env ctx con choices branches C ext)

  | recon''' env ctx con A (A.CaseR(branches)) (A.With(choices)) ext =
    A.CaseR(recon_branchesR env ctx con A branches choices ext)
  | recon''' env ctx con (A as A.With(choices)) (A.LabL(k,Q)) C ext =
    A.LabL(k, recon env ctx con (TC.syn_alt env choices k) Q C ext)

  | recon''' env ctx con (A.Dot) (A.CloseR) C ext = A.CloseR
  | recon''' env ctx con (A.One) (A.WaitL(Q)) C ext =
    A.WaitL(recon env ctx con (A.Dot) Q C ext)

  (* quantifiers *)
  | recon''' env ctx con A (A.AssertR(phi,P)) (A.Exists(phi',C')) ext =
    A.AssertR(phi,recon env ctx con A P C' ext)
  | recon''' env ctx con (A.Exists(phi',A')) (A.AssumeL(phi, P)) C ext =
    A.AssumeL(phi,recon env ctx con A' P C ext)

  | recon''' env ctx con A (A.AssumeR(phi,P)) (A.Forall(phi',C')) ext =
    A.AssumeR(phi, recon env ctx con A P C' ext)
  | recon''' env ctx con (A.Forall(phi',A')) (A.AssertL(phi,P)) C ext =
    A.AssertL(phi, recon env ctx con A' P C ext)
  (* end structural cases *)

  (* impossibility *)
  | recon''' env ctx con A (A.Imposs) C ext = A.Imposs

  (* ergometric types *)
  | recon''' env ctx con A (A.Work(p,P)) C ext =
    A.Work(p, recon env ctx con A P C ext) (* pot >= p, to be enforced later *)

  | recon''' env ctx con A (A.PayR(p',P)) (A.PayPot(p,C)) ext =
    A.PayR(p', recon env ctx con A P C ext)
  | recon''' env ctx con (A.PayPot(p,A)) (A.GetL(p',P)) C ext =
    A.GetL(p', recon env ctx con A P C ext)
  | recon''' env ctx con A (A.GetR(p',P)) (A.GetPot(p,C)) ext =
    A.GetR(p', recon env ctx con A P C ext)
  | recon''' env ctx con (A.GetPot(p,A)) (A.PayL(p',P)) C ext =
    A.PayL(p', recon env ctx con A P C ext)

  (* temporal types *)
  | recon''' env ctx con A (A.Delay(t,P)) C ext =
    let val A' = TC.decrementL env ctx con A t ext
        val C' = TC.decrementR env ctx con C t ext
    in
        A.Delay(t, recon env ctx con A' P C' ext)
    end

  | recon''' env ctx con A (A.NowR(P)) (A.Dia(C)) ext =
    A.NowR(recon env ctx con A P C ext)
  | recon''' env ctx con (A.Dia(A)) (A.WhenL(P)) C ext =
    A.WhenL(recon env ctx con A P C ext)
  | recon''' env ctx con A (A.WhenR(P)) (A.Box(C)) ext =
    A.WhenR(recon env ctx con A P C ext)
  | recon''' env ctx con (A.Box(A)) (A.NowL(P)) C ext =
    A.NowL(recon env ctx con A P C ext)

  (* traverse but preserve marks *)
  | recon''' env ctx con A (A.Marked(marked_P)) C ext =
    A.Marked(Mark.mark'(recon''' env ctx con A (Mark.data marked_P) C (Mark.ext marked_P),
                        Mark.ext marked_P))

  | recon''' env ctx con A P C ext =
    ( TextIO.print (PP.pp_exp env P ^ "\n : " ^ PP.pp_tpj_compact env A (R.Int(0)) C ^ "\n")
    ; raise Match )

  (* all other cases are impossible, since we assume approximate typing *)

and recon_branchesL env ctx con nil nil C ext = nil
  | recon_branchesL env ctx con ((l,A)::choices) ((l',ext',P)::branches) C ext =
    (* after quantifer reconstruction, branches must match choices exactly *)
    (l',ext',recon env ctx con A P C ext)::(recon_branchesL env ctx con choices branches C ext)

and recon_branchesR env ctx con A nil nil ext = nil
  | recon_branchesR env ctx con A ((l,ext',P)::branches) ((l',C)::choices) ext =
    (* after quantifer reconstruction, branches must match choices exactly *)
    (l,ext',recon env ctx con A P C ext)::(recon_branchesR env ctx con A branches choices ext)
    
fun subst es (vs,con,(A,pot,C)) =
    let
        val sg = R.zip vs es
    in
        (R.apply_prop sg con, (A.apply_tp sg A, R.apply sg pot, A.apply_tp sg C))
    end

fun recon_decls env ((decl as A.ExpDef(f,vs,P,ext))::decls) =
    let val (SOME(vs', con', (A', pot', C'))) = A.lookup_expdec env f
        val (con, (A, pot, C)) = subst (R.create_idx vs) (vs', con', (A', pot', C'))
        val P' = recon env vs con A P C ext
        (* can't double-check here if internal names have been expanded *)
        (* might loop in type equality *)
        (* 
        val () = if !Flags.verbosity >= 2
                 then TextIO.print ("% double-checking polarized " ^ f ^ "...")
                 else ()
        val () = TC.check_exp false env vs con A pot P' C ext
        val () = if !Flags.verbosity >= 2 then TextIO.print ("ok\n") else ()
        *)
    in
        A.ExpDef(f, vs, P', ext)::recon_decls env decls
    end
  | recon_decls env (decl::decls) = decl::recon_decls env decls
  | recon_decls env nil = nil

(*extract mu and nu from a label if any*)
fun lab2tpname s =
    if String.isPrefix "mu_" s
    then SOME(IND, String.extract(s,3,NONE)                                                                                             )
    else if String.isPrefix "nu_" s
    then SOME(CO, String.extract(s,3,NONE))
    else NONE

fun tp2lab (A.Plus[(l,_)]) = SOME(l)
  | tp2lab (A.With[(l,_)]) = SOME(l)
  | tp2lab _ = NONE

structure C :>
          sig
              datatype constraint = LESS of A.expname * A.expname * int (* 0 <= m < #of types *)
              datatype outcome = CONSISTENT | INCONSISTENT
              val find_pos : A.expname -> A.expname -> constraint list -> int option (* 0 <= m < #of types *)
              val add : constraint list -> constraint -> constraint list * outcome
              val pp_cons : constraint list -> string
              (*val permutet: A.tp list list-> Ast.env -> A.tp list list*)
          end 
  =
struct
datatype constraint = LESS of A.expname * A.expname * int
datatype outcome = CONSISTENT | INCONSISTENT





    
(*
fun mem nil (LESS(f,g,n)) = false
  | mem (LESS(f',g',n')::cons) (LESS(f,g,n)) =
    ((f' = f) andalso (g' = g) andalso (n' = n) orelse mem cons (LESS(f,g,n))
 *)
fun find_pos f g nil = NONE
  | find_pos f g (LESS(f',g',n')::cons) =
    if f = f' andalso g = g' then SOME(n')
    else find_pos f g cons

fun find_min n f g (LESS(f',g',n')::cons) =
    if f = g' orelse f' = g then find_min (Int.min(n,n')) f g cons
    else find_min n f g cons
  | find_min n f g nil = n

fun update n f g (LESS(f',g',n')::cons) =
    if f = g' orelse f' = g then (LESS(f',g',n)::cons)
    else (LESS(f',g',n')::cons)
  | update n f g nil = nil

fun all_less g nil = [g]
  | all_less g (LESS(f',g',n')::cons) =
    if g = g'
    then f'::all_less g cons
    else all_less g cons

fun all_greater f nil = [f]
  | all_greater f (LESS(f',g',n')::cons) =
    if f = f'
    then g'::all_greater f cons
    else all_greater f cons

fun add_all_less n nil greater = nil
  | add_all_less n (f::fs) greater =
    add_all_less' n f greater @ add_all_less n fs greater
and add_all_less' n f nil = nil
  | add_all_less' n f (g::gs) = LESS(f,g,n)::add_all_less' n f gs
    
fun trans (LESS(f,g,n)) cons =
    let val n' = find_min n f g cons
        val cons' = update n f g cons
        val less = all_less f cons'
        val greater = all_greater g cons'
    in add_all_less n' less greater @ cons' end

fun add Con (LESS(f,g,n)) =
    if f = g then (Con, INCONSISTENT)
    else if List.exists (fn LESS(f',g',n') => f' = f andalso g' = g andalso n' = n) Con then (Con, CONSISTENT)
    else if List.exists (fn LESS(f',g',n') => f' = g andalso g' = f) Con then (Con, INCONSISTENT)
    else (trans (LESS(f,g,n)) Con, CONSISTENT)

fun pp_cons nil = "\n"
  | pp_cons (LESS(f,g,n)::cons) = (f ^ " < " ^ g ^ " @ " ^ Int.toString n ^ "\n") ^ pp_cons cons
end


fun inlist a nil=false
  | inlist a (b::cons)= if (a=b) then true else inlist a cons

fun access cons  env  (A.Plus(choices))  = access_alt cons env choices
| access cons  env (A.With(choices))= access_alt cons  env choices
| access cons  env (A.One)= cons
| access cons  env (A.Exists(phi,A))= access cons  env A
| access cons  env (A.Forall(phi,A))= access cons  env A
| access cons  env (A.PayPot(p,A))= access cons  env A
| access cons  env (A.GetPot(p,A))= access cons env A
| access cons  env (A.Next(t,A))= access cons  env A
| access cons  env (A.Dia(A))= access cons  env A
| access cons  env (A.Box(A))= access cons  env A
| access cons env (A.TpName(a,es))= if not (inlist a cons)  then access (a::cons)  env (A.expd_tp env (a,es)) 
                                         else cons

and  access_alt cons  env ((l,A)::alts)= 
     let val cons1= access cons  env A 
     in (cons1 @ access_alt cons  env alts) end
   | access_alt cons env nil = cons


fun findk_order k (chan::channel)=  if (k=0) then chan else findk_order (k-1) channel

(*fun cut_init_order nil 0 IND 1 permutation right B*)
fun cut_init_order al k last_d c nil chan B env1 check=  if check then ([(al, k, last_d, c, 0)]) else [(findk_order k chan)] (*if comes by true: same, if not: copy paste the kth tuple from right/left channel before cut, call next by cut*)
                                                        
  | cut_init_order al k last_d c (A.TpDef(a, l, _, A, ext)::env) chan B env1 check =
    (case tp2lab A
      of NONE => cut_init_order al k last_d c env chan B env1 check
       | SOME(l) => (case lab2tpname l
                      of SOME(d, _) => if last_d = d
                                          then  cut_init_order (al @ [a]) k last_d c env chan B env1 (check orelse (inlist a (access nil env1 B)))
                                               (*check if a can be accessed from type of the cut: if yes pass true. if not check. default: false*)
                                          else if (k=0 andalso al=nil) then ((al, k, last_d, 0, 0)::cut_init_order [a] (k+1) d c env chan B env1 (check orelse (inlist a (access nil env1 B))))
                                               (*if al=nil, then the actual first priority is of CO ductivity. And this priority is dummy!*)
                                          else if check then (al, k, last_d, c, 0)::cut_init_order [a] (k+1) d c env chan B env1 false
                                               else (findk_order k chan) ::cut_init_order [a] (k+1) d c env chan B env1 false
                                               (*if cehck is true: as before, reset the channel, if check is false: copy paste the kth tuple from right/left channel before cut. Build next tuple starting by check=false*)
                       | NONE => cut_init_order al k last_d c env chan B env1 check))
  | cut_init_order al k last_d c (_::env) chan B env1 check = cut_init_order al k last_d c env chan B env1 check





(* init_order k env where we have already seen k type definitions *)
(* c = 0 or c = 1; c = 0 same as before; c = 1 freshly allocated channel *)
fun init_order al k last_d c nil  = [(al, k, last_d, c, 0)] (* al = [] is possible, but okay *)
  | init_order al k last_d c (A.TpDef(a, l, _, A, ext)::env) =
    (case tp2lab A
      of NONE => init_order al k last_d c env
       | SOME(l) => (case lab2tpname l
                      of SOME(d, _) => if last_d = d
                                          then init_order (al @ [a]) k last_d c env (*if a can be accessed from type of the cut pass true. Previously true->true.default: false*)
                                          else if (k=0 andalso al=nil) then ((al, k, last_d, 0, 0)::init_order [a] (k+1) d c env)  (*if al=nil, then the actual first priority is of CO ductivity. And this priority is dummy!*)
                                          else (al, k, last_d, c, 0)::init_order [a] (k+1) d c env (*if comes by true: same, if not: copy paste the kth tuple from right/left channel before cut, call next by cut*)
                       | NONE => init_order al k last_d c env))
  | init_order al k last_d c (_::env) = init_order al k last_d c env

fun add cons (C.LESS(f,g,n), err) ext =
    ( (* TextIO.print("before: [" ^ C.pp_cons cons ^ "]") ; *)
      (* TextIO.print("adding: " ^ f ^ " < " ^ g ^ " @ " ^ Int.toString n ^ "\n") ; *)
      (*print(f^g^Int.toString(n));*)
    
     case C.add cons (C.LESS(f,g,n))
      of (cons', C.CONSISTENT) => ( (* TextIO.print("after: [" ^ C.pp_cons cons' ^ "]") ; *) cons' )
       | (cons', C.INCONSISTENT) => ERROR ext ("Termination violation(3): \n " ^ err ^ " and " ^ f ^ " < " ^ g ^ " @ pos " ^ Int.toString n ^ " is Inconsistent" ^ "\n")  )

(* m = pos in list *)

(*err builds the error message*)   
(*priorities in the error message begin with 1 if the first type is coinductive, and begin with 0 if the first type is inductive. *)

fun cless cons f g m ((al,n,d,c,k)::ords) ((al',n',d',c', k')::ords') err ext = (* al = al', d = d' *) (*g calls f*)
  if (k < k' andalso c=c') then let val err:string =" " in cons  end
  else (if (k = k' andalso c=c')
   then let val err: string = (err ^ (if(n=0 andalso al=nil) then ""  else ( "@ priority " ^  Int.toString n ^  (if(m mod 2=0) then (" (receive) ") else (" (send) "))  ^ ": "  ^ Int.toString (if (c=c') then k else 1) ^ " <= " ^ Int.toString k' ^ ", "))) in
   cless cons f g (m+1) ords ords' err ext end
  else 
  ( let val err: string = (err ^ (if(n=0 andalso al=nil) then ""  else ( "@ priority " ^  Int.toString n ^  (if(m mod 2=0) then (" (receive) ") else (" (send) "))  ^ ": "  ^ Int.toString (if (c=c') then k else 1) ^ " > " ^ Int.toString k' ^ ", "))) in 
    (add cons (C.LESS(f,g,(m div 2)),err) ext) end )(* f < g at pos n *)) 
  | cless cons f g m nil nil err ext =  let val err: string = err in 
    add cons (C.LESS(f,g,(m div 2)),err)  ext end

 (*err builds the error message, num is for identifying the send/receive in the err message*)   
(*priorities in the error message begin with 1 if the first type is coinductive, and begin with 0 if the first type is inductive. *)

fun check_less f g 0 ords ords' err num ext = ERROR ext ("termination violation! (0)\n " ^ g ^ " calls " ^ f ^ ": " ^ "but we already have @ pos 0 " ^ f ^ " > " ^ g ^"\n") 
  | check_less f g m ((al,n,d,c,k)::ords) ((al',n',d',c',k')::ords') err num ext = let val err: string =  (err ^ (if(n=0 andalso al=nil) then ""  else ("@ priority " ^ Int.toString n ^ (if(num mod 2=0) then (" (receive) ") else (" (send) ")) ^ ": "  ^ Int.toString (if (c=c') then k else 1) ^ " <= " ^ Int.toString k' ^ ", "))) in(* al = al', d = d' *)
   (k < k' andalso c=c') orelse (k = k' andalso c=c' andalso n < m andalso check_less f g m ords ords' err (num+1) ext)
    orelse ERROR ext ("termination violation! (1)\n" ^ g ^ " calls " ^ f ^ ": "^ err ^ " but we already have @ pos " ^ Int.toString m ^ ": " ^ f ^ ">" ^ g ^ "\n" ) end
  | check_less f g m nil nil err num ext = ERROR ext ("termination violation! (2)\n ")  (*covered in first pass. this case never occurs*)

fun is_less cons f g ords ords' ext =   (*g calls f*)
    (case C.find_pos  g f cons
      of NONE => true
       | SOME(n) => (* g < f at n *) check_less f g n ords ords' " " 0 ext)

fun inc a ((al',n,d,c,k)::ords) =
    if List.exists (fn a' => a = a') al'
    then ((al',n,d,c,k+1)::ords)
    else ((al',n,d,c,k)::inc a ords)
    (* inc a nil should be impossible *)

fun dec a ((al',n,d,c,k)::ords) =
    if List.exists (fn a' => a = a') al'
    then ((al',n,d,c,k-1)::ords)
    else ((al',n,d,c,k)::dec a ords)
    (* dec a nil should be impossible *)

fun merge nil nil = nil
  | merge ((al, n, IND, c,k)::ords) ((al', n', IND, c', k')::ords') = (* al = al', n = n' *)
    (al, n, IND, c, k)::(al', n', IND, c', k')::merge ords ords'
  | merge ((al, n, CO,c, k)::ords) ((al', n', CO,c', k')::ords') = (* al = al', n = n' *)
    (al', n', CO, c', k')::(al, n, CO,c, k)::(merge ords ords')
  (* everything else should be impossible *)

datatype pass = First | Second

fun cterm pass env cons f permutation left (A.Id) right ext = cons (* A = A' *)
  | cterm pass env cons f permutation left (A.Cut(P, _, B, Q)) right ext =
    let val cons1 = cterm pass env cons f permutation left P (cut_init_order nil 0 IND 1 permutation right B env false) ext (* IND is arbitrary *)
    in cterm pass env cons1 f permutation (cut_init_order nil 0 IND 1 permutation left B env false) Q right ext end (* IND is arbitrary *)
  | cterm pass env cons f permutation left (A.Spawn(P,Q)) right ext =
    cterm pass env cons f permutation left (TC.syn_cut env (P,Q) ext) right ext

  | cterm First env cons f permutation left (A.ExpName(g,es)) right ext =
    cless cons g f 0 (merge left right) (merge (init_order nil 0 IND 0 permutation) (init_order nil 0 IND 0 permutation)) " " ext (*If in the first pass, construct a relation between g and f by calling cless*)
  
  | cterm Second env cons f permutation left (A.ExpName(g,es)) right ext =
    if not (is_less cons g f (merge left right) (merge (init_order nil 0 IND 0 permutation) (init_order nil 0 IND 0 permutation)) ext) (*If in the second pass, check if the value of recursive call is less that the value of first call*)
    then ERROR ext "Termination violation! (4)"
    else cons

  (* internal choice *)
  | cterm pass env cons f permutation left (A.LabR(k, P)) right ext =
    (case lab2tpname k
      of NONE => cterm pass env cons f permutation left P right ext
       | SOME(IND, a) => cterm pass env cons f permutation left P (inc a right) ext  (* if sends a mu unfolding message to the right for type a, increment the value of type a on the right*)
       (* SOME(CO, a) should be impossible! *)
    )
  | cterm pass env cons f permutation left (A.CaseL(branches)) right ext =
    cterm_branchesL pass env cons f permutation left branches right ext

  (* external choice *)
  | cterm pass env cons f permutation left (A.CaseR(branches)) right ext =
    cterm_branchesR pass env cons f permutation left branches right ext
  | cterm pass env cons f permutation left  (A.LabL(k, Q)) right ext =
    (case lab2tpname k
      of NONE => cterm pass env cons f permutation left Q right ext
       | SOME(CO, a) => cterm pass env cons f permutation (inc a left) Q right ext (* if sends a nu unfolding message to the left for type a, increment the value of type a on the left*)
       (* SOME(IND, a) should be impossible *)
    )

  (* unit *)
  | cterm pass env cons f permutation left (A.CloseR) right ext = cons
  | cterm pass env cons f permutation left (A.WaitL(Q)) right ext =
    cterm pass env cons f permutation left Q right ext

  (* quantifiers *)
  | cterm pass env cons f permutation left (A.AssertR(phi,P)) right ext =
    cterm pass env cons f permutation left P right ext
  | cterm pass env cons f permutation left (A.AssumeL(phi,P)) right ext =
    cterm pass env cons f permutation left P right ext
  | cterm pass env cons f permutation left (A.AssumeR(phi,P)) right ext =
    cterm pass env cons f permutation left P right ext
  | cterm pass env cons f permutation left (A.AssertL(phi,P)) right ext =
    cterm pass env cons f permutation left P right ext
  | cterm pass env cons f permutation left (A.Imposs) right ext = cons

  (* work *)
  | cterm pass env cons f permutation left (A.Work(p,P)) right ext =
    cterm pass env cons f permutation left P right ext
  | cterm pass env cons f permutation left (A.PayR(p,P)) right ext =
    cterm pass env cons f permutation left P right ext    
  | cterm pass env cons f permutation left (A.GetL(p,P)) right ext =
    cterm pass env cons f permutation left P right ext    
  | cterm pass env cons f permutation left (A.GetR(p,P)) right ext =
    cterm pass env cons f permutation left P right ext    
  | cterm pass env cons f permutation left (A.PayL(p,P)) right ext =
    cterm pass env cons f permutation left P right ext    

  (* time *)
  | cterm pass env cons f permutation left (A.Delay(t,P)) right ext =
    cterm pass env cons f permutation left P right ext
  | cterm pass env cons f permutation left (A.NowR(P)) right ext =
    cterm pass env cons f permutation left P right ext
  | cterm pass env cons f permutation left (A.WhenL(P)) right ext =
    cterm pass env cons f permutation left P right ext
  | cterm pass env cons f permutation left (A.WhenR(P)) right ext =
    cterm pass env cons f permutation left P right ext
  | cterm pass env cons f permutation left (A.NowL(P)) right ext =
    cterm pass env cons f permutation left P right ext

  | cterm pass env cons f permutation left (A.Marked(marked_P)) right ext =
    cterm pass env cons f permutation left (Mark.data marked_P) right (Mark.ext marked_P)

  (*
  | cterm pass env cons f left P right ext = ERROR ext "expression not permitted for termination checking"
  *)
and cterm_branchesL pass env cons f permutation left ((l,_,P)::branches) right ext =
    (case (lab2tpname l, branches)
      of (NONE, _) => let val cons1 = cterm pass env cons f permutation left P right ext
                      in cterm_branchesL pass env cons1 f permutation left branches right ext end
       | (SOME(IND, a), nil) => cterm pass env cons f permutation (dec a left) P right ext       (* if receives a mu unfolding message from left for type a, decrement the value of type a on the left*)
       (* SOME(CO, a) should be impossible *)
    )
  | cterm_branchesL pass env cons f permutation left nil right ext = cons
and cterm_branchesR pass env cons f permutation left ((l,_,P)::branches) right ext =
    (case (lab2tpname l,branches)
      of (NONE,_) => let val cons1 = cterm pass env cons f permutation left P right ext
                       in cterm_branchesR pass env cons1 f permutation left branches right ext end
       | (SOME(CO, a), nil) => cterm pass env cons f permutation left P (dec a right) ext          (* if receives a nu unfolding message from right for type a, decrement the value of type a on the right*)
       (* SOME(IND, a) should be impossible *)
    )
  | cterm_branchesR pass env cons f permutation left nil right ext = cons

  fun isin f nil= false
  | isin f (a::cons)= if a=f then true else isin f cons


fun terminates block permutation pass env cons nil = cons
  | terminates block permutation pass env cons (A.Pragma _::decls) = terminates block permutation pass env cons decls
  | terminates block permutation pass env cons (A.TpDef(a, l, _, A, ext)::decls) =
    terminates block permutation pass env cons decls
  | terminates block permutation pass env cons (A.ExpDec(f, _, _, _, ext)::decls) = terminates block permutation pass env cons decls
  | terminates block permutation pass env cons (A.ExpDef(f, _, P, ext)::decls) = 
  if isin f block then
  (let val cons1 = cterm pass env cons f permutation (init_order nil 0 IND 0 permutation) P (init_order nil 0 IND 0 permutation) ext
    in terminates block permutation pass env cons1 decls end)
  else terminates block permutation pass env cons decls
  | terminates block permutation pass env cons (A.Exec _::decls) = terminates block permutation pass env cons decls

fun pp_tpdefs env ((decl as A.TpDef(a,_,_,_,_))::decls) =
    if is_internal a
    then pp_tpdefs env decls
    else ( TextIO.print (PP.pp_decl env decl ^ "\n")
         ; pp_tpdefs env decls )
  | pp_tpdefs env (decl::decls) = pp_tpdefs env decls
  | pp_tpdefs env nil = ()

fun pp_expdefs env ((decl as A.ExpDef _)::decls) =
    ( TextIO.print (PP.pp_decl env decl ^ "\n")
    ; pp_expdefs env decls )
  | pp_expdefs env (_::decls) = pp_expdefs env decls
  | pp_expdefs env nil = ()


(*block and permute*)


fun initblocks nil= nil
  |initblocks (decl as A.ExpDef(f, _, _, ext)::decls)= ([f]::initblocks decls)
  |initblocks  (_::decls)= initblocks decls 

 
fun isin f nil= false
  | isin f (a::cons)= if a=f then true else isin f cons

fun findclass f nil= nil
| findclass f (a::cons) = if (isin f a) then a else findclass f cons 



fun delete f nil=nil
fun delete f (a::cons)= if f=a then cons else (a::(delete f cons ))
fun  class g f nil =  nil
  |class g f (a::cons)= if g=f  then (a::cons) else ((g@f):: (delete g (delete f (a::cons))))


fun funblock env cons f (A.Id) ext = cons (* A = A' *)
  | funblock env cons f (A.Cut(P, _, B, Q)) ext =
    let val cons1 = funblock env cons f P ext (* IND is arbitrary *)
    in funblock env cons1 f Q ext end (* IND is arbitrary *)
  | funblock env cons f (A.Spawn(P,Q)) ext =
    funblock  env cons f (TC.syn_cut env (P,Q) ext) ext

  | funblock env cons f (A.ExpName(g,es)) ext = class (findclass g cons) (findclass f cons) cons
     (* internal choice *)
  | funblock  env cons f (A.LabR(k, P)) ext = funblock  env cons f  P ext
  | funblock  env cons f (A.CaseL(branches)) ext =
    funblock_branchesL  env cons f branches ext

  (* external choice *)
  | funblock  env cons f (A.CaseR(branches)) ext =
    funblock_branchesR  env cons f branches  ext
  | funblock  env cons f (A.LabL(k, Q)) ext =
    funblock  env cons f Q ext
  (* unit *)
  | funblock  env cons f (A.CloseR) ext = cons
  | funblock  env cons f (A.WaitL(Q)) ext =
    funblock  env cons f Q  ext

  (* quantifiers *)
  | funblock  env cons f (A.AssertR(phi,P)) ext =
    funblock  env cons f P ext
  | funblock  env cons f (A.AssumeL(phi,P)) ext =
    funblock  env cons f P ext
  | funblock  env cons f (A.AssumeR(phi,P)) ext =
    funblock  env cons f P ext
  | funblock  env cons f (A.AssertL(phi,P)) ext =
    funblock  env cons f P ext
  | funblock  env cons f (A.Imposs) ext = cons

  (* work *)
  | funblock  env cons f (A.Work(p,P)) ext =
    funblock  env cons f P ext
  | funblock  env cons f (A.PayR(p,P)) ext =
    funblock  env cons f P ext    
  | funblock  env cons f (A.GetL(p,P)) ext =
    funblock  env cons f P ext    
  | funblock  env cons f (A.GetR(p,P)) ext =
    funblock  env cons f P ext    
  | funblock  env cons f (A.PayL(p,P)) ext =
    funblock  env cons f P ext    

  (* time *)
  | funblock  env cons f (A.Delay(t,P)) ext =
    funblock  env cons f P ext
  | funblock  env cons f (A.NowR(P)) ext =
    funblock  env cons f P ext
  | funblock  env cons f (A.WhenL(P)) ext =
    funblock  env cons f P ext
  | funblock  env cons f (A.WhenR(P)) ext =
    funblock  env cons f P ext
  | funblock  env cons f (A.NowL(P)) ext =
    funblock  env cons f P ext

  | funblock  env cons f (A.Marked(marked_P)) ext =
    funblock  env cons f (Mark.data marked_P) (Mark.ext marked_P)

  
and funblock_branchesL  env cons f ((l,_,P)::branches) ext =
    let val cons1 = funblock  env cons f P ext
                      in funblock_branchesL  env cons1 f branches ext end
    | funblock_branchesL  env cons f nil ext = cons
and funblock_branchesR  env cons f ((l,_,P)::branches) ext =
    let val cons1 = funblock  env cons f  P ext
                       in funblock_branchesR  env cons1 f branches ext end
    | funblock_branchesR  env cons f nil ext = cons

fun preblock env cons nil = cons
  | preblock  env cons (A.Pragma _::decls) = preblock  env cons decls
  | preblock  env cons (A.TpDef(a, l, _, A, ext)::decls) =
    preblock  env cons decls
  | preblock  env cons (A.ExpDec(f, _, _, _, ext)::decls) = preblock  env cons decls
  | preblock  env cons (A.ExpDef(f, _, P, ext)::decls) =
    let val cons1 = funblock  env cons f P  ext
    in preblock  env cons1 decls end
  | preblock  env cons (A.Exec _::decls) = preblock env cons decls

fun conc a (c::nil) = [(a::c)]
  | conc a (c::rest) = [(a::c)] @ (conc a rest)

fun insert new nil = [[new]]
  | insert new (a::rest) = [(new::(a::rest))] @ conc a (insert new rest)

fun addl new nil = [[new]]
  | addl new (a::nil) = insert new a
  | addl new (a::k) = insert new a @ addl new k

fun printt env ((decl as A.TpDef _)) = TextIO.print (PP.pp_decl env decl ^ "\n")

fun depol (a::cons) = a

fun permutet tohere nil= tohere
  | permutet tohere (decl as A.TpDef(a, l, _, A, ext)::env) =
    if (not (is_internal a)) 
    then  permutet (addl (depol decl) tohere) env
    else  permutet  tohere env
  | permutet tohere (_::env)= permutet tohere env 

fun printproc nil = ()
  | printproc (c::proc) =
    let val() = TextIO.print(c ^ "\n")
    in printproc proc end

fun printx env nil = ()
  | printx env (a::cons) =
    let val () = printt env a
    in printx env cons end

fun permuteblocks nil env cons decls block = ERROR NONE "tried everything!"
  | permuteblocks (a::permutation) env cons decls block =
    let val () = if !Flags.verbosity >= 2
                 then ( TextIO.print ("%Checking Permutation: \n")
                      ; printx env a )
                 else ()
        val cons1 = terminates block a First env cons env 
        val cons2 = terminates block a Second env cons1 env
        in () end 
        handle ErrorMsg.Error => permuteblocks permutation env cons env block

fun terminateblocks permutation env cons decls nil = ()
  | terminateblocks permutation env cons decls (a::blocks) =
    let val () = if !Flags.verbosity >= 2
                 then ( TextIO.print ("%Checking Block: \n")
                      ; printproc a )
                 else ()
        val () = permuteblocks permutation env cons decls a
    in terminateblocks permutation env cons decls blocks end 

val terminates = fn env => fn decls =>
    case !Flags.terminate
      of SOME(Flags.Equi) =>                                   
         let val () = if !Flags.verbosity >= 2
                      then TextIO.print "% starting polarization\n% ---------------\n"
                      else ()
             val env' = polarize_decls env decls
             val () = if !Flags.verbosity >= 2
                      then pp_tpdefs env' env'
                      else ()
             val env'' = recon_decls env' env'
             val () = if !Flags.verbosity >= 2
                      then pp_expdefs env'' env''
                      else ()
             val () = if !Flags.verbosity >= 2
                      then TextIO.print "% ---------------\n% completed polarization\n"
                      else ()
             
             val permutations = permutet nil env'' (* generate all permutations *)
             val singleblocks= initblocks env''   (* each function in its own block *)
             val blocks = preblock  env'' singleblocks env'' (* was: decls *)
             val () = terminateblocks permutations env'' nil env'' blocks
  
             (*print(permutations)*)
             (*val cons1 = terminates block permutation First env'' nil env''*)
             (*val cons2 = terminates block permutation Second env'' cons1 env''*)
             val () = if !Flags.verbosity >= 1
                      then TextIO.print "% termination checking succeeded\n"
                      else ()
         in () end
       | SOME(Flags.Iso) =>
         let
        
 
             val permutations= permutet nil env
             val singleblocks= initblocks env  
             val blocks = preblock env singleblocks decls
             val cons1= terminateblocks  permutations env nil env blocks
             (*val cons1 = terminates block permutation First env'' nil env''*)
             (*val cons2 = terminates block permutation Second env'' cons1 env''*)
         in
             ()
         end 
end (* structure Termination *)
