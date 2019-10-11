(* Constraints *)

(* 
 * Deciding validity and satisfiability of constraints in Presburger
 * arithmetic.  Some trivial tests are also performed for nonlinear
 * constraints.  A flag 'approx' records if constraints whose validity
 * could not be determined were trusted.
 *)

signature CONSTRAINTS =
sig
    (* judgments *)
    val entails : Arith.ctx -> Arith.prop -> Arith.prop -> bool
    val hardentails : Arith.ctx -> Arith.prop -> Arith.prop -> bool
    val equiv : Arith.ctx -> Arith.prop -> Arith.prop -> Arith.prop -> bool
    val contradictory : Arith.ctx -> Arith.prop -> Arith.prop -> bool

    (* error messages *)
    val pp_jfail : Arith.prop -> Arith.prop -> string  (* con |/= phi *)
    val pp_jhold : Arith.prop -> Arith.prop -> string  (* con |= phi *)
    val pp_junsat : Arith.prop -> Arith.prop -> string (* con |= ~phi *)
    val pp_jsat : Arith.prop -> Arith.prop -> string   (* con |/= ~phi *)
    val pp_unrel : Arith.prop -> Arith.arith -> Arith.arith -> string (* con |/= e <?> e' *)

    (* if true, judgment could not be established or refuted *)
    val approx : bool ref
end

structure Constraints :> CONSTRAINTS =
struct

structure R = Arith
structure RP = R.Print
structure PP = PPrint
(* structure N = Normalize *)

val approx = ref false

fun pp_jfail con phi = PP.pp_prop con ^ " |/= " ^ PP.pp_prop phi
fun pp_jhold con phi = PP.pp_prop con ^ " |= " ^ PP.pp_prop phi
fun pp_junsat con phi = PP.pp_prop con ^ " |= " ^ PP.pp_prop (R.Not(phi))
fun pp_jsat con phi = PP.pp_prop con ^ " |/= " ^ PP.pp_prop (R.Not(phi))
fun pp_unrel con e1 e2 = PP.pp_prop con ^ " |/= " ^ PP.pp_arith e1 ^ " <?> " ^ PP.pp_arith e2

(* qcheck vs sigma con rhs_pred phi = true
 * if it happens to find a grounding substitution sigma @ sigma' such that
 * one (sigma @ sigma') con is false or rhs_pred ((sigma @ sigma') phi);
 * only considers substituting 0 and 1 for the variables in vs
 *)
fun qcheck (v::vs) sigma con rhs_pred phi =
    qcheck vs (sigma @ [(v,R.Int(0))]) con rhs_pred phi (* build subst in order of variables, for sanity *)
    andalso qcheck vs (sigma @ [(v,R.Int(1))]) con rhs_pred phi
  | qcheck nil sigma con rhs_pred phi = (* either [sigma]con is false, or [sigma]phi satisfies rhs_pred *)
    not (R.evaluate_prop (R.apply_prop sigma con))
    orelse rhs_pred (R.evaluate_prop (R.apply_prop sigma phi))

fun quick_check_valid ctx con phi = qcheck ctx nil con (fn b => b) phi (* phi true *)
fun quick_check_unsat ctx con phi = qcheck ctx nil con (fn b => not b) phi (* phi false *)

fun drop_anon_ctx ctx = List.map (fn v => if R.anon v then String.extract (v,1,NONE) else v) ctx

fun anoncheck con phi =
  let val ctx = R.free_prop phi []
      val ctx = R.free_prop con ctx
      val ctx = drop_anon_ctx ctx
      val tcon = R.drop_anon_prop con
      val tphi = R.drop_anon_prop phi
  in
  TextIO.print ("Checking: " ^ pp_jhold tcon tphi ^ "\n") ;
  R.valid ctx tcon tphi
    handle R.NonLinear => false
  end

(* constraint entailment, called in type-checking *)

(* entails ctx con phi = true if ctx ; con |= phi *)
(* assumes ctx |- con PROP and ctx |- phi PROP *)
(* returns true and sets flag 'approx' if con or phi are non-linear
 * and entailment cannot be proved or refuted 
 *)
fun entails ctx con phi =
    ( if !Flags.verbosity >= 3 then TextIO.print ("Testing: " ^ pp_jhold con phi ^ "\n") else ()
    ; R.valid ctx con phi
      handle R.NonLinear =>
             if quick_check_valid ctx con phi (* quick check, for arbitrary propositions *)
             then (* yes: may or may not be valid *)
                 ( TextIO.print ("Trusting: " ^ pp_jhold con phi ^ "\n")
                 ; approx := true
                 ; true )
             else (* no: definitely not valid *)
                 false
            | R.Anonymous =>
              if anoncheck con phi
              then
                ( TextIO.print ("Constraint!: " ^ pp_jhold con phi ^ "\n")
                ; true )
              else
                ( TextIO.print ("Constraint?: " ^ pp_jhold con phi ^ "\n")
                ; approx := true
                ; true )
    )

(* hardentails ctx con phi = true if ctx ; con |= phi *)
(* assumes ctx |- con PROP and ctx |- phi PROP *)
(* returns true/false if linear and false if con or phi are non-linear
 * and entailment cannot be proved or refuted 
 *)
fun hardentails ctx con phi =
    ( if !Flags.verbosity >= 3 then TextIO.print ("Testing: " ^ pp_jhold con phi ^ "\n") else ()
    ; R.valid ctx con phi
      handle R.NonLinear => false
           | R.Anonymous => anoncheck con phi        
    )

(* constraint equivalence, called in type equality *)

(* equiv ctx con phi phi' = true if con |= phi <=> phi' *)
(* assumes ctx |- con PROP, ctx |- phi PROP, and ctx |- phi' PROP *)
(* returns true and sets flag 'approx' if con, phi, or phi' are non-linear
 * and entailment cannot be proved or refuted *)
fun equiv ctx con phi phi' =
    ( entails ctx (R.And(con,phi)) phi'
      andalso entails ctx (R.And(con,phi')) phi )

(* contradictory ctx con phi = true if ctx ; con, phi |= false *)
(* see 'entails' for 'approx' flag *)
fun contradictory ctx con phi =
    ( if !Flags.verbosity >= 3 then TextIO.print ("Testing: " ^ pp_junsat con phi ^ "\n") else ()
    ; R.valid ctx (R.And(con,phi)) R.False
      handle R.NonLinear =>
             if quick_check_unsat ctx con phi
             then (* yes: may or may not be contradictory *)
                 ( TextIO.print ("Trusting: " ^ pp_junsat con phi ^ "\n")
                 ; approx := true
                 ; true )
             else (* no: definitely not contradictory *)
                 false
           | R.Anonymous =>
              if anoncheck con phi
              then
                ( TextIO.print ("Constraint!: " ^ pp_jhold con phi ^ "\n")
                ; true )
              else
                ( TextIO.print ("Constraint?: " ^ pp_jhold con phi ^ "\n")
                ; approx := true
                ; true )
    )

end (* structure Constraints *)
