(* Normalizing Arithmetic Expressions *)

signature NORMALIZE = 
sig

  type normal = Arith.arith

  (* normalizing an expression, combining the coefficients for each term in the multinomial *)
  val normalize : Arith.arith -> normal
  val check_normal : Arith.arith -> bool

  (* compare two multinomials in normal form *)
  val compare : normal -> normal -> bool

  (* simple checker for nonlinear constraints *)
  datatype outcome = Valid | NotValid | Unknown
  val decide : Arith.varname list -> Arith.prop -> Arith.prop -> outcome

end

structure Normalize :> NORMALIZE =
struct
  
  structure R = Arith

  type normal = R.arith

  (* normal form *)
  (* (vprod) vs ::= v * vs | v  % in alphabetical order
   * (prod)   p ::= n [>0] * vs | n 
   * (sum)    s ::= p + s | p
   *)
  (* strict normal form *)
  (* in s, each vs (including the empty one) is unique *)
  (* products p can be compared with built-in '=' *)
                
  fun check_const (R.Int(n)) = true (* n could be negative *)
    | check_const _ = false

  fun check_vprod (R.Var(v)) = true
    | check_vprod (R.Mult(R.Var(v),e)) = check_vprod e
    | check_vprod _ = false

  fun check_prod (R.Mult(e1,e2)) = check_const e1 andalso check_vprod e2
    | check_prod e = check_const e

  fun check_sum (R.Add(e1,e2)) = check_prod e1 andalso check_sum e2
    | check_sum e = check_prod e

  (* check_normal e does not verify uniqueness of products *)
  fun check_normal e = check_sum e

  (* add (s1 : sum) (s2 : sum) : sum, not necessarily strict
   * add s1 s2 ~> s1 + s2  *)
  fun add (R.Add(p1,s1)) s2 = R.Add(p1, add s1 s2)
    | add p1 s2 = R.Add(p1,s2)

  (* pminus (p : prod) : prod
   * pminus p ~> -p *)
  fun pminus (R.Mult(R.Int(n),p)) = R.Mult(R.Int(~n),p)
    | pminus (R.Int(n)) = R.Int(~n)

  (* sminus (s : sum) : sum
   * sminus s ~> -s *)
  fun sminus (R.Add(p,s)) = R.Add(pminus p, sminus s)
    | sminus p = pminus p

  (* subtract (s1 : sum) (s2 : sum) : sum, not necessarily strict
   * subtract s1 s2 ~> s1 - s2 *)
  fun subtract (R.Add(p1,s1)) s2 = R.Add(p1, add s1 (sminus s2))
    | subtract p1 s2 = R.Add(p1, sminus s2)

  (* mult_left (a : const) (p2 : prod) : prod ~> a * p *)
  fun mult_left (R.Int(0)) p2 = R.Int(0)
    | mult_left (R.Int(n)) p2 = R.Mult(R.Int(n), p2)

  (* next three functions may be redundant *)
  (* add_right (p1 : prod) (s2 : sum) : sum ~> p1 + s2 *)
  fun add_right p1 (R.Int(0)) = p1
    | add_right p1 s2 = R.Add(p1, s2)

  (* add_left (p1 : prod) (s2 : sum) : sum ~> p1 + s2 *)
  fun add_left (R.Int(0)) s2 = s2
    | add_left p1 s2 = R.Add(p1, s2)

  (* add_lr (p1 : prod) (s2 : sum) : sum ~> p1 + s2 *)
  fun add_lr (R.Int(0)) s2 = s2
    | add_lr p1 (R.Int(0)) = p1
    | add_lr p1 s2 = R.Add(p1,s2)

  (* ccmultiply (a1 : const) (a2 : const) : const ~> a1 * a2 *)
  fun ccmultiply (R.Int(n1)) (R.Int(n2)) = R.Int(n1*n2)

  (* vvmultiply (vs1 : vprod) (vs2 : vprod) : vprod ~> vs1 * vs2 *)
  fun vvmultiply (R.Mult(R.Var(v1),p1)) (R.Mult(R.Var(v2),p2)) =
      if v1 <= v2 (* compare as strings *)
      then R.Mult(R.Var(v1), vvmultiply p1 (R.Mult(R.Var(v2),p2)))
      else R.Mult(R.Var(v2), vvmultiply (R.Mult(R.Var(v1),p1)) p2)
    | vvmultiply (R.Var(v1)) (R.Mult(R.Var(v2), p2)) =
      if v1 <= v2
      then R.Mult(R.Var(v1), R.Mult(R.Var(v2), p2))
      else R.Mult(R.Var(v2), vvmultiply (R.Var(v1)) p2)
    | vvmultiply (R.Mult(R.Var(v1),p1)) (R.Var(v2)) =
      if v1 <= v2
      then R.Mult(R.Var(v1), vvmultiply p1 (R.Var(v2)))
      else R.Mult(R.Var(v2), R.Mult(R.Var(v1), p1))
    | vvmultiply (R.Var(v1)) (R.Var(v2)) =
      if v1 <= v2
      then R.Mult(R.Var(v1), R.Var(v2))
      else R.Mult(R.Var(v2), R.Var(v1))

  (* ppmultiply (p1 : prod) (p2 : prod) : prod ~> p1 * p2 *)
  fun ppmultiply (R.Mult(a1,p1)) (R.Mult(a2,p2)) = R.Mult (ccmultiply a1 a2, vvmultiply p1 p2)
    | ppmultiply (R.Int(n1)) (R.Mult(a2,p2)) = mult_left (ccmultiply (R.Int(n1)) a2) p2
    | ppmultiply (R.Mult(a1,p1)) (R.Int(n2)) = mult_left (ccmultiply a1 (R.Int(n2))) p1
    | ppmultiply (R.Int(n1)) (R.Int(n2)) = ccmultiply (R.Int(n1)) (R.Int(n2))

  (* pmultiply (p1 : prod) (s2 : sum) : sum ~> p1 * s2 *)
  fun pmultiply p1 (R.Add(p2,s2)) = add_lr (ppmultiply p1 p2) (pmultiply p1 s2)
    | pmultiply p1 p2 = ppmultiply p1 p2

  (* smultiply (s1 : sum) (s2 : sum) : sum ~> s1 * s2 *)
  fun smultiply (R.Add(p1,s1)) s2 = add (pmultiply p1 s2) (smultiply s1 s2)
    | smultiply p1 s2 = pmultiply p1 s2

  (* the next function generate strict normal forms *)
  (* add_consts (a1 : const) (a2 : const) : const ~> a1 + a2 (strict) *)
  fun add_consts (R.Int(n1)) (R.Int(n2)) = R.Int(n1+n2)

  (* add_int (a1 : const) (s2 : sum) : sum ~> a1 + s2 (strict) *)
  fun add_int (R.Int(0)) s = s
    | add_int (R.Int(n)) (R.Add(R.Int(k), s2)) = add_left (R.Int(n+k)) s2
    | add_int (R.Int(n)) (R.Add(R.Mult(a,p), s2)) = add_right (R.Mult(a,p)) (add_int (R.Int(n)) s2)
    | add_int (R.Int(n)) (R.Mult(a,p)) = R.Add(R.Mult(a,p), R.Int(n))
    | add_int (R.Int(n)) (R.Int(k)) = R.Int(n+k)

  (* add_prod (p1 : prod) (s2 : sum) : sum ~> p1 + s2 (strict) *)
  fun add_prod (R.Mult(a1,p1)) (R.Add(R.Mult(a2,p2),s2)) =
      if p1 = p2
      then add_left (mult_left (add_consts a1 a2) p2) s2
      else add_right (R.Mult(a2,p2)) (add_prod (R.Mult(a1,p1)) s2)
    | add_prod (R.Mult(a1,p1)) (R.Add(R.Int(n),s2)) =
      add_int (R.Int(n)) (add_prod (R.Mult(a1,p1)) s2) (* add_int because Int(0) may arise *)
    | add_prod (R.Mult(a1,p1)) (R.Mult(a2,p2)) =
      if p1 = p2
      then mult_left (add_consts a1 a2) p2
      else R.Add (R.Mult(a2,p2), R.Mult(a1,p1)) (* neither is a constant *)
    | add_prod (R.Mult(a1,p1)) (R.Int(n)) = R.Add(R.Mult(a1,p1), R.Int(n))

  (* sreduce (s : sum) : sum ~> s', where s' is strictly normal *)
  fun sreduce (R.Add(R.Mult(a,p),s)) = add_prod (R.Mult(a,p)) (sreduce s)
    | sreduce (R.Add(R.Int(n),s)) = add_int (R.Int(n)) (sreduce s)
    | sreduce (R.Mult(a,p)) = R.Mult(a,p)
    | sreduce (R.Int(n)) = R.Int(n)

  (* normalize (e : arith) : sum ~> s, where s is strictly normal *)
  fun normalize (R.Int(n)) = R.Int(n)
    | normalize (R.Add(e1,e2)) = sreduce (add (normalize e1) (normalize e2))
    | normalize (R.Sub(e1,e2)) = sreduce (subtract (normalize e1) (normalize e2))
    | normalize (R.Mult(e1,e2)) = sreduce (smultiply (normalize e1) (normalize e2))
    | normalize (R.Var(v)) = R.Mult(R.Int(1), R.Var(v))

  fun member p1 (R.Add(p2,s2)) = (p1 = p2) orelse member p1 s2
    | member p1 p2 = (p1 = p2)

  fun subset (R.Add(p1,s1)) s2 = member p1 s2 andalso subset s1 s2
    | subset p1 s2 = member p1 s2

  fun compare s1 s2 = subset s1 s2 andalso subset s2 s1

  fun is_zero (R.Int(0)) = true
    | is_zero s = false

  datatype outcome = Valid | NotValid | Unknown

  fun and_ (R.True, phi2) = phi2
    | and_ (phi1, R.True) = phi1
    | and_ (R.False, phi2) = R.False
    | and_ (phi1, R.False) = R.False
    | and_ (phi1, phi2) = R.And(phi1, phi2)

  fun or_ (R.True, phi2) = R.True
    | or_ (phi1, R.True) = R.True
    | or_ (R.False, phi2) = phi2
    | or_ (phi1, R.False) = phi1
    | or_ (phi1, phi2) = R.Or(phi1, phi2)

  fun normalize_prop (R.Eq(e1,e2)) = R.Eq (normalize (R.Sub(e1,e2)), R.Int(0))
    | normalize_prop (R.Lt(e1,e2)) = normalize_prop (R.Gt(e2,e1))
    | normalize_prop (R.Gt(e1,e2)) = R.Gt (normalize (R.Sub(e1,e2)), R.Int(0))
    | normalize_prop (R.Le(e1,e2)) = normalize_prop (R.Ge(e2,e1))
    | normalize_prop (R.Ge(e1,e2)) = R.Ge (normalize (R.Sub(e1,e2)), R.Int(0))
    | normalize_prop (R.Divides(n,e)) = R.Divides(n, normalize e)
    | normalize_prop (R.True) = R.True
    | normalize_prop (R.False) = R.False
    | normalize_prop (R.Or(phi1,phi2)) = or_ (normalize_prop phi1, normalize_prop phi2)
    | normalize_prop (R.And(phi1,phi2)) = and_ (normalize_prop phi1, normalize_prop phi2)
    | normalize_prop (R.Implies(phi1,phi2)) = or_ (normalize_not phi1, normalize_prop phi2)
    | normalize_prop (R.Not(phi)) = normalize_not phi
  and normalize_not (R.Eq(e1,e2)) = R.Not (R.Eq(normalize (R.Sub(e1,e2)), R.Int(0)))
    | normalize_not (R.Lt(e1,e2)) = normalize_prop (R.Ge(e1,e2))
    | normalize_not (R.Gt(e1,e2)) = normalize_prop (R.Le(e1,e2))
    | normalize_not (R.Le(e1,e2)) = normalize_prop (R.Gt(e1,e2))
    | normalize_not (R.Ge(e1,e2)) = normalize_prop (R.Lt(e1,e2))
    | normalize_not (R.Divides(n,e)) = R.Not (R.Divides(n, normalize e))
    | normalize_not (R.True) = R.False
    | normalize_not (R.False) = R.True
    | normalize_not (R.Or(phi1,phi2)) = and_ (normalize_not phi1, normalize_not phi2)
    | normalize_not (R.And(phi1,phi2)) = or_ (normalize_not phi1, normalize_not phi2)
    | normalize_not (R.Implies(phi1,phi2)) = and_ (normalize_prop phi1, normalize_not phi2)
    | normalize_not (R.Not(phi)) = normalize_prop (phi)

  fun all_pos_atom (R.Int(n)) = (n >= 0)
    | all_pos_atom (R.Var(v)) = true
  fun all_pos_prod (R.Mult(s,t)) = all_pos_prod s andalso all_pos_prod t
    | all_pos_prod s = all_pos_atom s
  fun all_pos_sum (R.Add(s,t)) = all_pos_sum s andalso all_pos_sum t
    | all_pos_sum s = all_pos_prod s
  fun all_pos s = all_pos_sum s

  datatype outcome = Valid | NotValid | Unknown

  (* decide_norm (s = t) => compare each coefficient for equality *)
  (* decide_norm (s >= t) => compare each coefficient for >= *)
  fun decide_norm ctx con (R.Eq(s,R.Int(0))) =
      (* if compare s t then Valid else Unknown *)
      if is_zero s then Valid else Unknown
    | decide_norm ctx con (R.Ge(s,R.Int(0))) =
      if all_pos s then Valid else Unknown
    | decide_norm ctx con phi = Unknown
                                
  fun decide ctx con phi =
      let val (con', phi') = R.subst_eq con R.True phi (* substitute out equalities *)
          val phi'' = normalize_prop phi'
      in
          decide_norm ctx con phi''
      end

end  (* structure Normalize *)
