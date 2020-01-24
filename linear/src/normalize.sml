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

  (* R.Int can be applied to negative numbers here *)
  fun check_atom (R.Int(n)) = true
    | check_atom (R.Var(v)) = true
    | check_atom e = false

  fun check_prod (R.Mult(e1,e2)) = check_atom e1 andalso check_prod e2
    | check_prod e = check_atom e

  fun check_sum (R.Add(e1,e2)) = check_prod e1 andalso check_sum e2
    | check_sum e = check_prod e

  fun check_normal e = check_sum e

  fun add (R.Add(p1,s1)) s2 = R.Add(p1, add s1 s2)
    | add p1 s2 = R.Add(p1,s2)

  fun aminus (R.Int(n)) = R.Int(0-n)

  fun pminus (R.Mult(R.Var(v),p)) = R.Mult(R.Int(0-1), R.Mult(R.Var(v), p))
    | pminus (R.Mult(a,p)) = R.Mult(aminus a,p)
    | pminus a = aminus a

  fun sminus (R.Add(p,s)) = R.Add(pminus p, sminus s)
    | sminus p = pminus p

  fun subtract (R.Add(p1,s1)) s2 = R.Add(p1, add s1 (sminus s2))
    | subtract p1 s2 = R.Add(p1, sminus s2)

  fun ppmultiply (R.Mult(a1,p1)) p2 = R.Mult(a1, ppmultiply p1 p2)
    | ppmultiply a p = R.Mult(a,p)

  fun pmultiply p1 (R.Add(p2,s2)) = R.Add(ppmultiply p1 p2, pmultiply p1 s2)
    | pmultiply p1 p2 = ppmultiply p1 p2

  fun smultiply (R.Add(p1,s1)) s2 = add (pmultiply p1 s2) (smultiply s1 s2)
    | smultiply p1 s2 = pmultiply p1 s2

  fun insert (v:string) nil = [v]
    | insert v (v'::vs') = if (v <= v') then v::v'::vs'
                           else v'::(insert v vs')

  fun mult_left (R.Int(0)) e2 = R.Int(0)
    | mult_left e1 e2 = R.Mult(e1, e2)

  fun add_right e1 (R.Int(0)) = e1
    | add_right e1 e2 = R.Add(e1, e2)
  fun add_left (R.Int(0)) e2 = e2
    | add_left e1 e2 = R.Add(e1, e2)

  fun coeff c vs (R.Mult(R.Int(n),p)) = coeff (c*n) vs p
    | coeff c vs (R.Mult(R.Var(v),p)) = coeff c (insert v vs) p
    | coeff c vs (R.Int(n)) = (c*n,vs)
    | coeff c vs (R.Var(v)) = (c, insert v vs)

  fun create_term nil = R.Int(1)
    | create_term [v] = R.Var(v)
    | create_term (v::vs) = R.Mult(R.Var(v), create_term vs)

  fun add_coeff (R.Int(n1)) (R.Int(n2)) = R.Int(n1+n2)

  fun addin (a1,p1) (R.Add(R.Mult(a2,p2),s2)) = if (p1 = p2) then add_left (mult_left (add_coeff a1 a2) p1) s2
                                                else add_right (R.Mult(a2,p2)) (addin (a1,p1) s2)
    | addin (a1,p1) (R.Mult(a2,p2)) = if (p1 = p2) then mult_left (add_coeff a1 a2) p1
                                      else add_right (R.Mult(a2,p2)) (mult_left a1 p1)
    | addin (a1,p1) (R.Int(0)) = R.Mult(a1,p1)

  fun sreduce (R.Add(p,s)) =
      let val s' = sreduce s
          val (c,vs) = coeff 1 nil p
          val a = R.Int(c)
          val p' = create_term vs
      in
          addin (a,p') s'
      end
    | sreduce p =
      let val (c,vs) = coeff 1 nil p
          val a = R.Int(c)
          val p' = create_term vs
      in
          mult_left a p'
      end

  fun areduce (R.Int(n)) = R.Mult(R.Int(n), create_term nil)
    | areduce (R.Var(v)) = R.Mult(R.Int(1), create_term [v])

  fun normalize (R.Int(n)) = areduce (R.Int(n))
    | normalize (R.Add(e1,e2)) = sreduce (add (normalize e1) (normalize e2))
    | normalize (R.Sub(e1,e2)) = sreduce (subtract (normalize e1) (normalize e2))
    | normalize (R.Mult(e1,e2)) = sreduce (smultiply (normalize e1) (normalize e2))
    | normalize (R.Var(v)) = areduce (R.Var(v))

  fun member p1 (R.Add(p2,s2)) = (p1 = p2) orelse member p1 s2
    | member p1 p2 = (p1 = p2)

  fun subset (R.Add(p1,s1)) s2 = member p1 s2 andalso subset s1 s2
    | subset p1 s2 = member p1 s2

  fun compare s1 s2 = subset s1 s2 andalso subset s2 s1

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

  fun normalize_prop (R.Eq(e1,e2)) = R.Eq (normalize e1, normalize e2)
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
  and normalize_not (R.Eq(e1,e2)) = R.Not (R.Eq(normalize e1, normalize e2))
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
  fun decide_norm ctx con (R.Eq(s,t)) =
      if compare s t then Valid else Unknown
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
