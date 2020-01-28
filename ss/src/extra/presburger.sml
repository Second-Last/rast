(* Presburger arithmetic over natural numbers,
 * restricted to (implicit) prefix quantification
 *)

signature PRESBURGER =
sig
    type varname = string
    type nat = int
               
    datatype arith =
             Int of int
           | Add of arith * arith
           | Sub of arith * arith
           | Mult of int * arith
           | Var of varname

    datatype prop =
             Eq of arith * arith
           | Lt of arith * arith
           | Gt of arith * arith
           | Le of arith * arith
           | Ge of arith * arith
           | Divides of nat * arith
           | True
           | False
           | Or of prop * prop
           | And of prop * prop
           | Implies of prop * prop
           | Not of prop

    type nnf = prop
    val nnf : prop -> nnf
    val elim : varname -> prop -> nnf (* elim x F = G where (exists x. F) <=> G *)
    val elim_nnf : varname -> nnf -> nnf
    val elim_vars : varname list -> nnf -> nnf (* elim xs F = G where (exists xs. F) <=> G *)
    val valid : varname list -> prop list -> prop -> bool   (* valid xs Fs G iff forall xs. Fs |= G *)

    val pp_arith : arith -> string
    val pp_prop : prop -> string

end (* signature PRESBURGER *)

structure Cooper :> PRESBURGER =
struct

    type varname = string
    type nat = int

    datatype arith =
             Int of int
           | Add of arith * arith
           | Sub of arith * arith
           | Mult of int * arith
           | Var of varname

    datatype prop =
             Eq of arith * arith
           | Lt of arith * arith
           | Gt of arith * arith
           | Le of arith * arith
           | Ge of arith * arith
           | Divides of nat * arith
           | True
           | False
           | Or of prop * prop
           | And of prop * prop
           | Implies of prop * prop
           | Not of prop

    type nnf = prop

    fun pp_arith (Int(n)) = Int.toString n
      | pp_arith (Add(s,t)) = "(" ^ pp_arith s ^ "+" ^ pp_arith t ^ ")"
      | pp_arith (Sub(s,t)) = "(" ^ pp_arith s ^ "-" ^ pp_arith t ^ ")"
      | pp_arith (Mult(k,t)) = Int.toString k ^ "*" ^ pp_arith t
      | pp_arith (Var(x)) = x

    fun pp_prop (Eq(s,t)) = pp_arith s ^ " = " ^ pp_arith t
      | pp_prop (Lt(s,t)) = pp_arith s ^ " < " ^ pp_arith t
      | pp_prop (Gt(s,t)) = pp_arith s ^ " > " ^ pp_arith t
      | pp_prop (Le(s,t)) = pp_arith s ^ " <= " ^ pp_arith t
      | pp_prop (Ge(s,t)) = pp_arith s ^ " >= " ^ pp_arith t
      | pp_prop (Divides(n,t)) = Int.toString n ^ "|" ^ pp_arith t
      | pp_prop (True) = "true"
      | pp_prop (False) = "false"
      | pp_prop (Or(F,G)) = "(" ^ pp_prop F ^ " \\/ " ^ pp_prop G ^ ")"
      | pp_prop (And(F,G)) = "(" ^ pp_prop F ^ " /\\ " ^ pp_prop G ^ ")"
      | pp_prop (Implies(F,G)) = "(" ^ pp_prop F ^ " => " ^ pp_prop G ^ ")"
      | pp_prop (Not(F)) = "~" ^ pp_prop F

fun is_prod (Mult(k,Var(x))) = true (* k <> 0 doesn't seem to be necessary *)
  | is_prod _ = false

fun is_linear (Add(p,t)) = is_prod p andalso is_linear t
  | is_linear (Int(k)) = true
  | is_linear s = false

fun mult k (Add(Mult(k',Var(x)),s)) = Add(Mult(k*k',Var(x)), mult k s)
  | mult k (Int(k')) = Int(k*k')

fun add_const c (Add(p,t)) = Add(p, add_const c t)
  | add_const (Int(k)) (Int(k')) = Int(k+k')

fun add_prod (p as Mult(k,Var(x))) (Add(p' as Mult(k', Var(x')), t)) =
    if x = x'
    then if k+k' = 0 then t else Add(Mult(k+k', Var(x')), t)
    else Add(p', add_prod p t)
  | add_prod p (c as Int(k')) = Add(p, c)
                                                    
fun add (Add(p,t)) s = add_prod p (add s t)
  | add (Int(k)) s = add_const (Int(k)) s

fun minus s t = add s (mult (0-1) t)

(* subst x t s, probably not needed *)
(*
fun subst x t (s as Int(k)) = Int(k)
  | subst x t (Add(p as Mult(k,Var(x')), s)) =
    if x = x'
    then add (mult k t) s
    else add_prod (p, subst x t s)
*)

(* linearizing a term *)
fun linearize (s as Int(k)) = s
  | linearize (Add(s,t)) = add (linearize s) (linearize t)
  | linearize (Sub(s,t)) = add (linearize s) (mult (0-1) (linearize t))
  | linearize (Mult(k,t)) = mult k (linearize t)
  | linearize (Var(x)) = Add(Mult(1,Var(x)), Int(0))

(* isolating a variable x in a term *)
(* iso_term x s = (Mult(k,Var(x)), t)
 * assume s is linear, ensures t is linear
 * k is arbitrary, including 0
 *)
fun iso_term x (s as Int(k)) = (Mult(0,Var(x)), s)
  | iso_term x (Add(p' as Mult(k,Var(x')), s)) =
    if x = x' then (p', s)
    else let val (px, t) = iso_term x s
         in (px, Add(p', t)) end

exception NotNNF

(* strict nnf, which requires linear terms *)
fun is_nnf (Lt(s,t)) = is_linear s andalso is_linear t
  | is_nnf (Divides(n,t)) = n > 0 andalso is_linear t
  | is_nnf (True) = true
  | is_nnf (False) = true
  | is_nnf (Or(F,G)) = is_nnf F andalso is_nnf G
  | is_nnf (And(F,G)) = is_nnf F andalso is_nnf G
  | is_nnf (Not(Divides(n,t))) = true
  | is_nnf _ = false

(* transforming a term in strict nnf *)
fun nnf (Eq(s,t)) = let val s' = linearize s
                        val t' = linearize t
                    in And(Lt(s', add_const (Int(1)) t'), Lt(t', add_const (Int(1)) s')) end
  | nnf (Lt(s,t)) = Lt(linearize s, linearize t)
  | nnf (Gt(s,t)) = Lt(linearize t, linearize s)
  | nnf (Le(s,t)) = Lt(linearize s, add_const (Int(1)) (linearize t))
  | nnf (Ge(s,t)) = Lt(linearize t, add_const (Int(1)) (linearize s))
  | nnf (Divides(n,t)) = Divides(n, linearize t)
  | nnf (True) = True
  | nnf (False) = False
  | nnf (Or(F,G)) = Or(nnf F, nnf G)
  | nnf (And(F,G)) = And(nnf F, nnf G)
  | nnf (Implies(F,G)) = Or(nnf_not F, nnf G)
  | nnf (Not(F)) = nnf_not F
and nnf_not (Eq(s,t)) = let val s' = linearize s
                            val t' = linearize t
                        in Or(Lt(s',t'), Lt(t',s')) end
  | nnf_not (Lt(s,t)) = Lt(linearize t, add_const (Int(1)) (linearize s))
  | nnf_not (Gt(s,t)) = Lt(linearize s, add_const (Int(1)) (linearize t))
  | nnf_not (Le(s,t)) = Lt(linearize t, linearize s)
  | nnf_not (Ge(s,t)) = Lt(linearize s, linearize t)
  | nnf_not (Divides(n,t)) = Not(Divides(n,linearize t))
  | nnf_not (True) = False
  | nnf_not (False) = True
  | nnf_not (Or(F,G)) = And(nnf_not F, nnf_not G)
  | nnf_not (And(F,G)) = Or(nnf_not F, nnf_not G)
  | nnf_not (Implies(F,G)) = And(nnf F, nnf_not G)
  | nnf_not (Not(F)) = nnf F

(* is x F = true if is isolated in F, written as F[x] *)
fun is_iso x (Lt(Add(Mult(k,Var(x')),s),Int(0))) =
    x = x' andalso is_linear s
  | is_iso x (Divides(n,Add(Mult(k,Var(x')),s))) =
    n > 0 andalso x = x' andalso is_linear s (* k arbitrary, inluding 0 *)
  | is_iso x (Not(Divides(n,s))) = is_iso x (Divides(n,s))
  | is_iso x (True) = true
  | is_iso x (False) = true
  | is_iso x (Or(F,G)) = is_iso x F andalso is_iso x G
  | is_iso x (And(F,G)) = is_iso x F andalso is_iso x G
  | is_iso x _ = false

(* iso x F = F'[x] where F and F'[x] are in nnf,
   and x is isoloated in F, that is, is_iso x F
 *)
fun iso x (Lt(s,t)) = Lt(Add(iso_term x (minus s t)), Int(0))
  | iso x (Divides(n,t)) = Divides(n, Add(iso_term x t))
  | iso x (Not(Divides(n,t))) = Not(Divides(n, Add(iso_term x t)))
  | iso x True = True
  | iso x False = False
  | iso x (Or(F,G)) = Or(iso x F, iso x G)
  | iso x (And(F,G)) = And(iso x F, iso x G)

fun gcd_nat k 0 = k
  | gcd_nat k l =
    if k < l then gcd_nat k (l mod k)
    else gcd_nat l (k mod l)

fun lcm_nat k l = (k * l) div (gcd_nat k l)

fun lcm_coeff k l =
    if k = 0 then l
    else if k > 0 then lcm_nat k l
    else (* k < 0 *) lcm_nat (0-k) l

(* lcm x F[x] = l, the least common multiple of coefficients of x in F[x] *)
fun lcm x (Lt(Add(Mult(k,_),t),_)) l = lcm_coeff k l
  | lcm x (Divides(n,Add(Mult(k,_),t))) l = lcm_coeff k l
  | lcm x True l = l
  | lcm x False l = l
  | lcm x (Or(F,G)) l = lcm x F (lcm x G l)
  | lcm x (And(F,G)) l = lcm x F (lcm x G l)
  | lcm x (Not(F)) l = lcm x F l

(* lcm_div x F[x] = l, the least common multiple of divisors of x in F[x] *)
fun lcm_div x (Lt(sx,z)) l = l
  | lcm_div x (Divides(n,Add(Mult(k,_),t))) l =
    if k = 0 then l else lcm_coeff n l
  | lcm_div x True l = l
  | lcm_div x False l = l
  | lcm_div x (Or(F,G)) l = lcm_div x F (lcm_div x G l)
  | lcm_div x (And(F,G)) l = lcm_div x F (lcm_div x G l)
  | lcm_div x (Not(F)) l = lcm_div x F l

(* unitize delta x F[x] = F'[x] where all coefficients of x are -1, 0, or 1 *)
fun unitize delta x (F as Lt(Add(Mult(k,Var(x')),t),z)) =
    if k = 0 then F
    else if k > 0 then Lt(Add(Mult(1,Var(x')), mult (delta div k) t), z)
    else (* k < 0 *) Lt(Add(Mult(0-1,Var(x')), mult (delta div (0-k)) t), z)
  | unitize delta x (F as Divides(n, Add(Mult(k,Var(x')),t))) =
    if k = 0 then F
    else if k > 0 then Divides((delta div k) * n, Add(Mult(1, Var(x')), mult (delta div k) t))
    else (* k < 0 *) Divides((delta div (0-k)) * n, Add(Mult(1, Var(x')), mult (delta div k) t)) (* not div (0-k)! *)
  | unitize delta x (True) = True
  | unitize delta x (False) = False
  | unitize delta x (Or(F,G)) = Or (unitize delta x F, unitize delta x G)
  | unitize delta x (And(F,G)) = And (unitize delta x F, unitize delta x G)
  | unitize delta x (Not(F)) = Not (unitize delta x F)

(* collect lower bounds -x + t < 0 *)
fun lbs x (Lt(Add(Mult(k,Var(x')),t),z)) acc =
    if k = 0 then acc
    else if k = 1 then acc
    else (* k = -1 *) t::acc
  | lbs x (Divides _) acc = acc
  | lbs x (True) acc = acc
  | lbs x (False) acc = acc
  | lbs x (Or(F,G)) acc = lbs x F (lbs x G acc)
  | lbs x (And(F,G)) acc = lbs x F (lbs x G acc)
  | lbs x (Not(F)) acc = acc (* F = Divides _ *)

(* subst_prop x t F = G, F must be unitary, G is nnf  *)
(* simplify after substitution? *)
fun subst_prop x t (Lt(Add(Mult(k,Var(x')),s), z)) = (* x = x', z = 0 *)
    if k = 0 then Lt(s,z)
    else Lt(add (mult k t) s, z) (* k = 1 or k = -1 *)
  | subst_prop x t (Divides(n,Add(Mult(k,Var(x')),s))) = (* x = x' *)
    if k = 0 then Divides(n, s)
    else Divides(n, add (mult k t) s) (* k = 1 or k = -1 *)
  | subst_prop x t (True) = True
  | subst_prop x t (False) = False
  | subst_prop x t (Or(F,G)) = Or(subst_prop x t F, subst_prop x t G)
  | subst_prop x t (And(F,G)) = And(subst_prop x t F, subst_prop x t G)
  | subst_prop x t (Not(F)) = Not(subst_prop x t F)

(* disjoin j bset x F[x] G = G or(0 < i <= j, b in bset)(F[b+j]) *)
fun disjoin 0 bset x Fx G = G
  | disjoin j bset x Fx G = disjoin (j-1) bset x Fx (disjoin' j bset x Fx G)
and disjoin' j nil x Fx G = G
  | disjoin' j (b::bset) x Fx G =
    disjoin' j bset x Fx (Or(G, subst_prop x (add_const (Int(j)) b) Fx))

fun or_ True G = True
  | or_ False G = G
  | or_ F True = True
  | or_ F False = F
  | or_ F G = Or(F,G)

fun and_ True G = G
  | and_ False G = False
  | and_ F True = F
  | and_ F False = False
  | and_ F G = And(F,G)

fun not_ True = False
  | not_ False = True
  | not_ F = Not(F)

fun simplify (Lt(Int(k),Int(k'))) = if k < k' then True else False
  | simplify (Lt(s,t)) = Lt(s,t)
  | simplify (Divides(n,Int(k))) = if k mod n = 0 then True else False
  | simplify (True) = True
  | simplify (False) = False
  | simplify (Or(F,G)) = or_ (simplify F) (simplify G)
  | simplify (And(F,G)) = and_ (simplify F) (simplify G)
  | simplify (Not(F)) = not_ (simplify F)

(* elim x F = G, where (exists x. F) <=> G and x does not occur in G
 * assume F is in strict nnf; ensure G is in strict nnf
 * relativize implicit quantifier to express we are solving over nat
 *)
fun elim_nnf x F =
    let 
        val () = if is_nnf F then () else raise NotNNF
        val F = And(Lt(Int(0), Add(Mult(1,Var(x)),Int(1))),F) (* x >= 0  <=>  0 < x+1 *)
        val Fx = iso x F
        val delta = lcm x Fx 1
        val Fx = And(unitize delta x Fx, Divides(delta, Add(Mult(1,Var(x)),Int(0))))
        val delta_div = lcm_div x Fx 1
        val bset = lbs x Fx nil
        (* for natural numbers, do not calculate F-infinity *)
        (* now calculate or(j=1..delta_div, b in bset)(F'x[b+j]) *)
        val G = disjoin delta_div bset x Fx False
        val G = simplify G
    in
        G
    end

fun elim x F = elim_nnf x (nnf F)

(* ctx ; con |= phi
 * <=> forall ctx. con => phi
 * <=> not exists ctx. not (con => phi)
 * <=> not exists ctx. con /\ not phi
 *)
(* elim_vars xs F = G, assuming F is in strict normal form *)
(* G = True | False if xs contains all variables in F *)
fun elim_vars nil F = F
  | elim_vars (x::xs) F = elim_vars xs (elim_nnf x F)

fun valid xs con phi =
    let val F = List.foldr And (Not(phi)) con
        val F = nnf F           (* convert to strict normal form *)
        val F = simplify F      (* only useful if xs = [] *)
        val G = elim_vars xs F
    in case G
        of True => false
         | False => true
    end

end (* structure Cooper *)

(* simple unit test *)

structure CooperTest =
struct

local
open Cooper
in

val true = valid ["x"] [] (Eq(Var("x"),Var("x")))
val true = valid ["x"] [Gt(Var("x"),Int(1))] (Gt(Var("x"),Int(0)))
val false = valid ["x"] [Gt(Var("x"),Int(0))] (Gt(Var("x"),Int(1)))

val True = elim "x" (Gt(Var("x"), Int(0)))
val True = elim "x" (Lt(Mult(0-1,Var("x")), Int(0)))
val True = elim_vars ["x","y"] (nnf (Lt(Var("x"), Var("y"))))
(* from Hansen 2010 *)
val True = elim "x" (And(Or(Lt(Add(Mult(3,Var("x")),Int(1)),Int(10)),
                            Gt(Sub(Mult(7,Var("x")),Int(6)),Int(7))),
                         Divides(2,Var("x"))))

end

end (* struct CooperTest *)
