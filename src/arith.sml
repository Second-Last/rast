(* Presburger arithmetic over natural numbers,
 * restricted to (implicit) prefix quantification
 *)

signature ARITH =
sig
    type varname = string       (* x *)
    type pos = int              (* > 0 *)
               
    datatype arith =
             Int of int            (* ..., -1, 0, 1, ... *)
           | Add of arith * arith  (* e1 + e2 *)
           | Sub of arith * arith  (* e1 - e2 *)
           | Mult of arith * arith (* e1 * e2 *)
           | Var of varname        (* x *)

    datatype prop =
             Eq of arith * arith    (* e1 = e2 *)
           | Lt of arith * arith    (* e1 < e2 *)
           | Gt of arith * arith    (* e1 > e2 *)
           | Le of arith * arith    (* e1 <= e2 *)
           | Ge of arith * arith    (* e1 >= e2 *)
           | Divides of pos * arith (* n | e *)
           | True                   (* true *)
           | False                  (* false *)
           | Or of prop * prop      (* phi1 \/ phi2 *)
           | And of prop * prop     (* phi1 /\ phi2 *)
           | Implies of prop * prop (* phi1 => phi2 *)
           | Not of prop            (* ~ phi *)

    type ctx = varname list             (* ctx = x1,...,xn *)
    type subst = (varname * arith) list (* sigma = e1/x1,...,en/xn *)
    exception NotClosed

    (* contexts and variables *)
    val closed : ctx -> arith -> bool
    val closed_prop : ctx -> prop -> bool

    val free_vars : arith -> ctx -> ctx
    val free_varlist : arith list -> ctx -> ctx
    val free_prop : prop -> ctx -> ctx

    val zip : ctx -> arith list -> subst               (* x1,...,xn\e1,...,en *)
                                                       (* may raise ListPair.UnequalLengths *)
    val apply : subst -> arith -> arith                (* [sigma]e *)
    val apply_list : subst -> arith list -> arith list (* [sigma](e1,...,en) *)
    val apply_prop : subst -> prop -> prop             (* [sigma]phi *)

    val create_idx : ctx -> arith list                 (* {x1}...{xn} *)

    val evaluate : arith -> int                        (* may raise NotClosed *)
    val evaluate_prop : prop -> bool                   (* may raise NotClosed *)

    val plus : arith * arith -> arith                  (* preserve integer values *)
    val minus : arith * arith -> arith                 (* preserve integer values *)

    (* Presburger arithmetic *)
    exception NonLinear

    type nnf = prop                   (* propositions in negation normal form *)
    val nnf : prop -> nnf             (* may raise NonLinear *)
    val elim : varname -> prop -> nnf (* elim x F = G where (exists x. F) <=> G *)
    val elim_nnf : varname -> nnf -> nnf
    val elim_vars : varname list -> nnf -> nnf
                                      (* elim xs F = G where (exists xs. F) <=> G *)

    val valid : varname list -> prop -> prop -> bool (* may raise NonLinear *)
                                      (* valid xs F G iff forall xs. F |= G *)

    (* quantification, eagerly eliminated by decision procedure *)
    val exists : varname -> nnf -> nnf  (* exists x F = G where (exists x.F) <=> G *)
    val forall : varname -> nnf -> nnf  (* forall x F = G where (forall x.F) <=> G *)

    structure Print :
    sig
        val pp_arith : arith -> string
        val pp_prop : prop -> string
    end

end (* signature Arith *)

structure Arith :> ARITH =
struct

type varname = string           (* x *)
type pos = int                  (* > 0 *)

datatype arith =
         Int of int            (* ..., -1, 0, 1, ... *)
       | Add of arith * arith  (* e1 + e2 *)
       | Sub of arith * arith  (* e1 - e2 *)
       | Mult of arith * arith (* e1 * e2 *)
       | Var of varname        (* x *)

datatype prop =
         Eq of arith * arith    (* e1 = e2 *)
       | Lt of arith * arith    (* e1 < e2 *)
       | Gt of arith * arith    (* e1 > e2 *)
       | Le of arith * arith    (* e1 <= e2 *)
       | Ge of arith * arith    (* e1 >= e2 *)
       | Divides of pos * arith (* n | e *)
       | True                   (* true *)
       | False                  (* false *)
       | Or of prop * prop      (* phi1 \/ phi2 *)
       | And of prop * prop     (* phi1 /\ phi2 *)
       | Implies of prop * prop (* phi1 => phi2 *)
       | Not of prop            (* ~ phi *)

type ctx = varname list
type subst = (varname * arith) list
exception NotClosed

fun closed ctx (Int(n)) = true
  | closed ctx (Add(e1,e2)) = closed ctx e1 andalso closed ctx e2
  | closed ctx (Sub(e1,e2)) = closed ctx e1 andalso closed ctx e2
  | closed ctx (Mult(e1,e2)) = closed ctx e1 andalso closed ctx e2
  | closed ctx (Var(v)) = List.exists (fn v' => v = v') ctx

fun closed_list ctx nil = true
  | closed_list ctx (e::es) = closed ctx e andalso closed_list ctx es

fun closed_prop ctx (Eq(e1,e2)) = closed ctx e1 andalso closed ctx e2
  | closed_prop ctx (Lt(e1,e2)) = closed ctx e1 andalso closed ctx e2
  | closed_prop ctx (Gt(e1,e2)) = closed ctx e1 andalso closed ctx e2
  | closed_prop ctx (Ge(e1,e2)) = closed ctx e1 andalso closed ctx e2
  | closed_prop ctx (Le(e1,e2)) = closed ctx e1 andalso closed ctx e2
  | closed_prop ctx (Divides(n,e)) = closed ctx e
  | closed_prop ctx (True) = true
  | closed_prop ctx (False) = false
  | closed_prop ctx (Or(F,G)) = closed_prop ctx F andalso closed_prop ctx G
  | closed_prop ctx (Implies(F,G)) = closed_prop ctx F andalso closed_prop ctx G
  | closed_prop ctx (Not(F)) = closed_prop ctx F

fun free_vars (Int(n)) ctx = ctx
  | free_vars (Add(s,t)) ctx = free_vars t (free_vars s ctx)
  | free_vars (Sub(s,t)) ctx = free_vars t (free_vars s ctx)
  | free_vars (Mult(s,t)) ctx = free_vars t (free_vars s ctx)
  | free_vars (Var(v)) ctx =
    if List.exists (fn v' => v = v') ctx
    then ctx
    else v::ctx

fun free_varlist nil ctx = ctx
  | free_varlist (e::es) ctx = free_varlist es (free_vars e ctx)

fun free_prop (Eq(e1,e2)) ctx = free_vars e2 (free_vars e1 ctx)
  | free_prop (Lt(e1,e2)) ctx = free_vars e2 (free_vars e1 ctx)
  | free_prop (Gt(e1,e2)) ctx = free_vars e2 (free_vars e1 ctx)
  | free_prop (Le(e1,e2)) ctx = free_vars e2 (free_vars e1 ctx)
  | free_prop (Ge(e1,e2)) ctx = free_vars e2 (free_vars e1 ctx)
  | free_prop (Divides(_,e)) ctx = free_vars e ctx
  | free_prop (True) ctx = ctx
  | free_prop (False) ctx = ctx
  | free_prop (Or(phi1,phi2)) ctx = free_prop phi2 (free_prop phi1 ctx)
  | free_prop (And(phi1,phi2)) ctx = free_prop phi2 (free_prop phi1 ctx)
  | free_prop (Implies(phi1,phi2)) ctx = free_prop phi2 (free_prop phi1 ctx)
  | free_prop (Not(phi)) ctx = free_prop phi ctx

(* requires: length ctx = length es; raises ListPair.UnequalLengths otherwise *)
fun zip ctx es = ListPair.zipEq (ctx, es)

(* find sg v' = [sg]v' *)
(* assumed sg : ctx and ctx |- v' nat *)
fun find ((v,e)::sg) v' =
    if (v = v') then e else find sg v'

(* apply sg e = [sg]e *)
(* assumes sg : ctx and ctx |- e : int *)
fun apply sg (e as Int(k)) = e
  | apply sg (Add(e1,e2)) = Add(apply sg e1, apply sg e2)
  | apply sg (Sub(e1,e2)) = Sub(apply sg e1, apply sg e2)
  | apply sg (Mult(e1,e2)) = Mult(apply sg e1, apply sg e2)
  | apply sg (Var(v)) = find sg v

exception NotClosed

fun apply_list sg es = List.map (fn e => apply sg e) es

(* apply_prog sg F = [sg]F *)
(* assumes sg : ctx and ctx |- F prop *)
fun apply_prop sg (Eq(e1,e2)) = Eq(apply sg e1, apply sg e2)
  | apply_prop sg (Lt(e1,e2)) = Lt(apply sg e1, apply sg e2)
  | apply_prop sg (Gt(e1,e2)) = Gt(apply sg e1, apply sg e2)
  | apply_prop sg (Le(e1,e2)) = Le(apply sg e1, apply sg e2)
  | apply_prop sg (Ge(e1,e2)) = Ge(apply sg e1, apply sg e2)
  | apply_prop sg (Divides(n,e)) = Divides(n, apply sg e)
  | apply_prop sg (True) = True
  | apply_prop sg (False) = False
  | apply_prop sg (Or(F,G)) = Or(apply_prop sg F, apply_prop sg G)
  | apply_prop sg (And(F,G)) = And(apply_prop sg F, apply_prop sg G)
  | apply_prop sg (Implies(F,G)) = Implies(apply_prop sg F, apply_prop sg G)
  | apply_prop sg (Not(F)) = Not(apply_prop sg F)

fun create_idx vs = List.map (fn v => Var(v)) vs

(* evaluate e = k if e |->* k *)
(* assumes . |- e int, raises NotClosed otherwise *)
fun evaluate (Int(k)) = k
  | evaluate (Add(e1,e2)) = (evaluate e1) + (evaluate e2)
  | evaluate (Sub(e1,e2)) = (evaluate e1) - (evaluate e2)
  | evaluate (Mult(e1,e2)) = (evaluate e1) * (evaluate e2)
  | evaluate (Var(v)) = raise NotClosed

(* evaluate F = b if F |->* b *)
(* assumes . |- F prop, raises NotClosed otherwise *)
fun evaluate_prop (Eq(e1,e2)) = (evaluate e1 = evaluate e2)
  | evaluate_prop (Lt(e1,e2)) = (evaluate e1 < evaluate e2)
  | evaluate_prop (Gt(e1,e2)) = (evaluate e1 > evaluate e2)
  | evaluate_prop (Le(e1,e2)) = (evaluate e1 <= evaluate e2)
  | evaluate_prop (Ge(e1,e2)) = (evaluate e1 >= evaluate e2)
  | evaluate_prop (Divides(n,e)) = ((evaluate e) mod n = 0)
  | evaluate_prop (True) = true
  | evaluate_prop (False) = false
  | evaluate_prop (Or(F,G)) = evaluate_prop F orelse evaluate_prop G
  | evaluate_prop (And(F,G)) = evaluate_prop F andalso evaluate_prop G
  | evaluate_prop (Implies(F,G)) = (not (evaluate_prop F)) orelse evaluate_prop G
  | evaluate_prop (Not(F)) = not (evaluate_prop F)

fun plus (e1, e2) =
    Int(evaluate(Add(e1,e2)))
    handle NotClosed => Add(e1,e2)

fun minus (e1, e2) =
    Int(evaluate(Sub(e1,e2)))
    handle NotClosed => Sub(e1,e2)

(* Printing *)
(* Defined earlier so that it can be used to instrument
 * the Presburger decision procedure
 *)
structure Print =
struct

    fun pp_arith (Int(n)) = if n >= 0 then Int.toString n else "0-" ^ Int.toString (0-n)
      | pp_arith (Add(s,t)) = "(" ^ pp_arith s ^ "+" ^ pp_arith t ^ ")"
      | pp_arith (Sub(s,t)) = "(" ^ pp_arith s ^ "-" ^ pp_arith t ^ ")"
      | pp_arith (Mult(s,t)) = "(" ^ pp_arith s ^ "*" ^ pp_arith t ^ ")"
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

end (* structure Print *)

(* Decision procedure for Presburger arithmetic using Cooper's algorithm *)
(* Current restrictions:
 * Quantifiers must range over natural numbers (F-infinity is not constructed)
 * Only implicit existential quantifiers
 * Universals can be obtained by |= forall x. F iff |= ~exists x. ~F
 *
 * s is a constant k if k is an integer (including 0)
 * s is a product p if it has the form k*x
 * s,t is linear if it has form k1*x1 + ... + kn*xn + k, xi all distinct
 *)

type nnf = prop
exception NonLinear

(* is_prod (k*x) where integer k may be 0 *)
(* write p for products *)
fun is_prod (Mult(Int(k),Var(x))) = true
  | is_prod _ = false

(* is_linear (k1*x1 + ... + kn*xn + k) *)
fun is_linear (Add(p,t)) = is_prod p andalso is_linear t
  | is_linear (Int(k)) = true
  | is_linear s = false

(* the functions below assume arguments s, t are linear,
 * ensure results are linear
 *)

(* mult_const k t = lin(k*t) *)
fun mult_const k (Add(Mult(Int(k'),Var(x)),t)) = Add(Mult(Int(k*k'),Var(x)), mult_const k t)
  | mult_const k (Int(k')) = Int(k*k')

(* add_const k t = lin(k+t) *)
fun add_const c (Add(p,t)) = Add(p, add_const c t)
  | add_const (Int(k)) (Int(k')) = Int(k+k')

(* add_prod p t = lin(p+t) *)
fun add_prod (p as Mult(Int(k),Var(x))) (Add(p' as Mult(Int(k'), Var(x')), t)) =
    if x = x'
    then if k+k' = 0 then t else Add(Mult(Int(k+k'), Var(x')), t) (* check for 0 is optional *)
    else Add(p', add_prod p t)
  | add_prod p (c as Int(k')) = Add(p, c)

(* add s t = lin(s+t) *)
fun add (Add(p,s)) t = add_prod p (add s t)
  | add (Int(k)) t = add_const (Int(k)) t

(* mult_prod_prod p p' = lin(p * p') *)
(* raises NonLinear if result is not linear, that is, neither p nor p' are 0 *)
fun mult_prod_prod (Mult(Int(0), _)) (Mult _) = Int(0) (* save linearity *)
  | mult_prod_prod (Mult _) (Mult(Int(0), _)) = Int(0) (* save linearity *)
  | mult_prod_prod _ _ = raise NonLinear

(* mult_prod p t = lin(p * t) *)
(* raises NonLinear if result is not linear *)
fun mult_prod p (Add(p',t)) = add (mult_prod_prod p p') (mult_prod p t)
  | mult_prod (Mult(Int(k),Var(x))) (Int(k')) = Mult(Int(k*k'),Var(x))

(* mult s t = lin(s * t), raises NonLinear if result is not linear *)
fun mult (Add(p,s)) t = add (mult_prod p t) (mult s t)
  | mult (Int(k)) t = mult_const k t

(* sub s t = lin(s - t) *)
fun sub s t = add s (mult_const (0-1) t)

(* subst x t s = lin([t/x]s), probably not needed *)
(*
fun subst x t (s as Int(k)) = Int(k)
  | subst x t (Add(p as Mult(Int(k),Var(x')), s)) =
    if x = x'
    then add (mult_const k t) s  (* by uniqueness of variables in linear form *)
    else add_prod p (subst x t s)
*)

(* linearize s = lin(t), may raise NonLinear *)
fun linearize (s as Int(k)) = s
  | linearize (Add(s,t)) = add (linearize s) (linearize t)
  | linearize (Sub(s,t)) = sub (linearize s) (linearize t)
  | linearize (Mult(s,t)) = mult (linearize s) (linearize t)
  | linearize (Var(x)) = Add(Mult(Int(1),Var(x)), Int(0))

(* isolating a variable x in a term *)

(* iso_term x s = (k*x, t) where s = k*x + t and x does not occur in t
 * k will be 0 if x does not occur in s
 * assume s is linear, ensure t is linear
 *)
fun iso_term x (s as Int(k)) = (Mult(Int(0),Var(x)), s)
  | iso_term x (Add(p' as Mult(Int(k'),Var(x')), s)) =
    if x = x' then (p', s)
    else let val (kx, t) = iso_term x s
         in (kx, Add(p', t)) end

(* strict nnf, where s, t are in linear form, n > 0
 * M,N ::= s < t | (n|s) | ~(n|s) | True | False | M \/ N | M /\ N 
 *)

exception NotNNF

(* strict nnf, which requires linear terms *)
fun is_nnf (Lt(s,t)) = is_linear s andalso is_linear t
  | is_nnf (Divides(n,t)) = n > 0 andalso is_linear t
  | is_nnf (Not(Divides(n,t))) = n > 0 andalso is_linear t
  | is_nnf (True) = true
  | is_nnf (False) = true
  | is_nnf (Or(F,G)) = is_nnf F andalso is_nnf G
  | is_nnf (And(F,G)) = is_nnf F andalso is_nnf G
  | is_nnf _ = false

(* transforming a proposition into strict nnf *)
(* nnf F = M, may raise NotLinear *)
fun nnf (Eq(s,t)) =
    (* (s = t) <=> (s < t+1 /\ t < s+1) *)
    let val s' = linearize s
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
and nnf_not (Eq(s,t)) =
    (* (s <> t) <=> (s < t \/ t < s) *)
    let val s' = linearize s
        val t' = linearize t
    in Or(Lt(s',t'), Lt(t',s')) end
  | nnf_not (Lt(s,t)) = Lt(linearize t, add_const (Int(1)) (linearize s)) (* s >= t *)
  | nnf_not (Gt(s,t)) = Lt(linearize s, add_const (Int(1)) (linearize t)) (* s <= t *)
  | nnf_not (Le(s,t)) = Lt(linearize t, linearize s) (* s > t *)
  | nnf_not (Ge(s,t)) = Lt(linearize s, linearize t) (* s < t *)
  | nnf_not (Divides(n,t)) = Not(Divides(n,linearize t))
  | nnf_not (True) = False
  | nnf_not (False) = True
  | nnf_not (Or(F,G)) = And(nnf_not F, nnf_not G)
  | nnf_not (And(F,G)) = Or(nnf_not F, nnf_not G)
  | nnf_not (Implies(F,G)) = And(nnf F, nnf_not G) (* ~(F => G) <=> F /\ ~G *)
  | nnf_not (Not(F)) = nnf F

(* x is isolated in F if F is in strict nnf
 * and all atomic propositions have the form
 * k*x + s < 0 or n|k*x or ~(n|(k*x + s))
 * for this particular x (where k may be 0)
 * we write F[x] if x is isolated in F
 *)

(* is x F = true if is isolated in F, written as F[x] *)
fun is_iso x (Lt(Add(Mult(Int(k),Var(x')),s),Int(0))) =
    x = x' andalso is_linear s
  | is_iso x (Divides(n,Add(Mult(Int(k),Var(x')),s))) =
    n > 0 andalso x = x' andalso is_linear s (* k arbitrary, including 0 *)
  | is_iso x (Not(Divides(n,s))) = is_iso x (Divides(n,s))
  | is_iso x (True) = true
  | is_iso x (False) = true
  | is_iso x (Or(F,G)) = is_iso x F andalso is_iso x G
  | is_iso x (And(F,G)) = is_iso x F andalso is_iso x G
  | is_iso x _ = false

(* iso x F = F'[x] where F and F'[x] are in strict nnf,
   and F <=> F'[x]
 *)
fun iso x (Lt(s,t)) = Lt(Add(iso_term x (sub s t)), Int(0))
  | iso x (Divides(n,t)) = Divides(n, Add(iso_term x t))
  | iso x (Not(Divides(n,t))) = Not(Divides(n, Add(iso_term x t)))
  | iso x True = True
  | iso x False = False
  | iso x (Or(F,G)) = Or(iso x F, iso x G)
  | iso x (And(F,G)) = And(iso x F, iso x G)

(* computation of least common multiple, on natural numbers only *)
(* we don't worry about overflow (here or anywhere else...) *)
fun gcd_nat k 0 = k
  | gcd_nat k l =
    if k < l then gcd_nat k (l mod k)
    else gcd_nat l (k mod l)

fun lcm_nat k l = (k * l) div (gcd_nat k l)

fun lcm_coeff k l =
    if k = 0 then l             (* ignore coefficients 0 *)
    else if k > 0 then lcm_nat k l
    else (* k < 0 *) lcm_nat (0-k) l

(* lcm x F[x] l = l', the least common multiple of l and
 * the absolute values of coefficients of x in F[x]
 *)
fun lcm x (Lt(Add(Mult(Int(k),_),t),_)) l = lcm_coeff k l
  | lcm x (Divides(n,Add(Mult(Int(k),_),t))) l = lcm_coeff k l
  | lcm x (Not(F)) l = lcm x F l
  | lcm x True l = l
  | lcm x False l = l
  | lcm x (Or(F,G)) l = lcm x F (lcm x G l)
  | lcm x (And(F,G)) l = lcm x F (lcm x G l)

(* lcm_div x F[x] l = l', the least common multiple of l and
 * the divisors of k*x in F[x]
 *)
fun lcm_div x (Lt(kx,z)) l = l
  | lcm_div x (Divides(n,Add(Mult(Int(k),_),t))) l =
    if k = 0 then l else lcm_coeff n l
  | lcm_div x True l = l
  | lcm_div x False l = l
  | lcm_div x (Or(F,G)) l = lcm_div x F (lcm_div x G l)
  | lcm_div x (And(F,G)) l = lcm_div x F (lcm_div x G l)
  | lcm_div x (Not(F)) l = lcm_div x F l

(* unitize delta x F[x] = F'[x] with (exists x.F[x]) <=> exists x.F'[x]
 * given delta = lcm x F[x] 1
 * where all coefficients of x in F'[x] are -1, 0, or 1
 *)
fun unitize delta x (F as Lt(Add(Mult(Int(k),_),t), z)) = (* z = 0 *)
    if k = 0 then F
    else if k > 0 then Lt(Add(Mult(Int(1),Var(x)), mult_const (delta div k) t), z)
    else (* k < 0 *) Lt(Add(Mult(Int(0-1),Var(x)), mult_const (delta div (0-k)) t), z)
  | unitize delta x (F as Divides(n, Add(Mult(Int(k),_),t))) =
    if k = 0 then F
    else if k > 0 then Divides((delta div k)*n, Add(Mult(Int(1), Var(x)), mult_const (delta div k) t))
    else (* k < 0 *)
        Divides((delta div (0-k))*n, Add(Mult(Int(1), Var(x)), mult_const (delta div k) t)) (* not div (0-k)! *)
  | unitize delta x (Not(F)) = Not (unitize delta x F)
  | unitize delta x (True) = True
  | unitize delta x (False) = False
  | unitize delta x (Or(F,G)) = Or (unitize delta x F, unitize delta x G)
  | unitize delta x (And(F,G)) = And (unitize delta x F, unitize delta x G)

(* collect lower bounds -x + t < 0 *)
(* lbs x F[x] = {t | -x + t < 0 in F[x]} *)
fun lbs x (Lt(Add(Mult(Int(k),_),t),_)) acc =
    if k = 0 then acc
    else if k = 1 then acc
    else (* k = -1 *) t::acc
  | lbs x (Divides _) acc = acc
  | lbs x (Not(Divides _)) acc = acc
  | lbs x (True) acc = acc
  | lbs x (False) acc = acc
  | lbs x (Or(F,G)) acc = lbs x F (lbs x G acc)
  | lbs x (And(F,G)) acc = lbs x F (lbs x G acc)

(* subst_prop x t F[x] = G, F[x] must be unitary, G is strict nnf *)
fun subst_prop x t (Lt(Add(Mult(Int(k),Var(x')),s), z)) = (* x = x', z = 0 *)
    if k = 0 then Lt(s,z)
    else Lt(add (mult_const k t) s, z) (* k = 1 or k = -1 *)
  | subst_prop x t (Divides(n,Add(Mult(Int(k),Var(x')),s))) = (* x = x' *)
    if k = 0 then Divides(n, s)
    else Divides(n, add (mult_const k t) s) (* k = 1 or k = -1 *)
  | subst_prop x t (Not(F)) = Not(subst_prop x t F)
  | subst_prop x t (True) = True
  | subst_prop x t (False) = False
  | subst_prop x t (Or(F,G)) = Or(subst_prop x t F, subst_prop x t G)
  | subst_prop x t (And(F,G)) = And(subst_prop x t F, subst_prop x t G)

(* disjoin j bset x F[x] G = G' where G' <=> \/(0 < i <= j, b in bset)(F[b+j]) *)
(* F[x] is unitary in x, G is strict nnf, G' will be strict nnf *)
fun disjoin 0 bset x Fx G = G
  | disjoin j bset x Fx G = disjoin (j-1) bset x Fx (disjoin' j bset x Fx G)
and disjoin' j nil x Fx G = G
  | disjoin' j (b::bset) x Fx G =
    disjoin' j bset x Fx (Or(G, subst_prop x (add_const (Int(j)) b) Fx))

(* simplification *)
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
  | simplify (Divides(n,t)) = Divides(n,t)
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
        val () = if is_nnf F then () else raise NotNNF (* redundant assertion *)
        val F = And(Lt(Int(0), Add(Mult(Int(1),Var(x)),Int(1))),F) (* x >= 0  <=>  0 < x+1 *)
        val Fx = iso x F
        val delta = lcm x Fx 1
        val Fx = And(unitize delta x Fx, Divides(delta, Add(Mult(Int(1),Var(x)),Int(0))))
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
    let val F = And(Not(phi), con)
        val F = nnf F           (* convert to strict normal form *)
        val F = simplify F      (* only useful if xs = [] *)
        val G = elim_vars xs F
    in case G
        of True => false
         | False => true
         | G => ( print ("constraint " ^ List.foldl (fn (x,s) => x ^ " " ^ s) "" xs ^ " |= "
                         ^ Print.pp_prop G ^ " not simplified to True or False\n")
                ; print ("this indicates an internal error in the type-checker\n")
                ; raise Match )
    end

(* neg nnF = nnG *)
fun neg F = nnf (Not(F))        (* optimize? *)

fun exists x F = elim_nnf x F
fun forall x F = neg (elim_nnf x (neg F))

end (* structure Arith *)

(* Simple unit test *)
(*
structure ArithTest =
struct

local
open Arith
in

val true = valid ["x"] True (Eq(Var("x"),Var("x")))
val true = valid ["x"] (Gt(Var("x"),Int(1))) (Gt(Var("x"),Int(0)))
val false = valid ["x"] (Gt(Var("x"),Int(0))) (Gt(Var("x"),Int(1)))

val True = elim "x" (Gt(Var("x"), Int(0)))
val True = elim "x" (Lt(Mult(Int(0-1),Var("x")), Int(0)))
val True = elim_vars ["x","y"] (nnf (Lt(Var("x"), Var("y"))))
(* from Hansen 2010 *)
val True = elim "x" (And(Or(Lt(Add(Mult(Int(3),Var("x")),Int(1)),Int(10)),
                            Gt(Sub(Mult(Int(7),Var("x")),Int(6)),Int(7))),
                         Divides(2,Var("x"))))

end

end (* struct ArithTest *)
*)
