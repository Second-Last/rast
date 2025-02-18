(* Presburger arithmetic over natural numbers *)
(* Authors: Frank Pfenning <fp@cs.cmu.edu>
 *          Ankush Das <ankushd@cs.cmu.edu>
 *)

(* 
 * This implements Cooper's algorithm for quantifier
 * elimination.  Quantification is not explicit in the
 * syntax at the moment.  Instead, there are functions
 * to construct equivalent quantifier-free propositions.
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
    type subst = (varname * arith) list (* sigma = (e1/x1,...,en/xn) *)

    exception NotClosed

    (* contexts and variables *)
    val closed : ctx -> arith -> bool                  (* check if arith is closed under ctx *)
    val closed_prop : ctx -> prop -> bool              (* check if prop is closed under ctx *)

    val free_vars : arith -> ctx -> ctx                (* free variables of arith *)
    val free_varlist : arith list -> ctx -> ctx        (* free variables of a list of arith *)
    val free_prop : prop -> ctx -> ctx                 (* free variables of a prop *)

    val zip : ctx -> arith list -> subst               (* x1,...,xn\e1,...,en *)
                                                       (* may raise ListPair.UnequalLengths *)
    val apply : subst -> arith -> arith                (* [sigma]e *)
    val apply_list : subst -> arith list -> arith list (* [sigma](e1,...,en) *)
    val apply_prop : subst -> prop -> prop             (* [sigma]phi *)
    val fresh_var : subst -> varname -> varname        (* variable not free in codom(sigma) *)

    val create_idx : ctx -> arith list                 (* {x1}...{xn} *)

    val evaluate : arith -> int                        (* may raise NotClosed *)
    val evaluate_prop : prop -> bool                   (* may raise NotClosed *)

    val plus : arith * arith -> arith                  (* preserve integer values *)
    val minus : arith * arith -> arith                 (* preserve integer values *)

    (* Next two eliminate some antecedents x = e and x > n *)
    val elim_eq : prop -> prop -> prop * prop          (* elim_eq con phi = (con', phi') where con |= phi iff con' |= phi' *)
    val elim_ge : prop -> prop -> prop * prop          (* elim_ge con phi = (con', phi') where con |= phi iff con' |= phi' *)

    (* Presburger arithmetic *)
    exception NonLinear

    type nnf = prop                   (* propositions in negation normal form *)
    val nnf : prop -> nnf             (* may raise NonLinear *)
    val elim : varname -> prop -> nnf (* elim x phi = psi where (exists x. phi) <=> psi *)
    val elim_nnf : varname -> nnf -> nnf
    val elim_vars : varname list -> nnf -> nnf
                                      (* elim xs phi = psi where (exists xs. phi) <=> psi *)

    val valid : varname list -> prop -> prop -> bool (* may raise NonLinear *)
                                      (* valid xs phi psi iff forall xs. phi |= psi *)

    (* quantification, eagerly eliminated by decision procedure *)
    val exists : varname -> nnf -> nnf  (* exists x phi = psi where (exists x.phi) <=> psi *)
    val forall : varname -> nnf -> nnf  (* forall x phi = psi where (forall x.phi) <=> psi *)

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

(* check if an arithmetic expression or proposition is closed under ctx *)
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
  | closed_prop ctx (Le(e1,e2)) = closed ctx e1 andalso closed ctx e2
  | closed_prop ctx (Ge(e1,e2)) = closed ctx e1 andalso closed ctx e2
  | closed_prop ctx (Divides(n,e)) = closed ctx e
  | closed_prop ctx (True) = true
  | closed_prop ctx (False) = false
  | closed_prop ctx (Or(phi,psi)) = closed_prop ctx phi andalso closed_prop ctx psi
  | closed_prop ctx (And(phi,psi)) = closed_prop ctx phi andalso closed_prop ctx psi
  | closed_prop ctx (Implies(phi,psi)) = closed_prop ctx phi andalso closed_prop ctx psi
  | closed_prop ctx (Not(phi)) = closed_prop ctx phi

(* compute the free variables of expressions and propositions *)
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

fun free_in v (Int(n)) = false
  | free_in v (Add(s,t)) = free_in v s orelse free_in v t
  | free_in v (Sub(s,t)) = free_in v s orelse free_in v t
  | free_in v (Mult(s,t)) = free_in v s orelse free_in v t
  | free_in v (Var(v')) = v = v'

fun free_in_subst v nil = false
  | free_in_subst v ((v',e)::sigma) = free_in v e orelse free_in_subst v sigma

(* zip [x1,...,xn] [e1,...,en] = (e1/x1,...,en/xn) *)
(* assumes length ctx = length es; raises ListPair.UnequalLengths otherwise *)
fun zip ctx es = ListPair.zipEq (ctx, es)

(* find sg v' = [sg]v' *)
(* assumed sg : ctx and ctx |- v' nat *)
fun find ((v,e)::sg) v' = if (v = v') then e else find sg v'
  | find nil v' = Var(v')

(* apply sg e = [sg]e *)
(* assumes sg : ctx and ctx |- e : int *)
fun apply sg (e as Int(k)) = e
  | apply sg (Add(e1,e2)) = Add(apply sg e1, apply sg e2)
  | apply sg (Sub(e1,e2)) = Sub(apply sg e1, apply sg e2)
  | apply sg (Mult(e1,e2)) = Mult(apply sg e1, apply sg e2)
  | apply sg (Var(v)) = find sg v

exception NotClosed

fun apply_list sg es = List.map (fn e => apply sg e) es

(* apply_prop sg phi = [sg]phi *)
(* assumes sg : ctx and ctx |- phi prop *)
fun apply_prop sg (Eq(e1,e2)) = Eq(apply sg e1, apply sg e2)
  | apply_prop sg (Lt(e1,e2)) = Lt(apply sg e1, apply sg e2)
  | apply_prop sg (Gt(e1,e2)) = Gt(apply sg e1, apply sg e2)
  | apply_prop sg (Le(e1,e2)) = Le(apply sg e1, apply sg e2)
  | apply_prop sg (Ge(e1,e2)) = Ge(apply sg e1, apply sg e2)
  | apply_prop sg (Divides(n,e)) = Divides(n, apply sg e)
  | apply_prop sg (True) = True
  | apply_prop sg (False) = False
  | apply_prop sg (Or(phi,psi)) = Or(apply_prop sg phi, apply_prop sg psi)
  | apply_prop sg (And(phi,psi)) = And(apply_prop sg phi, apply_prop sg psi)
  | apply_prop sg (Implies(phi,psi)) = Implies(apply_prop sg phi, apply_prop sg psi)
  | apply_prop sg (Not(phi)) = Not(apply_prop sg phi)

(* Fresh name generation *)

fun next_name v = v ^ "^"

fun fresh_var sigma v =
    if free_in_subst v sigma
    then fresh_var sigma (next_name v)
    else v

fun create_idx vs = List.map (fn v => Var(v)) vs

(* evaluate e = k if e |->* k *)
(* assumes . |- e int, raises NotClosed otherwise *)
fun evaluate (Int(k)) = k
  | evaluate (Add(e1,e2)) = (evaluate e1) + (evaluate e2)
  | evaluate (Sub(e1,e2)) = (evaluate e1) - (evaluate e2)
  | evaluate (Mult(e1,e2)) = (evaluate e1) * (evaluate e2)
  | evaluate (Var(v)) = raise NotClosed

(* evaluate phi = b if phi |->* b *)
(* assumes . |- phi prop, raises NotClosed otherwise *)
fun evaluate_prop (Eq(e1,e2)) = (evaluate e1 = evaluate e2)
  | evaluate_prop (Lt(e1,e2)) = (evaluate e1 < evaluate e2)
  | evaluate_prop (Gt(e1,e2)) = (evaluate e1 > evaluate e2)
  | evaluate_prop (Le(e1,e2)) = (evaluate e1 <= evaluate e2)
  | evaluate_prop (Ge(e1,e2)) = (evaluate e1 >= evaluate e2)
  | evaluate_prop (Divides(n,e)) = ((evaluate e) mod n = 0)
  | evaluate_prop (True) = true
  | evaluate_prop (False) = false
  | evaluate_prop (Or(phi,psi)) = evaluate_prop phi orelse evaluate_prop psi
  | evaluate_prop (And(phi,psi)) = evaluate_prop phi andalso evaluate_prop psi
  | evaluate_prop (Implies(phi,psi)) = (not (evaluate_prop phi)) orelse evaluate_prop psi
  | evaluate_prop (Not(phi)) = not (evaluate_prop phi)

fun plus (e1, e2) =
    Int(evaluate(Add(e1,e2)))
    handle NotClosed => Add(e1,e2)

fun minus (e1, e2) =
    Int(evaluate(Sub(e1,e2)))
    handle NotClosed => Sub(e1,e2)

(************)
(* Printing *)
(************)

(* 
 * Simple printing, mostly for internal purposes.
 * See pprint.sml for (user-facing) operator precedence printing
 *)

structure Print =
struct

    fun pp_arith (Int(n)) = if n >= 0 then Int.toString n else "-" ^ Int.toString (~n)
      | pp_arith (Add(s,t)) = pp_arith_paren s ^ "+" ^ pp_arith_paren t
      | pp_arith (Sub(s,t)) = pp_arith_paren s ^ "-" ^ pp_arith_paren t
      | pp_arith (Mult(s,t)) = pp_arith_paren s ^ "*" ^ pp_arith_paren t
      | pp_arith (Var(x)) = x
    and pp_arith_paren (s as Int(n)) = pp_arith s
      | pp_arith_paren (s as Var(x)) = pp_arith s
      | pp_arith_paren s = "(" ^ pp_arith s ^ ")"

    fun pp_prop (Eq(s,t)) = pp_arith s ^ " = " ^ pp_arith t
      | pp_prop (Lt(s,t)) = pp_arith s ^ " < " ^ pp_arith t
      | pp_prop (Gt(s,t)) = pp_arith s ^ " > " ^ pp_arith t
      | pp_prop (Le(s,t)) = pp_arith s ^ " <= " ^ pp_arith t
      | pp_prop (Ge(s,t)) = pp_arith s ^ " >= " ^ pp_arith t
      | pp_prop (Divides(n,t)) = Int.toString n ^ "|" ^ pp_arith t
      | pp_prop (True) = "true"
      | pp_prop (False) = "false"
      | pp_prop (Or(phi,psi)) = "(" ^ pp_prop phi ^ " \\/ " ^ pp_prop psi ^ ")"
      | pp_prop (And(phi,psi)) = "(" ^ pp_prop phi ^ " /\\ " ^ pp_prop psi ^ ")"
      | pp_prop (Implies(phi,psi)) = "(" ^ pp_prop phi ^ " => " ^ pp_prop psi ^ ")"
      | pp_prop (Not(phi)) = "~" ^ pp_prop phi

end (* structure Print *)

(**********************)
(* Decision procedure *)
(**********************)

(*
 * This implementation uses Cooper's algorithm
 *
 * Current restrictions:
 *
 * Quantifiers must range over natural numbers (F-infinity is not constructed)
 * As typical, eliminated only existential quantifiers
 * Universals can be obtained by |= forall x. phi iff |= ~exists x. ~phi
 *)


type nnf = prop
exception NonLinear

(****************)
(* Normal Terms *)
(****************)
(*
 * variable x
 * constant k (including 0)
 * product  p ::= k*x
 * linear   s ::= k1*x1 + ... + kn*xn + k, xi all distinct
 *)

(* is_prod (k*x) where integer k may be 0 *)
fun is_prod (Mult(Int(k),Var(x))) = true
  | is_prod _ = false

(* is_linear (k1*x1 + ... + kn*xn + k); do not check distinctness *)
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
  | mult_prod (Mult(Int(k),Var(x))) (Int(k')) = Add(Mult(Int(k*k'),Var(x)),Int(0))

(* mult s t = lin(s * t), raises NonLinear if result is not linear *)
fun mult (Add(p,s)) t = add (mult_prod p t) (mult s t)
  | mult (Int(k)) t = mult_const k t

(* sub s t = lin(s - t) *)
fun sub s t = add s (mult_const ~1 t)

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

(************************)
(* Isolating a Variable *)
(************************)

(* iso_term x s = (k*x, t) where s = k*x + t and x does not occur in t
 * k will be 0 if x does not occur in s
 * assume s is linear, ensure t is linear
 *)
fun iso_term x (s as Int(k)) = (Mult(Int(0),Var(x)), s)
  | iso_term x (Add(p' as Mult(Int(k'),Var(x')), s)) =
    if x = x' then (p', s)
    else let val (kx, t) = iso_term x s
         in (kx, Add(p', t)) end

(***********************)
(* Normal Propositions *)
(***********************)

(*
 * (Strict) negation normal forms (NNF), where
 * terms s and t are in linear normal form and n > 0
 *
 * M,N ::= s < t | (n|s) | ~(n|s) | true | false | M \/ N | M /\ N 
 *)

exception NotNNF

(* testing nnf *)
fun is_nnf (Lt(s,t)) = is_linear s andalso is_linear t
  | is_nnf (Divides(n,t)) = n > 0 andalso is_linear t
  | is_nnf (Not(Divides(n,t))) = n > 0 andalso is_linear t
  | is_nnf (True) = true
  | is_nnf (False) = true
  | is_nnf (Or(phi,psi)) = is_nnf phi andalso is_nnf psi
  | is_nnf (And(phi,psi)) = is_nnf phi andalso is_nnf psi
  | is_nnf _ = false

(* transforming into strict nnf *)
(* nnf phi = M, may raise NotLinear *)
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
  | nnf (Or(phi,psi)) = Or(nnf phi, nnf psi)
  | nnf (And(phi,psi)) = And(nnf phi, nnf psi)
  | nnf (Implies(phi,psi)) = Or(nnf_not phi, nnf psi)
  | nnf (Not(phi)) = nnf_not phi
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
  | nnf_not (Or(phi,psi)) = And(nnf_not phi, nnf_not psi)
  | nnf_not (And(phi,psi)) = Or(nnf_not phi, nnf_not psi)
  | nnf_not (Implies(phi,psi)) = And(nnf phi, nnf_not psi) (* ~(phi => psi) <=> phi /\ ~psi *)
  | nnf_not (Not(phi)) = nnf phi

(*
 * x is isolated in phi if phi is in strict nnf
 * and all atomic propositions have the form
 * k*x + s < 0 or n|k*x or ~(n|(k*x + s))
 * for this particular x (where k may be 0).
 * We write phi[x] (or phi_x) if x is isolated in phi
 *)

(* is_iso x phi = true if is isolated in phi, written as phi[x] *)
fun is_iso x (Lt(Add(Mult(Int(k),Var(x')),s),Int(0))) =
    x = x' andalso is_linear s
  | is_iso x (Divides(n,Add(Mult(Int(k),Var(x')),s))) =
    n > 0 andalso x = x' andalso is_linear s (* k arbitrary, including 0 *)
  | is_iso x (Not(Divides(n,s))) = is_iso x (Divides(n,s))
  | is_iso x (True) = true
  | is_iso x (False) = true
  | is_iso x (Or(phi,psi)) = is_iso x phi andalso is_iso x psi
  | is_iso x (And(phi,psi)) = is_iso x phi andalso is_iso x psi
  | is_iso x _ = false

(* iso x phi = phi'[x] where phi and phi'[x] are in strict nnf,
   and phi <=> phi'[x]
 *)
fun iso x (Lt(s,t)) = Lt(Add(iso_term x (sub s t)), Int(0))
  | iso x (Divides(n,t)) = Divides(n, Add(iso_term x t))
  | iso x (Not(Divides(n,t))) = Not(Divides(n, Add(iso_term x t)))
  | iso x True = True
  | iso x False = False
  | iso x (Or(phi,psi)) = Or(iso x phi, iso x psi)
  | iso x (And(phi,psi)) = And(iso x phi, iso x psi)

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
    else (* k < 0 *) lcm_nat (~k) l

(* lcm x phi[x] l = l', the least common multiple of l and
 * the absolute values of coefficients of x in phi[x]
 *)
fun lcm x (Lt(Add(Mult(Int(k),_),t),_)) l = lcm_coeff k l
  | lcm x (Divides(n,Add(Mult(Int(k),_),t))) l = lcm_coeff k l
  | lcm x (Not(phi)) l = lcm x phi l
  | lcm x True l = l
  | lcm x False l = l
  | lcm x (Or(phi,psi)) l = lcm x phi (lcm x psi l)
  | lcm x (And(phi,psi)) l = lcm x phi (lcm x psi l)

(* lcm_div x phi[x] l = l', the least common multiple of l and
 * the divisors of k*x in phi[x]
 *)
fun lcm_div x (Lt(kx,z)) l = l
  | lcm_div x (Divides(n,Add(Mult(Int(k),_),t))) l =
    if k = 0 then l else lcm_coeff n l
  | lcm_div x True l = l
  | lcm_div x False l = l
  | lcm_div x (Or(phi,psi)) l = lcm_div x phi (lcm_div x psi l)
  | lcm_div x (And(phi,psi)) l = lcm_div x phi (lcm_div x psi l)
  | lcm_div x (Not(phi)) l = lcm_div x phi l

(* unitize delta x phi[x] = phi'[x] with (exists x.phi[x]) <=> (exists x.phi'[x])
 * given delta = lcm x phi[x] 1
 * where all coefficients of x in phi'[x] are -1, 0, or 1
 *)
fun unitize delta x (phi as Lt(Add(Mult(Int(k),_),t), z)) = (* z = 0 *)
    if k = 0 then phi
    else if k > 0 then Lt(Add(Mult(Int(1),Var(x)), mult_const (delta div k) t), z)
    else (* k < 0 *) Lt(Add(Mult(Int(0-1),Var(x)), mult_const (delta div (~k)) t), z)
  | unitize delta x (phi as Divides(n, Add(Mult(Int(k),_),t))) =
    if k = 0 then phi
    else if k > 0 then Divides((delta div k)*n, Add(Mult(Int(1), Var(x)), mult_const (delta div k) t))
    else (* k < 0 *)
        Divides((delta div (0-k))*n, Add(Mult(Int(1), Var(x)), mult_const (delta div k) t)) (* not div (0-k)! *)
  | unitize delta x (Not(phi)) = Not (unitize delta x phi)
  | unitize delta x (True) = True
  | unitize delta x (False) = False
  | unitize delta x (Or(phi,psi)) = Or (unitize delta x phi, unitize delta x psi)
  | unitize delta x (And(phi,psi)) = And (unitize delta x phi, unitize delta x psi)

(* collect lower bounds -x + t < 0 *)
(* lbs x phi[x] = {t | -x + t < 0 in phi[x]} *)
fun lbs x (Lt(Add(Mult(Int(k),_),t),_)) acc =
    if k = 0 then acc
    else if k = 1 then acc
    else (* k = -1 *) t::acc
  | lbs x (Divides _) acc = acc
  | lbs x (Not(Divides _)) acc = acc
  | lbs x (True) acc = acc
  | lbs x (False) acc = acc
  | lbs x (Or(phi,psi)) acc = lbs x phi (lbs x psi acc)
  | lbs x (And(phi,psi)) acc = lbs x phi (lbs x psi acc)

(* subst_prop x t phi[x] = psi, phi[x] must be unitary, psi is strict nnf *)
fun subst_prop x t (Lt(Add(Mult(Int(k),Var(x')),s), z)) = (* x = x', z = 0 *)
    if k = 0 then Lt(s,z)
    else Lt(add (mult_const k t) s, z) (* k = 1 or k = -1 *)
  | subst_prop x t (Divides(n,Add(Mult(Int(k),Var(x')),s))) = (* x = x' *)
    if k = 0 then Divides(n, s)
    else Divides(n, add (mult_const k t) s) (* k = 1 or k = -1 *)
  | subst_prop x t (Not(phi)) = Not(subst_prop x t phi) (* phi = (n | s) *)
  | subst_prop x t (True) = True
  | subst_prop x t (False) = False
  | subst_prop x t (Or(phi,psi)) = Or(subst_prop x t phi, subst_prop x t psi)
  | subst_prop x t (And(phi,psi)) = And(subst_prop x t phi, subst_prop x t psi)

(* disjoin j bset x phi[x] psi = psi' where psi' <=> \/(0 < i <= j, b in bset)(phi[b+j]) *)
(* phi[x] is unitary in x, psi is strict nnf, psi' will be strict nnf *)
fun disjoin 0 bset x phi_x psi = psi
  | disjoin j bset x phi_x psi =
      disjoin (j-1) bset x phi_x (disjoin' j bset x phi_x psi)
and disjoin' j nil x phi_x psi = psi
  | disjoin' j (b::bset) x phi_x psi =
      disjoin' j bset x phi_x (Or(psi, subst_prop x (add_const (Int(j)) b) phi_x))

(******************)
(* Simplification *)
(******************)

fun or_ True psi = True
  | or_ False psi = psi
  | or_ phi True = True
  | or_ phi False = phi
  | or_ phi psi = Or(phi,psi)

fun and_ True psi = psi
  | and_ False psi = False
  | and_ phi True = phi
  | and_ phi False = False
  | and_ phi psi = And(phi,psi)

fun not_ True = False
  | not_ False = True
  | not_ phi = Not(phi)

fun simplify (Lt(Int(k),Int(k'))) = if k < k' then True else False
  | simplify (Lt(s,t)) = Lt(s,t)
  | simplify (Divides(n,Int(k))) = if k mod n = 0 then True else False
  | simplify (Divides(n,t)) = Divides(n,t)
  | simplify (True) = True
  | simplify (False) = False
  | simplify (Or(phi,psi)) = or_ (simplify phi) (simplify psi)
  | simplify (And(phi,psi)) = and_ (simplify phi) (simplify psi)
  | simplify (Not(phi)) = not_ (simplify phi)
                        
(* Eliminating antecedents in con before checking con |= phi
 *
 * At the moment, we optimize only for
 *   con ::= phi | con /\ psi  where phi is not a conjunction
 * and psi is an atomic assumption
 *)

(*
 * For equalities, we reason with sb : subst -> prop where
 *
 * sb [] = True
 * sb ([x,e] :: sigma) = (x = e /\ sb sigma)
 *
 * This should probably be extended at least to the case where psi
 * is broken down if it is a conjunction.
 *)
fun rev (And(con,psi)) con' = rev con (And(con',psi))
  | rev (True) con' = con'

(* eq_subst phi = (phi', sigma) where phi = phi' /\ sb(sigma) *)
fun eq_subst (phi as Eq(Var(x),e)) =
    if free_in x e then (phi, []) else (True, [(x,e)])
  | eq_subst (Eq(e, Var(x))) = eq_subst (Eq(Var(x), e))
  | eq_subst phi = (phi, [])

fun elim_eq_var (And(con,psi)) con' phi =
    ( case eq_subst psi
       of (psi', []) => elim_eq_var con (And(con',psi')) phi
        | (psi', sigma) => elim_eq_var (apply_prop sigma con) (And(apply_prop sigma con', psi')) (apply_prop sigma phi)
        (* could optimize away psi' = True *)
    )
  | elim_eq_var psi con' phi = (rev con' psi, phi)

(* Eliminating assumptions x >= k by substituting
 * (x' + k)/x  (except we actually don't rename x)
 * exploiting x' + k >= k for x' >= 0
 *
 * This is currently used in a heuristic for deciding
 * nonlinear inequalities.
 *)

(* ge_subst phi = (phi', sigma) where phi = phi' /\ sb(sigma) *)
(* We do not create fresh names, however *)
(* This could be applied more generally for x >= e where x not in e *)
fun ge_subst (Gt(Var(x),Int(n))) = ge_subst (Ge(Var(x),Int(n+1)))
  | ge_subst (Ge(Var(x),Int(n))) = if n > 0 then (True, [(x,Add(Var(x),Int(n)))]) else (True, [])
  | ge_subst (Le(Int(n),Var(x))) = ge_subst (Ge(Var(x),Int(n)))
  | ge_subst (Lt(Int(n),Var(x))) = ge_subst (Ge(Var(x),Int(n+1)))
  | ge_subst phi = (phi, [])

fun elim_ge_var_const (And(con,psi)) con' phi =
    ( case ge_subst psi
       of (psi', []) => elim_ge_var_const con (And(con',psi')) phi
        | (psi', sigma) => elim_ge_var_const (apply_prop sigma con) (And(apply_prop sigma con', psi')) (apply_prop sigma phi)
        (* could optimize the case where psi' = True *)
    )
  | elim_ge_var_const psi con' phi = (rev con' psi, phi)

fun elim_ge con phi = elim_ge_var_const con True phi
fun elim_eq con phi = elim_eq_var con True phi

(*****************)
(* Preprocessing *)
(*****************)

(*
 * We eliminated assumptions x = e (or e = x) where x not in e
 * by substitution.  This is an important optimization for efficiency
 * in the case of linear constraints, and decidability for
 * nonlinear constraints.
 *
 * This must happen before conversion to strict nnf, since this
 * eliminates all equalities.
 *)
fun preprocess xs con phi = elim_eq con phi

(**************************)
(* Quantifier Elimination *)
(**************************)

(*
 * elim x phi = psi, where (exists x. phi) <=> psi and x does not occur in psi
 * assume phi is in strict nnf; ensure psi is in strict nnf
 * Relativize implicit quantifiers to express we are solving over nat, not int.
 *)
fun elim_nnf x phi =
    let 
        val () = if is_nnf phi then () else raise NotNNF (* redundant assertion *)
        val phi = And(Lt(Int(0), Add(Mult(Int(1),Var(x)),Int(1))),phi) (* x >= 0  <=>  0 < x+1 *)
        val phi_x = iso x phi
        val delta = lcm x phi_x 1
        val phi_x = And(unitize delta x phi_x, Divides(delta, Add(Mult(Int(1),Var(x)),Int(0))))
        val delta_div = lcm_div x phi_x 1
        val bset = lbs x phi_x nil
        (* for natural numbers, do not calculate F-infinity *)
        (* now calculate or(j=1..delta_div, b in bset)(phi'x[b+j]) *)
        val psi = disjoin delta_div bset x phi_x False
        val psi = simplify psi
    in
        psi
    end

fun elim x phi = elim_nnf x (nnf phi)

(* ctx ; con |= phi
 * <=> forall ctx. con => phi
 * <=> not exists ctx. not (con => phi)
 * <=> not exists ctx. con /\ not phi
 *)
(* elim_vars xs phi = psi, assuming phi is in strict normal form *)
(* psi = True | False if xs contains all variables in phi *)
fun elim_vars nil phi = phi
  | elim_vars (x::xs) phi = elim_vars xs (elim_nnf x phi)

fun valid xs con phi =
    let val (con',phi') = preprocess xs con phi
        val phi = And(Not(phi'), con')
        val phi = nnf phi           (* convert to strict normal form *)
        val phi = simplify phi      (* only useful if xs = [] *)
        val psi = elim_vars xs phi
    in case psi
        of True => false
         | False => true
         | psi => ( print ("constraint " ^ List.foldl (fn (x,s) => x ^ " " ^ s) "" xs ^ " |= "
                           ^ Print.pp_prop psi ^ " not simplified to True or False\n")
                  ; print ("this indicates an internal error in the type-checker\n")
                  ; raise Match )
    end

fun neg phi = nnf (Not(phi))

fun exists x phi = elim_nnf x phi
fun forall x phi = neg (elim_nnf x (neg phi))

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
val True = elim "x" (Lt(Mult(Int(~1),Var("x")), Int(0)))
val True = elim_vars ["x","y"] (nnf (Lt(Var("x"), Var("y"))))
(* from Hansen 2010 *)
val True = elim "x" (And(Or(Lt(Add(Mult(Int(3),Var("x")),Int(1)),Int(10)),
                            Gt(Sub(Mult(Int(7),Var("x")),Int(6)),Int(7))),
                         Divides(2,Var("x"))))

end

end (* struct ArithTest *)
*)
