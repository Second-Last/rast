(* Type Checking *)
(* Use the syntax-directed rules to check the types and
 * raises ErrorMsg.Error if an error is discovered
 *)

signature TYPE_CHECK =
sig
    (* validity of types *)
    val closed : Arith.ctx -> Arith.arith -> Ast.ext -> unit     (* may raise ErrorMsg.Error *)
    val closed_prop : Arith.ctx -> Arith.prop -> Ast.ext -> unit (* may raise ErrorMsg.Error *)
    val closed_tp : Arith.ctx -> Ast.tp -> Ast.ext -> unit       (* may raise ErrorMsg.Error *)
    val closed_exp : Arith.ctx -> Ast.exp -> Ast.ext -> unit     (* may raise ErrorMsg.Error *)

    datatype polarity = Pos | Neg | Zero
    val valid : Ast.env -> Arith.ctx -> Arith.prop
                -> polarity -> Ast.tp -> Ast.ext -> unit (* may raise ErrorMsg.Error *)

    (* properties of types *)
    val contractive : Ast.env -> Ast.tp -> bool
    val eventually_box : Ast.env -> Ast.tp -> bool
    val eventually_dia : Ast.env -> Ast.tp -> bool

    (* operations on types *)
    val decrementL : Ast.env -> Arith.ctx -> Arith.prop
                     -> Ast.tp -> Arith.arith -> Ast.ext -> Ast.tp (* may raise ErrorMsg.Error *)
    val decrementR : Ast.env -> Arith.ctx -> Arith.prop
                     -> Ast.tp -> Arith.arith -> Ast.ext -> Ast.tp (* may raise ErrorMsg.Error *)
    val strip_next0 : Ast.env -> Arith.ctx -> Arith.prop -> Ast.tp -> Ast.tp
    val eq_tp : Ast.env -> Arith.ctx -> Arith.prop -> Ast.tp -> Ast.tp -> bool

    (* operations on approximately typed expressions (see arecon.sml) *)
    val syn_cut : Ast.env -> Ast.exp * Ast.exp ->  Ast.ext -> Ast.exp
    val syn_call : Ast.env -> Ast.exp -> Ast.ext -> Ast.tp * Ast.pot * Ast.exp * Ast.tp
    val synR : Ast.env -> Ast.expname * Arith.arith list -> Ast.tp
    val synL : Ast.env -> Ast.expname * Arith.arith list -> Ast.tp
    val synLR : Ast.env -> Ast.expname * Arith.arith list -> Ast.tp * Ast.pot * Ast.tp
    val syn_alt : Ast.env -> Ast.choices -> Ast.label -> Ast.tp

    (* check_exp trace env ctx con A pot P C ext = ()
     * checks that A |- P : C with potential pot
     * trace = true means print some tracinng information
     * ctx = context of free index variables
     * con = constraints
     * ext is approximation of source extent for P, if available
     * may raise ErrorMsg.Error *)
    val check_exp : bool -> Ast.env -> Arith.ctx -> Arith.prop
                    -> Ast.tp -> Ast.pot -> Ast.exp -> Ast.tp -> Ast.ext -> unit

end (* signature TYPE_CHECK *)

structure TypeCheck :> TYPE_CHECK =
struct

structure R = Arith
structure A = Ast
structure PP = PPrint
(* structure N = Normalize *)
structure E = TpError
structure C = Constraints
val ERROR = ErrorMsg.ERROR

(*********************)
(* Validity of types *)
(*********************)

fun closed ctx p ext =
    if R.closed ctx p then ()
    else ERROR ext ("arithmetic expression " ^ PP.pp_arith p ^ " not closed")

fun closed_prop ctx phi ext =
    if R.closed_prop ctx phi then ()
    else ERROR ext ("proposition " ^ PP.pp_prop phi ^ " not closed")

fun closed_tp ctx (A.Plus(choice)) ext = closed_choice ctx choice ext
  | closed_tp ctx (A.With(choice)) ext = closed_choice ctx choice ext
  | closed_tp ctx (A.One) ext = ()
  | closed_tp ctx (A.Exists(phi,A)) ext = ( closed_prop ctx phi ext ; closed_tp ctx A ext )
  | closed_tp ctx (A.Forall(phi,A)) ext = ( closed_prop ctx phi ext ; closed_tp ctx A ext )
  | closed_tp ctx (A.PayPot(p,A)) ext = ( closed ctx p ext ; closed_tp ctx A ext )
  | closed_tp ctx (A.GetPot(p,A)) ext = ( closed ctx p ext ; closed_tp ctx A ext )
  | closed_tp ctx (A.Next(t,A)) ext = ( closed ctx t ext ; closed_tp ctx A ext )
  | closed_tp ctx (A.Dia(A)) ext = closed_tp ctx A ext
  | closed_tp ctx (A.Box(A)) ext = closed_tp ctx A ext
  | closed_tp ctx (A.TpName(a,es)) ext = List.app (fn e => closed ctx e ext) es
  (* A.Dot should be impossible here *)
and closed_choice ctx nil ext = ()
  | closed_choice ctx ((l,Al)::choices) ext =
    ( closed_tp ctx Al ext ; closed_choice ctx choices ext )

fun closed_exp ctx (A.Id) ext = ()
  | closed_exp ctx (A.Cut(P,lpot,B,Q)) ext =
    ( closed_exp ctx P ext
    ; closed ctx lpot ext
    ; closed_tp ctx B ext
    ; closed_exp ctx Q ext )
  | closed_exp ctx (A.Spawn(P,Q)) ext =
    ( closed_exp ctx P ext
    ; closed_exp ctx Q ext )
  | closed_exp ctx (A.ExpName(f,es)) ext = List.app (fn e => closed ctx e ext) es

  | closed_exp ctx (A.LabR(k,P)) ext = closed_exp ctx P ext
  | closed_exp ctx (A.CaseL(branches)) ext = closed_branches ctx branches ext

  | closed_exp ctx (A.CaseR(branches)) ext = closed_branches ctx branches ext
  | closed_exp ctx (A.LabL(k,Q)) ext = closed_exp ctx Q ext

  | closed_exp ctx (A.CloseR) ext = ()
  | closed_exp ctx (A.WaitL(Q)) ext = closed_exp ctx Q ext
                                      
  | closed_exp ctx (A.AssertR(phi,P)) ext = (closed_prop ctx phi ext ; closed_exp ctx P ext )
  | closed_exp ctx (A.AssumeL(phi,P)) ext = (closed_prop ctx phi ext ; closed_exp ctx P ext )
  | closed_exp ctx (A.AssumeR(phi,P)) ext = (closed_prop ctx phi ext ; closed_exp ctx P ext )
  | closed_exp ctx (A.AssertL(phi,P)) ext = (closed_prop ctx phi ext ; closed_exp ctx P ext )
  | closed_exp ctx (A.Imposs) ext = ()

  | closed_exp ctx (A.Work(p,P)) ext = ( closed ctx p ext ; closed_exp ctx P ext )
  | closed_exp ctx (A.PayR(p,P)) ext = ( closed ctx p ext ; closed_exp ctx P ext )
  | closed_exp ctx (A.GetL(p,P)) ext = ( closed ctx p ext ; closed_exp ctx P ext )
  | closed_exp ctx (A.GetR(p,P)) ext = ( closed ctx p ext ; closed_exp ctx P ext )
  | closed_exp ctx (A.PayL(p,P)) ext = ( closed ctx p ext ; closed_exp ctx P ext )

  | closed_exp ctx (A.Delay(t,P)) ext = (closed ctx t ext ; closed_exp ctx P ext )
  | closed_exp ctx (A.WhenR(P)) ext = closed_exp ctx P ext
  | closed_exp ctx (A.NowL(P)) ext = closed_exp ctx P ext
  | closed_exp ctx (A.WhenL(P)) ext = closed_exp ctx P ext
  | closed_exp ctx (A.NowR(P)) ext = closed_exp ctx P ext

  | closed_exp ctx (A.Marked(marked_P)) ext = closed_exp ctx (Mark.data marked_P) (Mark.ext marked_P)
and closed_branches ctx nil ext = ()
  | closed_branches ctx ((l,ext',P)::branches) ext =
    ( closed_exp ctx P ext'
    ; closed_branches ctx branches ext )

(* Occurrences of |> and <| are restricted to
 * positive and negative positions in a type, respectively
 *)
datatype polarity = Pos | Neg | Zero

(* valid env ctx con polarity A ext = ()
 * raises ErrorMsg.Error if not a valid type
 * env must be the full environment which checking any
 * type to allow mutually recursive definitions
 * Type A must be an actual type (not '.' = A.Dot)
 *)
fun valid env ctx con _ (A.Plus(choice)) ext = valid_choice env ctx con Pos choice ext
  | valid env ctx con _ (A.With(choice)) ext = valid_choice env ctx con Neg choice ext
  | valid env ctx con _ A.One ext = ()

  | valid env ctx con Pos (A.Exists(phi, A)) ext = valid env ctx (R.And(con,phi)) Pos A ext
  | valid env ctx con _ (A.Exists(phi, A)) ext = valid env ctx (R.And(con,phi)) Zero A ext
  | valid env ctx con Neg (A.Forall(phi, A)) ext = valid env ctx (R.And(con,phi)) Neg A ext
  | valid env ctx con _ (A.Forall(phi, A)) ext = valid env ctx (R.And(con,phi)) Zero A ext

  | valid env ctx con Pos (A.PayPot(e,A)) ext =
    if not (C.entails ctx con (R.Ge(e,R.Int(0)))) (* allowing 0, for uniformity *)
    then ERROR ext ("potential " ^ PP.pp_arith e ^ " not positive under constraints " ^ PP.pp_prop con)
    else valid env ctx con Pos A ext
  | valid env ctx con Neg (A.PayPot(_,A)) ext = ERROR ext ("|> appears in a negative context")
  | valid env ctx con Zero (A.PayPot(_,A)) ext = ERROR ext ("|> appears in a neutral context")

  | valid env ctx con Pos (A.GetPot(_,A)) ext = ERROR ext ("<| appears in a positive context")
  | valid env ctx con Zero (A.GetPot(_,A)) ext = ERROR ext ("<| appears in a neutral context")
  | valid env ctx con Neg (A.GetPot(e,A)) ext =
    if not (C.entails ctx con (R.Ge(e,R.Int(0)))) (* allowing 0, for uniformity *)
    then ERROR ext ("potential " ^ PP.pp_arith e ^ " not positive under constraints " ^ PP.pp_prop con)
    else valid env ctx con Neg A ext

    (* propagate polarity for temporal types -fp Wed Feb 13 07:27:24 2019 *)
  | valid env ctx con polarity (A.Next(t,A)) ext =
    if not (C.entails ctx con (R.Ge(t,R.Int(0))))
    then ERROR ext ("time " ^ PP.pp_arith t ^ " not positive under constraints " ^ PP.pp_prop con)
    else valid env ctx con polarity A ext
  | valid env ctx con polarity (A.Dia(A)) ext = valid env ctx con polarity A ext
  | valid env ctx con polarity (A.Box(A)) ext = valid env ctx con polarity A ext

  | valid env ctx con _ (A.TpName(a,es)) ext =
    (* allow forward references since 'env' is the full environment *)
    (case A.lookup_tp env a
      of NONE => ERROR ext ("type name " ^ a ^ " undefined")
       | SOME(vs,con',_) =>
         if not (List.length vs = List.length es)
         then ERROR ext ("type " ^ a ^ " defined with " ^ Int.toString (List.length vs)
                         ^ " indices, but used with " ^ Int.toString (List.length es))
         else case List.find (fn e => not (C.entails ctx con (R.Ge(e, R.Int(0))))) es
               of SOME(e) => ERROR ext ("type index cannot shown to be positive\n"
                                        ^ C.pp_jfail con (R.Ge(e, R.Int(0))))
                | NONE => if not (C.entails ctx con (R.apply_prop (R.zip vs es) con'))
                          then ERROR ext ("type constraint " ^ PP.pp_prop (R.apply_prop (R.zip vs es) con')
                                          ^ " not satisfied")
                          else ())
  (* A.Dot impossible *)
and valid_choice env ctx con pol nil ext = ()
  | valid_choice env ctx con pol ((l,Al)::choices) ext =
    ( valid env ctx con pol Al ext
    ; valid_choice env ctx con pol choices ext )

(***********************)
(* Properties of types *)
(***********************)

(* Next(t,a) is not constructive because for t = 0
 * this can lead to an infinite loop in type-checking
 *)
fun contractive env (A as A.Next(_,A')) = contractive env A'
  | contractive env (A as A.TpName(a,l)) = false
  | contractive env (A as A.Dot) = false
  | contractive env A = true

fun eventually_box env (A.Box(A)) = true
  | eventually_box env (A.Next(_,A)) = eventually_box env A
  | eventually_box env (A.TpName(a,es)) = eventually_box env (A.expd_tp env (a,es))
  | eventually_box env (A.Dot) = true (* pseudo-type *)
  | eventually_box _ _ = false

fun eventually_dia env (A.Dia(A)) = true
  | eventually_dia env (A.Next(_,A)) = eventually_dia env A
  | eventually_dia env (A.TpName(a,es)) = eventually_dia env (A.expd_tp env (a,es))
  | eventually_dia env (A.Dot) = true (* pseudo-type *)
  | eventually_dia _ _ = false

(***********************)
(* Operations on types *)
(***********************)

fun decrementL env ctx con (A.Next(t,A)) t' ext =
    if C.entails ctx con (R.Ge(t,t'))
    then A.Next(R.minus (t,t'),A)
    else if C.entails ctx con (R.Le(t,t')) (* was: R.Lt, -fp Fri Feb  8 07:30:35 2019 *)
    then decrementL env ctx con A (R.minus (t',t)) ext
    else ERROR ext ("cannot decide: " ^ C.pp_unrel con t t')
  | decrementL env ctx con (A.Box(A)) t' ext = A.Box(A)
  | decrementL env ctx con (A.TpName(a,es)) t' ext = decrementL env ctx con (A.expd_tp env (a,es)) t' ext
  (* imaginary (and cost-free) constructs are transparent *)
  (* unfortunately these violate progress because the endpoints of
   * imaginary transaction may be at different points in time
   *)
  (*
  | decrementL env ctx con (A.Exists(phi,A)) t' ext = A.Exists(phi, decrementL env ctx con A t' ext)
  | decrementL env ctx con (A.Forall(phi,A)) t' ext = A.Forall(phi, decrementL env ctx con A t' ext)
  | decrementL env ctx con (A.PayPot(p,A)) t' ext = A.PayPot(p, decrementL env ctx con A t' ext)
  | decrementL env ctx con (A.GetPot(p,A)) t' ext = A.GetPot(p, decrementL env ctx con A t' ext)
  *)
  | decrementL env ctx con (A.Dot) t' ext = A.Dot  (* pseudo-type *)
  | decrementL env ctx con A t' ext =
    if C.entails ctx con (R.Eq(t',R.Int(0)))
    then A
    else ERROR ext ("left type " ^ PP.pp_tp_compact env A ^ " is neither (_)A nor []A :\n"
                    ^ C.pp_jfail con (R.Eq(t',R.Int(0))))

fun decrementR env ctx con (A.Next(t,A)) t' ext =
    if C.entails ctx con (R.Ge(t,t'))
    then A.Next(R.minus(t,t'),A)
    else if C.entails ctx con (R.Le(t,t')) (* was: R.Lt, -fp Fri Feb  8 07:30:47 2019 *)
    then decrementR env ctx con A (R.minus (t',t)) ext
    else ERROR ext ("cannot decide: " ^ C.pp_unrel con t' t)
  | decrementR env ctx con (A.Dia(A)) t' ext = A.Dia(A)
  | decrementR env ctx con (A.TpName(a,es)) t' ext = decrementR env ctx con (A.expd_tp env (a,es)) t' ext
  (* imaginary (and cost-free) constructs are transparent *)
  (* unfortunately these violate progress because the endpoints of
   * imaginary transaction may be at different points in time
   *)
  (*
  | decrementR env ctx con (A.Exists(phi,A)) t' ext = A.Exists(phi, decrementR env ctx con A t' ext)
  | decrementR env ctx con (A.Forall(phi,A)) t' ext = A.Forall(phi, decrementR env ctx con A t' ext)
  | decrementR env ctx con (A.PayPot(p,A)) t' ext = A.PayPot(p, decrementR env ctx con A t' ext)
  | decrementR env ctx con (A.GetPot(p,A)) t' ext = A.GetPot(p, decrementR env ctx con A t' ext)
  *)
  | decrementR env ctx con A t' ext =
    if C.entails ctx con (R.Eq(t',R.Int(0)))
    then A
    else ERROR ext ("right type " ^ PP.pp_tp_compact env A ^ " is neither (_)A or <>A :\n"
                    ^ C.pp_jfail con (R.Eq(t',R.Int(0))))

(*****************)
(* Type equality *)
(*****************)

(* eq_id ctx con e e' iff ctx ; con |= e = e' *)
fun eq_id ctx con e e' = C.entails ctx con (R.Eq(e,e'))

(* eq_idx ctx con es es', assumes |es| = |es'| *)
fun eq_idx ctx con nil nil = true
  | eq_idx ctx con (e::es) (e'::es') =
      eq_id ctx con e e' andalso eq_idx ctx con es es'

(* Type equality, equirecursively defined *)

(* Structural equality *)

fun mem_env (A.TpEq(CTX,CON,A as A.TpName(B,ES),A' as A.TpName(B',ES'),_)::env) a a' =
    if B = a andalso B' = a'
    then SOME(CTX,CON,(A,A'))
    else if B = a' andalso B' = a
    then SOME(CTX,CON,(A',A))   (* flip! *)
    else mem_env env a a'
  | mem_env (_::env) a a' = mem_env env a a'
  | mem_env nil a a' = NONE

fun mem_seen env ((E as (CTX,CON,(A as A.TpName(B, ES), A' as A.TpName(B', ES'))))::seen) a a' =
    if B = a andalso B' = a'
    then SOME(CTX,CON,(A,A'))
    else if B = a' andalso B' = a
    then SOME(CTX,CON,(A',A))
    else mem_seen env seen a a'
  | mem_seen env (_::seen) a a' = mem_seen env seen a a'
  | mem_seen env nil a a' = mem_env env a a'

fun fresh v = "%" ^ v

fun gen_fresh nil = (nil, nil)
  | gen_fresh (v::vs) =
    let val fv = fresh v
        val (fvs, sigma) = gen_fresh vs
    in
      (fv::fvs,(v, R.Var(fv))::sigma)
    end

fun gen_eq nil nil = R.True
  | gen_eq (E::ES) (e::es) = R.And(R.Eq(E,e), gen_eq ES es)

fun gen_prop_eq FCTX FCON FES es FES' es' =
    let val eqs = gen_eq FES es
        val eqs' = gen_eq FES' es'
        val and_prop = R.And(FCON, R.And(eqs, eqs'))
        val nnf_prop = R.nnf and_prop
        val exists_prop = R.elim_vars FCTX nnf_prop (* exists_prop is in NNF, but not using it *)
    in
        exists_prop
    end

(* strip_next0 ctx con A = A' preserves definitions for tracing
 * purposes but strips off all prefixes (t)A' if con |= t = 0.
 * For use in type equality, see aggregate_nexts
 *)
fun strip_next0 env ctx con (A as A.Next(t,A')) =
    if C.entails ctx con (R.Eq(t,R.Int(0)))
    then strip_next0 env ctx con A'
    else A
  | strip_next0 env ctx con A = A

(* aggregate_nexts' env ctx con s A = A'
 * where all initial next-time operators in A are added to S.
 * If the result is 0, the next-time operators is stripped entirely.
 *)
fun aggregate_nexts' env ctx con s (A.Next(t,A')) =
    aggregate_nexts' env ctx con (R.plus(s,t)) A'
  | aggregate_nexts' env ctx con s (A.TpName(a,es)) =
    aggregate_nexts' env ctx con s (A.expd_tp env (a,es))
  | aggregate_nexts' env ctx con s A = (* A <> Next _ *)
    if C.entails ctx con (R.Eq(s,R.Int(0)))
    then A
    else A.Next(s,A)

(* aggregate_nexts env ctx con A = A', where initial next-time
 * operators in A are combined into 0 or 1 operators.
 * Type definitions are not expanded unless A is a Next(_).
 * This ensures that, for example, ()()A and ({2})A are considered equal.
 *)
fun aggregate_nexts env ctx con (A as A.Next(t,A')) =
    aggregate_nexts' env ctx con t A'
  | aggregate_nexts env ctx con A = A

(* eq_tp env con seen A A' = true if (A = A'), defined coinductively *)
fun eq_tp' env ctx con seen A A' =
    eq_tp env ctx con seen
          (aggregate_nexts env ctx con A)
          (aggregate_nexts env ctx con A')

and eq_tp env ctx con seen (A.Plus(choice)) (A.Plus(choice')) =
    eq_choice env ctx con seen choice choice'
  | eq_tp env ctx con seen (A.With(choice)) (A.With(choice')) =
    eq_choice env ctx con seen choice choice'
  | eq_tp env ctx con seen (A.One) (A.One) = true

  | eq_tp env ctx con seen (A.Exists(phi,A)) (A.Exists(phi',A')) =
    C.equiv ctx con phi phi'
    andalso eq_tp' env ctx (R.And(con,phi)) seen A A'
    (* for now, require equality even in the presence of contradictory constraints *)
    (* orelse C.contradictory ctx con phi *)
  | eq_tp env ctx con seen (A.Forall(phi,A)) (A.Forall(phi',A')) =
    C.equiv ctx con phi phi'
    andalso eq_tp' env ctx (R.And(con,phi)) seen A A'
    (* for now, require equality even in the presence of contradictory constraints *)
    (* orelse C.contradictory ctx con phi *)

  | eq_tp env ctx con seen (A.PayPot(p,A)) (A.PayPot(p',A')) =
    eq_id ctx con p p' andalso eq_tp' env ctx con seen A A'
  | eq_tp env ctx con seen (A.GetPot(p,A)) (A.GetPot(p',A')) = 
    eq_id ctx con p p' andalso eq_tp' env ctx con seen A A'

  | eq_tp env ctx con seen (A.Next(t,A)) (A.Next(t',A')) =
    eq_id ctx con t t' andalso eq_tp' env ctx con seen A A'
  | eq_tp env ctx con seen (A.Box(A)) (A.Box(A')) =
    eq_tp' env ctx con seen A A'
  | eq_tp env ctx con seen (A.Dia(A)) (A.Dia(A')) =
    eq_tp' env ctx con seen A A'

  | eq_tp env ctx con seen (A as A.TpName(a,es)) (A' as A.TpName(a',es')) =
    if a = a' then eq_idx ctx con es es' (* reflexivity *)
    else eq_name_name env ctx con seen A A' (* coinductive type equality *)
  | eq_tp env ctx con seen (A as A.TpName(a,es)) A' =
    eq_tp' env ctx con seen (A.expd_tp env (a,es)) A'
  | eq_tp env ctx con seen A (A' as A.TpName(a',es')) =
    eq_tp' env ctx con seen A (A.expd_tp env (a',es'))

  | eq_tp env ctx con seen A.Dot A.Dot = true
  | eq_tp env ctx con seen A A' = false

and eq_choice env ctx con seen nil nil = true
  | eq_choice env ctx con seen ((l,A)::choice) ((l',A')::choice') = (* order must be equal *)
    l = l' andalso eq_tp' env ctx con seen A A'
    andalso eq_choice env ctx con seen choice choice'
  | eq_choice env ctx con seen ((l,A)::choice) nil = false
  | eq_choice env ctx con seen nil ((l',A')::choice') = false

and eq_name_name env ctx con seen (A as A.TpName(a,es)) (A' as A.TpName(a',es')) =
    case mem_seen env seen a a'
     of NONE => eq_tp' env ctx con ((ctx,con,(A,A'))::seen)
                       (A.expd_tp env (a,es)) (A.expd_tp env (a',es'))
      | SOME(CTX,CON, (A.TpName(_,ES), A.TpName(_,ES'))) =>
        let val (FCTX,sigma) = gen_fresh CTX
            val FCON = R.apply_prop sigma CON
            val FES = R.apply_list sigma ES
            val FES' = R.apply_list sigma ES'
        in
            C.entails ctx con (gen_prop_eq FCTX FCON FES es FES' es') (* could be trusting non-linear *)
        end

(*****************************)
(* Operations on expressions *)
(*****************************)

(* expd env a{es} = A for a type a{vs} = A *)
fun expd env (A.TpName(a,es)) = A.expd_tp env (a,es)

(* zip_check f vs es ext = [es/vs]
 * raises ErrorMsg.Error if |es| <> |vs|
 *)
fun zip_check f vs es ext =
    let val () = if List.length es = List.length vs then ()
                 else ERROR ext ("process " ^ f
                                 ^ " called with " ^ Int.toString (List.length es) ^ " indices "
                                 ^ "but defined with " ^ Int.toString (List.length vs))
    in R.zip vs es end

(* expd_expdec_check env f{es} ext = [es/vs](con, (A, p, C))
 * if vs ; con ; A |{p}- f : C
 * raises ErrorMsg.Error if f undeclared or |es| <> |vs|
 *)
fun expd_expdec_check env (f,es) ext =
    (case A.lookup_expdec env f
      of SOME(vs,con,(A,pot,C)) =>
         let val sg = zip_check f vs es ext
         in (R.apply_prop sg con, (A.apply_tp sg A, R.apply sg pot, A.apply_tp sg C)) end
       | NONE => E.error_undeclared (f, ext))

(* syn_cut env (f{es} || Q) ext = f{es} {[es/vs] |{p}-B } Q 
 * if vs ; con ; A |{p}- f : B
 * raises ErrorMsg.Error if P || Q where P is not a process name,
 * f is undeclared, or |es| <> |vs|
 *)
fun syn_cut env (P as A.ExpName(f,es), Q) ext =
    (case A.lookup_expdec env f
      of SOME(vs,con,(A,pot,B)) =>
         let val sg = zip_check f vs es ext
         in A.Cut(P, R.apply sg pot, A.apply_tp sg B, Q) end
       | NONE => ERROR ext ("process " ^ f ^ " undeclared"))
  | syn_cut env (A.Marked(marked_P), Q) ext = (* Q: preserve mark? *)
    syn_cut env (Mark.data marked_P, Q) (Mark.ext marked_P)
  | syn_cut env P ext = ERROR ext ("left-hand side of spawn '||' must be a process name")

(* syn_call env f{es} ext = [vs/es](con, (A, p, C))
 * if vs ; con ; A |{p}- f : C
 * raises ErrorMsg.Error if f undeclared or |es| <> |vs|
 *)
fun syn_call env (P as A.ExpName(f,es)) ext =
    (case A.lookup_expdec env f
      of SOME(vs,con,(A,pot,B)) =>
         let val sg = zip_check f vs es ext
         in (A.apply_tp sg A, R.apply sg pot, P, A.apply_tp sg B) end
       | NONE => ERROR ext ("process " ^ f ^ " undeclared"))
  | syn_call env (A.Marked(marked_P)) ext = (* Q: preserve mark? *)
    syn_call env (Mark.data marked_P) (Mark.ext marked_P)
  | syn_call env P ext = ERROR ext ("call must be a process name")

(* synL env (f,es) = A where A |- f : _, approximately *)
fun synL env (f, es) =
    (case A.expd_expdec env (f, es)
      of SOME(con, (A, pot, C)) => A
         (* NONE impossible, since f{es} approximately typed *)
    )

(* synR env (f,es) = C where _ |- f : C, approximately *)
fun synR env (f, es) =
    (case A.expd_expdec env (f,es)
      of SOME(con, (A, pot, C)) => C
         (* NONE impossible, since f{es} approximately typed *)
    )

(* synLR env (f,es) = (A,pot,C) where A |{pot}- f : C, approximately *)
fun synLR env (f, es) =
    (case A.expd_expdec env (f,es)
      of SOME(con, (A, pot, C)) => (A, pot, C)
         (* NONE impossible, since f{es} approximately typed *)
    )

(* syn_alt env (l => Al)_(l in L) k = Ak, assumes k in L *)
fun syn_alt env choices k = Option.valOf (A.lookup_choice choices k)

(*************************************)
(* Type checking process expressions *)
(*************************************)
                            
fun interactsL P = case P of
    A.CaseL _ => true | A.LabL _ => true | A.WaitL _ => true
  | A.WhenL _ => true | A.NowL _ => true
  | A.GetL _ => true | A.PayL _ => true
  | A.AssumeL _ => true | A.AssertL _ => true
  | A.Marked(marked_exp) => interactsL (Mark.data marked_exp)
  | _ => false

fun interactsR P = case P of
    A.CaseR _ => true | A.LabR _ => true | A.CloseR => true
  | A.WhenR _ => true | A.NowR _ => true
  | A.GetR _ => true | A.PayR _ => true
  | A.AssumeR _ => true | A.AssertR _ => true
  | A.Marked(marked_exp) => interactsR (Mark.data marked_exp)
  | _ => false

fun is_tpname (A.TpName(a,l)) = true
  | is_tpname _ = false

(* check_explist_pos ctx con es ext = ()
 * if ctx ; con |= e >= 0 for all e in es
 * raises ErrorMsg.Error otherwise
 *)
fun check_explist_pos ctx con (nil) ext = ()
  | check_explist_pos ctx con (e::es) ext =
    if not(C.entails ctx con (R.Ge(e, R.Int(0))))
    then ERROR ext ("index cannot be shown to be positive: " ^ C.pp_jfail con (R.Ge(e, R.Int(0))))
    else check_explist_pos ctx con es ext

(* check_exp trace env ctx con A pot P C = () if A |{pot}- P : C
 * raises ErrorMsg.Error otherwise
 * assumes ctx ; con |= A valid
 *         ctx ; con |= C valid
 *         ctx ; con |= pot nat
 *
 * trace = true means to print some tracing information
 *
 * entry point is check_exp'
 *
 * We expand type definitions lazily, based on the direction of
 * interactions.  This is done so tracing (if enabled) or error
 * message are more intelligible.
 *)
fun check_exp' trace env ctx con A pot P C ext =
    ( if trace
      then TextIO.print (PP.pp_exp_prefix env P ^ " : "
                         ^ PP.pp_tpj_compact env A pot C ^ "\n")
      else ()
    ; check_exp trace env ctx con (strip_next0 env ctx con A) pot P (strip_next0 env ctx con C) ext )

and (* judgmental constructs: id, cut, spawn, call *)
    check_exp trace env ctx con A pot (A.Id) C ext =
    if not (C.entails ctx con (R.Eq(pot, R.Int(0))))
    then ERROR ext ("unconsumed potential: " ^ C.pp_jfail con (R.Eq(pot, R.Int(0))))
    else if eq_tp' env ctx con nil A C
    then ()
    else ERROR ext ("type " ^ PP.pp_tp_compact env A ^ " not equal " ^ PP.pp_tp_compact env C)
  | check_exp trace env ctx con A pot (A.Cut(P,lpot,B,Q)) C ext =
    ( valid env ctx con Zero B ext (* interface type B must be valid *)
    ; if not (C.entails ctx con (R.Ge(lpot,R.Int(0)))) (* and potential >= 0 *)
      then ERROR ext ("potential not positive: " ^ C.pp_jfail con (R.Ge(lpot, R.Int(0))))
      else if not (C.entails ctx con (R.Ge(pot, lpot)))
      then ERROR ext ("insufficient potential: " ^ C.pp_jfail con (R.Ge(pot, lpot)))
      else ( check_exp' trace env ctx con A lpot P B ext
           ; check_exp' trace env ctx con B (R.minus(pot,lpot)) Q C ext )
    )
  | check_exp trace env ctx con A pot (A.Spawn(P,Q)) C ext =
    check_exp trace env ctx con A pot (syn_cut env (P,Q) ext) C ext
  | check_exp trace env ctx con A pot (A.ExpName(f,es)) C ext =
    (* verify the type, but also make sure f is defined somewhere *)
    (case (expd_expdec_check env (f,es) ext, A.lookup_expdef env f)
      of ((con',(A',pot',C')), SOME _) =>
         let val () = if eq_tp' env ctx con nil A A' then ()
                      else ERROR ext ("type " ^ PP.pp_tp_compact env A ^ " not equal " ^ PP.pp_tp_compact env A')
             val () = if eq_tp' env ctx con nil C' C then ()
                      else ERROR ext ("type " ^ PP.pp_tp_compact env C' ^ " not equal " ^ PP.pp_tp_compact env C)
             val () = if not (C.entails ctx con (R.Eq(pot, pot')))
                      then ERROR ext ("potential mismatch: " ^ C.pp_jfail con (R.Eq(pot, pot')))
                      else ()
             val () = check_explist_pos ctx con es ext
             val () = if not (C.entails ctx con con')
                      then ERROR ext ("constraint not entailed: " ^ C.pp_jfail con con')
                      else ()
         in () end
       | (_, NONE) => E.error_undeclared (f, ext)
    )
    
  (* structural types +{...}, &{...}, 1 *)
  | check_exp trace env ctx con A pot (A.LabR(k,P)) (C as A.Plus(choices)) ext =
    (case A.lookup_choice choices k
      of SOME(Ck) => check_exp' trace env ctx con A pot P Ck ext
       | NONE => E.error_label_invalid env (k, C, ext))
  | check_exp trace env ctx con (A.Plus(choices)) pot (A.CaseL(branches)) C ext =
    check_branchesL trace env ctx con choices pot branches C ext

  | check_exp trace env ctx con A pot (A.CaseR(branches)) (A.With(choices)) ext =
    check_branchesR trace env ctx con A pot branches choices ext
  | check_exp trace env ctx con (A as A.With(choices)) pot (A.LabL(k,Q)) C ext =
    (case A.lookup_choice choices k
      of SOME(Ak) => check_exp' trace env ctx con Ak pot Q C ext
       | NONE => E.error_label_invalid env (k, A, ext))

  | check_exp trace env ctx con (A.Dot) pot (A.CloseR) (A.One) ext =
    if not (C.entails ctx con (R.Eq(pot, R.Int(0))))
    then ERROR ext ("unconsumed potential: " ^ C.pp_jfail con (R.Eq(pot, R.Int(0))))
    else ()
  | check_exp trace env ctx con (A.One) pot (A.WaitL(Q)) C ext =
    check_exp' trace env ctx con (A.Dot) pot Q C ext

  (* quantified types ?{phi}.A, !{phi}.A *)
  (* existential ?{phi}. A *)
  | check_exp trace env ctx con A pot (A.AssertR(phi,P)) (A.Exists(phi',C)) ext =
    if not (C.entails ctx con phi)
    then ERROR ext ("assertion not entailed: " ^ C.pp_jfail con phi)
    else if not (C.entails ctx con phi') (* equivalent would be con, phi |= phi' *)
    then ERROR ext ("type constraint not entailed: " ^ C.pp_jfail con phi')
    else check_exp' trace env ctx con A pot P C ext
  | check_exp trace env ctx con (A.Exists(phi',A)) pot (A.AssumeL(phi,Q)) C ext =
    if not (C.entails ctx (R.And(con,phi')) phi) (* con, phi' |= phi *)
    then ERROR ext ("assumption not entailed: " ^ C.pp_jfail (R.And(con,phi')) phi)
    else check_exp' trace env ctx (R.And(con,phi)) A pot Q C ext (* assume the possibly weaker phi *)
  (* universal !{phi}. A *)
  | check_exp trace env ctx con A pot (A.AssumeR(phi,P)) (A.Forall(phi',C)) ext =
    if not (C.entails ctx (R.And(con,phi')) phi)
    then ERROR ext ("assumption not entailed: " ^ C.pp_jfail (R.And(con,phi')) phi)
    else check_exp' trace env ctx (R.And(con,phi)) A pot P C ext (* assume only the possibly weaker phi *)
  | check_exp trace env ctx con (A.Forall(phi',A)) pot (A.AssertL(phi,Q)) C ext =
    if not (C.entails ctx con phi)
    then ERROR ext ("assertion not entailed: " ^ C.pp_jfail con phi)
    else if not (C.entails ctx con phi') (* equivalent would be con, phi |= phi' *)
    then ERROR ext ("type constraint not entailed: " ^ C.pp_jfail con phi')
    else check_exp' trace env ctx con A pot Q C ext

  (* impossibility *)
  | check_exp trace env ctx con A pot (A.Imposs) C ext =
    if not (C.contradictory ctx con R.True) (* TODO: fix interface *)
    then ERROR ext ("constraints not contradictory: " ^ C.pp_jsat con R.True)
    else ()

  (* ergometric types |>, <| *)
  | check_exp trace env ctx con A pot (A.Work(p,P)) C ext =
    if not (C.entails ctx con (R.Ge(p,R.Int(0))))
    then ERROR ext ("potential not positive: " ^ C.pp_jfail con (R.Ge(p,R.Int(0))))
    else if not (C.entails ctx con (R.Ge(pot,p)))
    then ERROR ext ("insufficient potential: " ^ C.pp_jfail con (R.Ge (pot, p)))
    else check_exp' trace env ctx con A (R.minus(pot,p)) P C ext
  | check_exp trace env ctx con A pot (A.PayR(p',P)) (A.PayPot(p,C)) ext =
    (* con |= p >= 0 since type is valid *)
    if not (C.entails ctx con (R.Ge(pot,p')))
    then ERROR ext ("insufficient potential: " ^ C.pp_jfail con (R.Ge(pot, p')))
    else if not (C.entails ctx con (R.Eq(p',p)))
    then ERROR ext ("potential mismatch: " ^ C.pp_jfail con (R.Eq(p',p)))
    else check_exp' trace env ctx con A (R.minus (pot,p)) P C ext
  | check_exp trace env ctx con (A.PayPot(p,A)) pot (A.GetL(p',P)) C ext =
    (* con |= p >= 0 since type is valid *)
    if not (C.entails ctx con (R.Eq(p,p')))
    then ERROR ext ("potential mismatch: " ^ C.pp_jfail con (R.Eq(p,p')))
    else check_exp' trace env ctx con A (R.plus (pot,p)) P C ext
  | check_exp trace env ctx con A pot (A.GetR(p',P)) (A.GetPot(p,C)) ext =
    (* con |= p >= 0 since type is valid *)
    if not (C.entails ctx con (R.Eq(p',p)))
    then ERROR ext ("potential mismatch: " ^ C.pp_jfail con (R.Eq(p',p)))
    else check_exp' trace env ctx con A (R.plus (pot,p)) P C ext
  | check_exp trace env ctx con (A.GetPot(p,A)) pot (A.PayL(p',P)) C ext =
    (* con |= p >= 0 since type is valid *)
    if not (C.entails ctx con (R.Ge(pot,p)))
    then ERROR ext ("insufficient potential: " ^ C.pp_jfail con (R.Ge (pot, p)))
    else if not (C.entails ctx con (R.Eq(p,p')))
    then ERROR ext ("potential mismatch: " ^ C.pp_jfail con (R.Eq(p,p')))
    else check_exp' trace env ctx con A (R.minus (pot,p)) P C ext

  (* temporal types (), [], <> *)
  | check_exp trace env ctx con A pot (A.Delay(t,P)) C ext =
    if not(C.entails ctx con (R.Ge(t,R.Int(0))))
    then ERROR ext ("delay cannot be shown to be positive : " ^ C.pp_jfail con (R.Ge(t,R.Int(0))))
    else check_exp' trace env ctx con (decrementL env ctx con A t ext) pot P (decrementR env ctx con C t ext) ext
  | check_exp trace env ctx con A pot (A.NowR(P)) (A.Dia(C)) ext =
    check_exp' trace env ctx con A pot P C ext
  | check_exp trace env ctx con (A.Dia(A)) pot (A.WhenL(Q)) C ext =
    let val () = if eventually_dia env C then ()
                 else ERROR ext ("type " ^ PP.pp_tp_compact env C ^ " is not patient (ie, not (n)<>A")
    in
        check_exp' trace env ctx con A pot Q C ext
    end
  | check_exp trace env ctx con A pot (A.WhenR(P)) (A.Box(C)) ext =
    let val () = if eventually_box env A then ()
                 else ERROR ext ("type " ^ PP.pp_tp_compact env A ^ " is not patient (ie, not (n)[]A")
    in
        check_exp' trace env ctx con A pot P C ext
    end
  | check_exp trace env ctx con (A.Box(A)) pot (A.NowL(Q)) C ext =
    check_exp' trace env ctx con A pot Q C ext

  (* marked expressions *)
  | check_exp trace env ctx con A pot (A.Marked(marked_P)) C ext =
    check_exp trace env ctx con A pot (Mark.data marked_P) C (Mark.ext marked_P)

  (* type definitions or error messages *)
  | check_exp trace env ctx con A pot P C ext =
    if interactsL P
    then if is_tpname A
         then check_exp' trace env ctx con (expd env A) pot P C ext
         else ERROR ext ("process interacts left but does not match left type\n"
                         ^ PP.pp_tpj env A pot C)
    else if interactsR P
    then if is_tpname C
         then check_exp' trace env ctx con A pot P (expd env C) ext
         else ERROR ext ("process interacts right but does not match right type\n"
                         ^ PP.pp_tpj env A pot C)
    else (* not sure if this is possible *)
        ERROR ext ("process does not match types" ^ PP.pp_tpj env A pot C)

(* check_branchesL env ctx con choices branches C ext = ()
 * for client of internal choice +{...}
 *)
and check_branchesL trace env ctx con nil pot nil C ext = ()
  | check_branchesL trace env ctx con ((l,A)::choices) pot ((l',ext',P)::branches) C ext =
    (* require exact order *)
    ( if trace then TextIO.print ("| " ^ l' ^ " => \n") else ()
    ; if l = l' then () else E.error_label_mismatch (l, l', ext')
    ; check_exp' trace env ctx con A pot P C ext
    ; check_branchesL trace env ctx con choices pot branches C ext )
  | check_branchesL trace env ctx con ((l,A)::_) pot nil C ext = E.error_label_missing_branch (l, ext)
  | check_branchesL trace env ctx con nil pot ((l',ext',P)::_) C ext = E.error_label_missing_alt (l', ext')

(* check_branchesR trace env ctx con A branches choices = ()
 * for provider of external choice &{...}
 *)
and check_branchesR trace env ctx con A pot nil nil ext = ()
  | check_branchesR trace env ctx con A pot ((l,ext',P)::branches) ((l',C)::choices) ext =
    (* require exact order *)
    ( if trace then TextIO.print ("| " ^ l ^ " => \n") else ()
    ; if l = l' then () else E.error_label_mismatch (l, l', ext')
    ; check_exp' trace env ctx con A pot P C ext
    ; check_branchesR trace env ctx con A pot branches choices ext )
  | check_branchesR trace env ctx con A pot ((l,ext',P)::_) nil ext = E.error_label_missing_alt (l, ext')
  | check_branchesR trace env ctx con A pot nil ((l',C)::_) ext = E.error_label_missing_branch (l', ext)

(* external interface *)
val check_exp = check_exp'      (* entry point for tracing *)
val eq_tp = fn env => fn ctx => fn con => fn A => fn B =>
            eq_tp' env ctx con nil A B

end (* structure TypeCheck *)
