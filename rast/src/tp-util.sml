(* Type Utilities *)
(* Authors: Ankush Das <ankushd@cs.cmu.edu>
 *          Frank Pfenning <fp@cs.cmu.edu>
 *)

signature TYPE_UTIL =
sig

    val expd : Ast.env -> Ast.tp -> Ast.tp  (* expand type definition, but also register abbreviation *)
    val expand : Ast.env -> Ast.tp -> Ast.tp (* expand until no longer a definition *)

    val eventually_box : Ast.env -> Ast.tp -> bool
    val eventually_dia : Ast.env -> Ast.tp -> bool

    (* decrement functions may raise ErrorMsg.error *)
    val decrementL : Ast.env -> Arith.ctx -> Arith.prop
                     -> Ast.tp -> Arith.arith -> Ast.ext -> Ast.tp
    val decrement_context : Ast.env -> Arith.ctx -> Arith.prop
                            ->  Ast.context -> Arith.arith -> Ast.ext -> Ast.context
    val decrementR : Ast.env -> Arith.ctx -> Arith.prop
                     -> Ast.tp -> Arith.arith -> Ast.ext -> Ast.tp

    val strip_next0 : Ast.env -> Arith.ctx -> Arith.prop -> Ast.chan_tp -> Ast.chan_tp
    val strip_next0_context : Ast.env -> Arith.ctx -> Arith.prop -> Ast.context -> Ast.context

end  (* signature TYPE_UTIL *)

structure TypeUtil :> TYPE_UTIL =
struct

structure R = Arith
structure A = Ast
structure PP = PPrint
structure C = Constraints
val ERROR = ErrorMsg.ERROR

(************************)
(* Expanding type names *)
(************************)

(* expd env a[As]{es} = [es/vs][As/alphas]A for a type a[alphas]{vs} = A *)
fun expd env (short as A.TpName(a,As,es)) =
    let val long = A.expd_tp env (a,As,es)
        val () = PP.Abbrev.register short long
    in long end

fun expand env (A as A.TpName(a,As,es)) = expand env (expd env A)
  | expand env A = A


(***********************)
(* Properties of types *)
(***********************)

(* needed for BoxR and DiaL rules *)
fun eventually_box env (A.Box(A)) = true
  | eventually_box env (A.Next(_,A)) = eventually_box env A
  | eventually_box env (A as A.TpName(a,As,es)) = eventually_box env (expd env A)
  | eventually_box _ _ = false

fun eventually_dia env (A.Dia(A)) = true
  | eventually_dia env (A.Next(_,A)) = eventually_dia env A
  | eventually_dia env (A as A.TpName(a,As,es)) = eventually_dia env (expd env A)
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
  | decrementL env ctx con (A as A.TpName(a,As,es)) t' ext = decrementL env ctx con (expd env A) t' ext
  | decrementL env ctx con A t' ext =
    if C.entails ctx con (R.Eq(t',R.Int(0)))
    then A
    else ERROR ext ("left type " ^ PP.pp_tp_compact env A ^ " is neither (_)A nor []A :\n"
                    ^ C.pp_jfail con (R.Eq(t',R.Int(0))))

fun decrement_context env ctx con D t ext =
    List.map (fn (x,A) => (x,decrementL env ctx con A t ext)) D

fun decrementR env ctx con (A.Next(t,A)) t' ext =
    if C.entails ctx con (R.Ge(t,t'))
    then A.Next(R.minus(t,t'),A)
    else if C.entails ctx con (R.Le(t,t')) (* was: R.Lt, -fp Fri Feb  8 07:30:47 2019 *)
    then decrementR env ctx con A (R.minus (t',t)) ext
    else ERROR ext ("cannot decide: " ^ C.pp_unrel con t' t)
  | decrementR env ctx con (A.Dia(A)) t' ext = A.Dia(A)
  | decrementR env ctx con (A as A.TpName(a,As,es)) t' ext = decrementR env ctx con (expd env A) t' ext
  | decrementR env ctx con A t' ext =
    if C.entails ctx con (R.Eq(t',R.Int(0)))
    then A
    else ERROR ext ("right type " ^ PP.pp_tp_compact env A ^ " is neither (_)A or <>A :\n"
                    ^ C.pp_jfail con (R.Eq(t',R.Int(0))))

(* stripnext0 ctx con A = A' preserves definitions for tracing
 * purposes but strips off all prefixes (t)A' if con |= t = 0.
 * For use in type equality, see aggregate_nexts
 *)
fun stripnext0 env ctx con (A as A.Next(t,A')) =
    if C.entails ctx con (R.Eq(t,R.Int(0)))
    then stripnext0 env ctx con A'
    else A
  | stripnext0 env ctx con A = A

fun strip_next0 env ctx con (x,A) = (x, stripnext0 env ctx con A)
fun strip_next0_context env ctx con D = List.map (fn xA => strip_next0 env ctx con xA) D

end  (* structure TypeUtil *)
