(* Type Checking Utilities *)
(* Authors: Ankush Das <ankushd@cs.cmu.edu>
 *          Frank Pfenning <fp@cs.cmu.edu>
 *)

signature TYPE_CHECK_UTIL =
sig

    (* operations on approximately typed expressions (see arecon.sml) *)
    (* synthesizing the expected types *)
    val syn_call : Ast.env -> Ast.context -> Ast.exp -> Ast.ext -> Ast.context (* may raise ErrorMsg.error *)
    val syn_pot : Ast.env -> Ast.exp -> Ast.ext -> Ast.pot                     (* may raise ErrorMsg.error *)

    (*
    val synL : Ast.env -> (Ast.chan * Ast.expname * Arith.arith list * Ast.chan list) -> Ast.context
    val synR : Ast.env -> (Ast.chan * Ast.expname * Arith.arith list * Ast.chan list) -> Ast.chan_tp
    *)

    val syn_altR : Ast.env -> Ast.chan_tp -> Ast.label -> Ast.chan_tp
    val syn_altL : Ast.env -> Ast.context -> Ast.chan -> Ast.label -> Ast.context
    val syn_sendR : Ast.env -> Ast.chan_tp -> Ast.chan_tp
    val syn_sendL : Ast.env -> Ast.context -> Ast.chan -> Ast.context
    val syn_recvR1 : Ast.env -> Ast.context -> Ast.chan_tp -> Ast.chan -> Ast.context
    val syn_recvR2 : Ast.env -> Ast.chan_tp -> Ast.chan_tp
    val syn_recvL : Ast.env -> Ast.context -> Ast.chan -> Ast.chan -> Ast.context
    val syn_waitL : Ast.env -> Ast.context -> Ast.chan -> Ast.context

    val syn_branchesR : Ast.env -> Ast.chan_tp -> Ast.chan * Ast.choices

    val syn_branchesL : Ast.env -> Ast.context -> Ast.chan -> Ast.chan * Ast.choices

    val syn_assertR : Ast.env -> Ast.chan_tp -> Ast.chan_tp
    val syn_assertL : Ast.env -> Ast.context -> Ast.chan -> Ast.context
    val syn_assumeR : Ast.env -> Ast.chan_tp -> Ast.chan_tp
    val syn_assumeL : Ast.env -> Ast.context -> Ast.chan -> Ast.context

    val syn_sendNatR : Ast.env -> Arith.arith -> Ast.chan_tp -> Ast.chan_tp
    val syn_sendNatL : Ast.env -> Ast.context -> Arith.arith -> Ast.chan -> Ast.context
    val syn_recvNatR : Ast.env -> Arith.varname -> Ast.chan_tp -> Ast.chan_tp
    val syn_recvNatL : Ast.env -> Ast.context -> Ast.chan -> Arith.varname -> Ast.context

    (* context manipulation *)
    val remove_chans : Ast.chan list -> Ast.context -> Ast.ext -> Ast.context
    val remove_chan : Ast.chan -> Ast.context -> Ast.ext -> Ast.context
    val update_tp : Ast.chan_tp -> Ast.context -> Ast.context
    val lookup_context : Ast.env -> Ast.chan -> Ast.context -> Ast.ext -> Ast.tp

    val expd_expdec_check : Ast.env -> (Ast.expname * Ast.tp list * Arith.arith list) -> Ast.ext
                            -> Arith.prop * (Ast.context * Ast.pot * Ast.chan_tp)
    (* may raise ErrorMsg.error *)

end (* signature TYPE_CHECK_UTIL *)


structure TypeCheckUtil :> TYPE_CHECK_UTIL =
struct

structure R = Arith
structure A = Ast
structure PP = PPrint
structure E = TpError
structure TU = TypeUtil
structure TEQ = TypeEquality
structure C = Constraints
val ERROR = ErrorMsg.ERROR

fun lookup_context env x ((y,A)::D') ext = if x = y then TU.expand env A else lookup_context env x D' ext
  | lookup_context env x nil ext = ERROR ext ("channel " ^ x ^ " not present in context")

fun update_tp (x,A) ((y,B)::D') = if x = y then (x,A)::D' else (y,B)::(update_tp (x,A) D')
    (* nil should be impossible *)

fun remove_chan x ((y,B)::D') ext = if x = y then D' else (y,B)::(remove_chan x D' ext)
  | remove_chan x nil ext = ERROR ext ("channel " ^ x ^ " not present in context")

fun remove_chans (x::xs) D ext = remove_chans xs (remove_chan x D ext) ext
  | remove_chans nil D ext = D

(* zip_check f vs es ext = [es/vs]
 * raises ErrorMsg.Error if |es| <> |vs|
 *)
fun zip_check f vs es ext =
    let val () = if List.length es = List.length vs then ()
                 else ERROR ext ("process " ^ f ^ " called with incorrect number of indices:\n"
                                 ^ "expected " ^ Int.toString (List.length vs) ^ "\n"
                                 ^ "found " ^ Int.toString (List.length es))
    in R.zip vs es end

(* expd_expdec_check env f{es} ext = [es/vs](con, (A, p, C))
 * if vs ; con ; A |{p}- f : C
 * raises ErrorMsg.Error if f undeclared or |es| <> |vs|
 *)
fun expd_expdec_check env (f,As,es) ext =
    (case A.lookup_expdec env f
      of SOME(alphas,vs,con,(D,pot,zC)) =>
         let val () = if List.length As = List.length alphas then ()
                      else E.error_tparam_number "call" (List.length alphas, List.length As) ext
             val () = if List.length es = List.length vs then ()
                      else E.error_index_number "call" (List.length vs, List.length es) ext
             val sg = R.zip vs es
         (* !!! *)
         in (R.apply_prop sg con, (A.apply_context sg D, R.apply sg pot, A.apply_chan_tp sg zC)) end
       | NONE => E.error_undeclared (f, ext)
    )

(* syn_call env D (x <- f{es} <- ys) ext = (x : [es/vs]A) (D-ys)
 * if vs ; con ; D' |{p}- f : A
 * raises ErrorMsg.Error if f undeclared or |es| <> |vs|
 *)
fun syn_call env D (P as A.ExpName(x,f,As,es,ys)) ext =
    let val (con', (D', pot', (x',A))) = expd_expdec_check env (f,As,es) ext
        val contD = remove_chans ys D ext
        val () = if List.exists (fn (y,_) => x = y) contD
                 then E.error_channel_mismatch "call" ("fresh <id>", x) ext
                 else ()
    in (x,A)::contD end
  | syn_call env D (A.Marked(marked_P)) ext =
    syn_call env D (Mark.data marked_P) (Mark.ext marked_P)

(* syn_pot env D (x <- f{es} <- ys) ext = [es/vs]p
 * if vs ; con ; D' |{p}- f : B
 * raises ErrorMsg.Error if f undeclared or |es| <> |vs|
 *)
fun syn_pot env (P as A.ExpName(x,f,As,es,ys)) ext =
    let val (con', (D', pot', (x',A'))) = expd_expdec_check env (f,As,es) ext
    in pot' end
  | syn_pot env (A.Marked(marked_P)) ext =
    syn_pot env (Mark.data marked_P) (Mark.ext marked_P)

(*
(* synL env (f,es) = D where D |- f : _, approximately *)
fun synL env (y, f, es, xs) =
    (case A.expd_expdec env (f, es)
      of SOME(con, (D, pot, zC)) => ListPair.mapEq (fn (x,(x',A')) => (x,A')) (xs,D)
         (* NONE impossible, since f{es} approximately typed *)
    )

(* synR env (f,es) = C where _ |- f : C, approximately *)
fun synR env (y, f, es, xs) =
    (case A.expd_expdec env (f,es)
      of SOME(con, (D, pot, (z,C))) => (y,C)
         (* NONE impossible, since f{es} approximately typed *)
    )

(* synLR env (f,es) = (D,pot,C) where D |{pot}- f : C, approximately *)
fun synLR env (f, es) =
    (case A.expd_expdec env (f,es)
      of SOME(con, (D, pot, zC)) => (D, pot, zC)
         (* NONE impossible, since f{es} approximately typed *)
    )
*)

(* syn_altR env z +(l : Al)_(l in L) k = (z,Ak), assumes k in L *)
fun syn_altR' env z (A.Plus(choices)) k = (z, Option.valOf (A.lookup_choice choices k))
fun syn_altR env (z,C) k = syn_altR' env z (TU.expand env C) k

(* syn_altL env x &(l : Al)_(l in L) k = (x,Ak), assumes k in L *)
fun syn_altL' env x (A.With(choices)) k D = (x, Option.valOf (A.lookup_choice choices k))::D
fun syn_altL env ((x',A)::D') x k =
    if x' = x
    then syn_altL' env x' (TU.expand env A) k D'
    else (x',A)::syn_altL env D' x k
    (* nil impossile by approx typing *)

(* syn_sendR env z (A * B) = (z,B) *)
fun syn_sendR' env z (A.Tensor(A,B)) = (z,B)
fun syn_sendR env (z,C) = syn_sendR' env z (TU.expand env C)

(* syn_sendL env x (A -o B) = (x,B) *)
fun syn_sendL' env x (A.Lolli(A,B)) D = (x,B)::D
fun syn_sendL env ((x',A)::D') x  =
    if x' = x then syn_sendL' env x' (TU.expand env A) D'
    else (x',A)::syn_sendL env D' x
    (* nil impossible by approx typing *)

fun syn_recvR1' env y (A.Lolli(A,B)) D = (y,A)::D
fun syn_recvR1 env D (z,C) y = syn_recvR1' env y (TU.expand env C) D

fun syn_recvR2' env z (A.Lolli(A,B)) = (z,B)
fun syn_recvR2 env (z,C) = syn_recvR2' env z (TU.expand env C)

fun syn_recvL' env (y,x) (A.Tensor(A,B)) D = (y,A)::(x,B)::D
fun syn_recvL env ((x',A)::D') x y =
    if x' = x then syn_recvL' env (y,x) (TU.expand env A) D'
    else (x',A)::syn_recvL env D' x y

fun syn_waitL' env () (A.One) D = D
fun syn_waitL env ((x',A)::D') x =
    if x = x' then syn_waitL' env () (TU.expand env A) D'
    else (x',A)::syn_waitL env D' x

fun syn_branchesR' env z (A.With(choices)) = (z,choices)
fun syn_branchesR env (z,C) = syn_branchesR' env z (TU.expand env C)

fun syn_branchesL' env x (A.Plus(choices)) = (x,choices)
fun syn_branchesL env ((x',A)::D') x =
    if x = x' then syn_branchesL' env x (TU.expand env A)
    else syn_branchesL env D' x

fun syn_assertR' env z (A.Exists(phi,C)) = (z,C)
fun syn_assertR env (z,C) = syn_assertR' env z (TU.expand env C)

fun syn_assertL' env x (A.Forall(phi,A)) D = (x,A)::D
fun syn_assertL env ((x',A)::D') x =
    if x = x' then syn_assertL' env x (TU.expand env A) D'
    else (x',A)::syn_assertL env D' x

fun syn_assumeR' env z (A.Forall(phi,C)) = (z,C)
fun syn_assumeR env (z,C) = syn_assumeR' env z (TU.expand env C)

fun syn_assumeL' env x (A.Exists(phi,A)) D' = (x,A)::D'
fun syn_assumeL env ((x',A)::D') x =
    if x = x' then syn_assumeL' env x (TU.expand env A) D'
    else (x',A)::syn_assumeL env D' x

fun syn_sendNatR' env z e (A.ExistsNat(v,C)) = (z,A.apply_tp [(v,e)] C)
fun syn_sendNatR env e (z,C) = syn_sendNatR' env z e (TU.expand env C)

fun syn_sendNatL' env x e (A.ForallNat(v,A)) D = (x,A.apply_tp [(v,e)] A)::D
fun syn_sendNatL env ((x',A)::D') e x =
    if x = x' then syn_sendNatL' env x e (TU.expand env A) D'
    else (x',A)::syn_sendNatL env D' e x

fun syn_recvNatR' env v' z (A.ForallNat(v,C)) = (z,A.apply_tp [(v,R.Var(v'))] C)
fun syn_recvNatR env v' (z,C) = syn_recvNatR' env v' z (TU.expand env C)

fun syn_recvNatL' env x v' (A.ExistsNat(v,A)) D' = (x,A.apply_tp [(v,R.Var(v'))] A)::D'
fun syn_recvNatL env ((x',A)::D') x v' =
    if x = x' then syn_recvNatL' env x v' (TU.expand env A) D'
    else (x',A)::syn_recvNatL env D' x v'

end (* structure TypeCheckUtil *)
