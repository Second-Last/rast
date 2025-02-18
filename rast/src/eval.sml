(* Evaluation *)
(* Author: Frank Pfenning <fp@cs.cmu.edu> *)

(* A sequential evaluator based on a shared memory semantics
 * proposed by Pruiksma and Pfenning (2019)
 *)

signature EVAL =
sig
    type value
    exception DynError
    val evaluate : Ast.env -> Ast.exp -> Ast.chan -> value (* may raise DynError *)

    structure Print :
    sig
        val pp_value : Ast.env -> value -> string
    end
end

structure Eval :> EVAL =
struct

structure R = Arith
structure A = Ast
structure PP = PPrint
val ERROR = ErrorMsg.ERROR

datatype value =
         Lab of A.label * value (* + *)
       | Send of value * value  (* * *)
       | Close                  (* 1 *)
       | SendNat of int * value (* ?v *) 
       | SendTp of A.tp * value (* ?[alpha] *)
       | CloCase of (A.chan * value) list * A.branches * A.chan       (* & *)
       | CloRecv of (A.chan * value) list * (A.chan * A.exp) * A.chan (* -o *)
       | CloRecvNat of (A.chan * value) list * (R.varname * A.exp) * A.chan (* !v *) 
       | CloRecvTp of (A.chan * value) list * (A.tpvarname * A.exp) * A.chan (* ![v] *)

type environment = (A.chan * value) list

exception DynError

structure Print =
struct

fun pp_value env (Lab(k,v)) = k ^ " ; " ^ pp_value env v                  (* k(v) *)
  | pp_value env (Send(w,v)) = "(" ^ pp_value env w ^ ") ; " ^ pp_value env v (* (w,v) *)
  | pp_value env (Close) = "close"                                    (* () *)
  | pp_value env (SendNat(n,v)) =
    if !Flags.verbosity >= 2
    then "{" ^ Int.toString n ^ "} ; " ^ pp_value env v
    else pp_value env v
  | pp_value env (SendTp(A,v)) = "[" ^ PP.pp_tp_compact env A ^ "] ; " ^ pp_value env v
  | pp_value env (CloRecv(eta,(x,P),z)) = "-"     (* closures not observable *)
  | pp_value env (CloCase(eta,branches,z)) = "-"  (* closures not observable *)
  | pp_value env (CloRecvNat(eta,(k,P),z)) = "-"  (* closures not observable *)
  | pp_value env (CloRecvTp(eta,(alpha,P),z)) = "-" (* closures not observable *)

fun pp_eta env [] = "."
  | pp_eta env ((x,v)::eta) = x ^ " = " ^ pp_value env v ^ "\n" ^ pp_eta env eta
                                   
end (* structure Print *)

(*************************)
(* Environment utilities *)
(*************************)

fun lookup ((x,v)::eta) y =
    if x = y then v else lookup eta y

fun update ((x,v)::eta) (y,w) =
    if x = y then (y,w)::eta else (x,v)::update eta (y,w)

fun remove ((x,v)::eta) y =
    if x = y then eta else (x,v)::remove eta y

(* split ys ys' eta1_rev eta = (eta1', eta2)
 * assumes each variable y in ys is defined in eta
 * generates eta1' = v/y' for every such y
 * also returns eta2, the remaining binding from eta
 * eta1_rev is an accumulator argument for eta1'
 *
 * This is used for a call x <- f y1...yn where f is defined
 * with x' <- f y1'...yn' = P
 *)
fun split nil nil eta1_rev eta = (List.rev eta1_rev, eta)
  | split (y::ys) (y'::ys') eta1_rev eta =
    let val v = lookup eta y
        val eta2 = remove eta y
    in split ys ys' ((y',v)::eta1_rev) eta2 end

fun select ((l, _, P)::branches) k =
    if l = k then P else select branches k

fun body env f As es =
    ( case A.lookup_expdef env f
       of SOME(alphas, ctx, (ys', P, x')) =>
          let val theta = ListPair.zipEq (alphas, As)
              val sigma = R.zip ctx es
              val P' = A.subst_exp theta (A.apply_exp sigma P)
          in (ys', P', x') end
        | NONE => raise Fail (f ^ " undefined!!!\n") )

(* eval env eta P z = v, where v the value of [eta]P
 * Requires eta : D and z : C where D |- P :: (z : C)
 * Ensures v : C
 *)
fun eval env eta P z = eval' env eta P z
and eval' env eta (A.Id(x,y)) z = (* x = z *)
    lookup eta y
  | eval' env eta (A.Spawn(P, Q)) z =
    let val eta' = eval_call env eta P
    in eval env eta' Q z end
  | eval' env eta (P as A.ExpName(x,f,As,es,ys)) z = (* x = z *)
    let val [(x',v)] = eval_call env eta P (* x' = x = z *)
    in v end

  | eval' env eta (A.Lab(x, k, P)) z =
    if x = z
    then Lab (k, eval' env eta P z) (* +R *)
    else let val CloCase(eta', branches, z') = lookup eta x (* &L *)
             val v = eval env eta' (select branches k) z'
         in eval env (update eta (x,v)) P z end
  | eval' env eta (A.Case(x, branches)) z =
    if x = z
    then CloCase(eta, branches, z)     (* &R *)
    else let val Lab(k,v) = lookup eta x (* +L *)
             val P = select branches k
         in eval env (update eta (x,v)) P z end

  | eval' env eta (A.Send(x,w,P)) z =
    if x = z
    then Send(lookup eta w, eval env (remove eta w) P z) (* *R *)
    else let val CloRecv(eta', (y,Q), z') = lookup eta x (* -oL *)
             val v = eval env ((y,lookup eta w)::eta') Q z'
         in eval env (remove (update eta (x,v)) w) P z end
  | eval' env eta (A.Recv(x,y,P)) z =
    if x = z
    then CloRecv(eta, (y,P), z) (* -oR *)
    else let val Send(w,v) = lookup eta x (* *L *)
         in eval env ((y,w)::update eta (x,v)) P z end

  | eval' env eta (A.Close(x)) z = Close (* x = z *)
  | eval' env eta (A.Wait(x,P)) z = (* x <> z *)
    let val Close = lookup eta x
     in eval env (remove eta x) P z end

  | eval' env eta (A.Assert(x,phi,P)) z = eval' env eta P z
  | eval' env eta (A.Assume(x,phi,P)) z = eval' env eta P z

  | eval' env eta (A.SendNat(x,e,P)) z =
    if x = z
    then SendNat(R.evaluate e, eval env eta P z) (* ?R *)
    else let val CloRecvNat(eta', (k,Q), z') = lookup eta x (* !L *)
             val n = R.evaluate e
             val Q' = A.apply_exp [(k,R.Int(n))] Q
             val v = eval env eta' Q' z'
         in eval env (update eta (x,v)) P z end
  | eval' env eta (A.RecvNat(x,k,P)) z =
    if x = z
    then CloRecvNat(eta, (k,P), z) (* !R *)
    else let val SendNat(n, v) = lookup eta x (* ?L *)
             val P' = A.apply_exp [(k, R.Int(n))] P
         in eval env (update eta (x,v)) P' z end

  | eval' env eta (A.SendTp(x,A,P)) z =
    if x = z
    then SendTp(A, eval env eta P z)
    else let val CloRecvTp(eta', (alpha,Q), z') = lookup eta x
             val Q' = A.subst_exp [(alpha,A)] Q
             val v = eval env eta' Q' z'
         in eval env (update eta (x,v)) P z end
  | eval' env eta (A.RecvTp(x,alpha,P)) z =
    if x = z
    then CloRecvTp(eta, (alpha,P), z)
    else let val SendTp(A, v) = lookup eta x
             val P' = A.subst_exp [(alpha,A)] P
         in eval env (update eta (x,v)) P' z end

  | eval' env eta (A.Imposs) z = raise DynError
  | eval' env eta (A.Work(q,P)) z = eval' env eta P z
  | eval' env eta (A.Pay(x,q,P)) z = eval' env eta P z
  | eval' env eta (A.Get(x,q,P)) z = eval' env eta P z
  | eval' env eta (A.Delay(t,P)) z = eval' env eta P z
  | eval' env eta (A.Now(x,P)) z = eval' env eta P z
  | eval' env eta (A.When(x,P)) z = eval' env eta P z
    
  | eval' env eta (A.Marked(marked_P)) z =
    eval' env eta (Mark.data marked_P) z
    
and eval_call env eta P = eval_call' env eta P
and eval_call' env eta (A.ExpName(x,f,As,es,ys)) =
    (* lookup f, evaluate body with x,ys substituted *)
    let val (ys', P, x') = body env f As es
        val (eta1', eta2) = split ys ys' nil eta
        val v = eval env eta1' P x'
    in (x,v)::eta2 end

fun evaluate env P z = eval env [] P z

end (* structure Eval *)
