(* Evaluation *)

signature EVAL =
sig
    type value
    val evaluate : Ast.env -> Ast.exp -> Ast.chan -> value

    structure Print :
    sig
        val pp_value : value -> string
    end
end

structure Eval :> EVAL =
struct

structure A = Ast
structure PP = PPrint
val ERROR = ErrorMsg.ERROR

datatype value =
         Lab of A.label * value (* + *)
       | Send of value * value  (* * *)
       | Close                  (* 1 *)
       | CloRecv of (A.chan * value) list * (A.chan * A.exp) * A.chan (* -o *)
       | CloCase of (A.chan * value) list * A.branches * A.chan (* & *)

type environment = (A.chan * value) list

structure Print =
struct

fun pp_value (Lab(k,v)) = k ^ " ; " ^ pp_value v  (* k(v) *)
  | pp_value (Send(w,v)) = "(" ^ pp_value w ^ ") ; " ^ pp_value v (* (w,v) *)
  | pp_value (Close) = "close"  (* () *)
  | pp_value (CloRecv(eta,(x,P),z)) = "-"
  | pp_value (CloCase(eta,branches,z)) = "-"

fun pp_eta [] = "."
  | pp_eta ((x,v)::eta) = x ^ " = " ^ pp_value v ^ "\n" ^ pp_eta eta
                                   
end (* structure Print *)

fun lookup ((x,v)::eta) y =
    if x = y then v else lookup eta y
fun update ((x,v)::eta) (y,w) =
    if x = y then (y,w)::eta else (x,v)::update eta (y,w)
fun remove ((x,v)::eta) y =
    if x = y then eta else (x,v)::remove eta y
fun split nil nil eta1_rev eta = (List.rev eta1_rev, eta)
  | split (y::ys) (y'::ys') eta1_rev eta =
    let val v = lookup eta y
        val eta2 = remove eta y
    in split ys ys' ((y',v)::eta1_rev) eta2 end

fun select ((l, _, P)::branches) k =
    if l = k then P else select branches k

fun body env f =
    ( case A.lookup_expdef env f
       of SOME(ctx, (ys', P, x')) => (ys', P, x') )

fun eval env eta P z =
    eval' env eta P z
and eval' env eta (A.Id(x,y)) z = (* x = z *)
    lookup eta y
  | eval' env eta (A.Spawn(P, Q)) z =
    let val eta' = eval_call env eta P
    in eval env eta' Q z end
  | eval' env eta (P as A.ExpName(x,f,es,ys)) z = (* x = z *)
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
    
  | eval' env eta (A.Marked(marked_P)) z =
    eval' env eta (Mark.data marked_P) z
    

and eval_call env eta P =
    eval_call' env eta P
and eval_call' env eta (A.ExpName(x,f,es,ys)) =
    (* lookup f, evaluate body with x,ys substituted *)
    let val (ys', P, x') = body env f
        val (eta1', eta2) = split ys ys' nil eta
        val v = eval env eta1' P x'
    in (x,v)::eta2 end

fun evaluate env P z = eval env [] P z

end (* structure Eval *)
