(* Cost Models *)
(* Authors: Frank Pfenning <fp@cs.cmu.edu>
 *          Ankush Das <ankushd@cs.cmu.edu>
 *)

(*
 * Applies several predefined cost models to
 * a process expression by inserting 'work' (for ergometric
 * types) or 'delay' (aka 'tick', for temporal types).
 * These construct may be insert before or after certain
 * actions, and some actions (especially related to work and
 * time analysis itself and index objects we don't expect
 * to be actual runtime operations).
 *)

signature COST =
sig
    (* applying cost models to programs *)
    val apply_cost_model : Ast.exp -> Ast.exp
    
    (* apply work cost model, pre-inserts ticks *)
    val apply_cost_work : Ast.exp -> Ast.exp

    (* apply time cost model, post-inserts delays *)
    val apply_cost_time : Ast.exp -> Ast.exp

end (* signature COST *)

structure Cost :> COST =
struct

structure R = Arith
structure A = Ast

(* insert a tick/delay with each receive operation *)
fun cost_recv f (A.Id(x,y)) = A.Id(x,y)
  | cost_recv f (A.Spawn(P,Q)) = A.Spawn(cost_recv f P, cost_recv f Q)
  | cost_recv f (A.ExpName(x,g,es,xs)) = A.ExpName(x,g,es,xs)

  | cost_recv f (A.Lab(x,k,P)) = A.Lab(x,k, cost_recv f P)
  | cost_recv f (A.Case(x,branches)) = A.Case(x,cost_recv_branches f branches)

  | cost_recv f (A.Send(x,w,P)) = A.Send(x,w, cost_recv f P)
  | cost_recv f (A.Recv(x,y,Q)) = A.Recv(x,y, f (cost_recv f Q))

  | cost_recv f (A.Close(x)) = A.Close(x)
  | cost_recv f (A.Wait(x,P)) = A.Wait(x,f(cost_recv f P))

  | cost_recv f (A.Assert(x,phi,P)) = A.Assert(x,phi,cost_recv f P)
  | cost_recv f (A.Assume(x,phi,P)) = A.Assume(x,phi,cost_recv f P)
  | cost_recv f (A.SendNat(x,e,P)) = A.SendNat(x,e,cost_recv f P) (* free *)
  | cost_recv f (A.RecvNat(x,v,P)) = A.RecvNat(x,v,cost_recv f P) (* free *)

  | cost_recv f (A.Imposs) = A.Imposs

  | cost_recv f (A.Work(p,P)) = A.Work(p,cost_recv f P)
  | cost_recv f (A.Pay(x,p,P)) = A.Pay(x,p,cost_recv f P)
  | cost_recv f (A.Get(x,p,P)) = A.Get(x,p,cost_recv f P)

  | cost_recv f (A.Delay(t,P)) = A.Delay(t,cost_recv f P)  (* allow in source *)
  | cost_recv f (A.When(x,P)) = A.When(x,cost_recv f P)
  | cost_recv f (A.Now(x,P)) = A.Now(x,cost_recv f P)

  | cost_recv f (A.Marked(marked_P)) =
    A.Marked(Mark.mark'(cost_recv f (Mark.data marked_P), Mark.ext marked_P))
and cost_recv_branches f nil = nil
  | cost_recv_branches f ((l,ext,P)::branches) =
    (l,ext,f(cost_recv f P))::cost_recv_branches f branches

(* insert before/after operation *)
datatype Sequence = Before | After

(* insert a tick/delay with each send operation *)
fun cost_send sf (A.Id(x,y)) = A.Id(x,y)
  | cost_send sf (A.Spawn(P,Q)) = A.Spawn(cost_send sf P, cost_send sf Q)
  | cost_send sf (A.ExpName(x,f,es,xs)) = A.ExpName(x,f,es,xs)

  | cost_send (After,f) (A.Lab(x,k,P)) = A.Lab(x,k, f(cost_send (After,f) P))
  | cost_send (Before,f) (A.Lab(x,k,P)) = f(A.Lab(x,k, cost_send (Before,f) P))
  | cost_send sf (A.Case(x,branches)) = A.Case(x,cost_send_branches sf branches)

  | cost_send (After,f) (A.Send(x,w,P)) = A.Send(x,w, f (cost_send (After,f) P))
  | cost_send (Before,f) (A.Send(x,w,P)) = f (A.Send(x,w, cost_send (Before,f) P))
  | cost_send sf (A.Recv(x,y,Q)) = A.Recv(x,y, cost_send sf Q)

  | cost_send (After,f) (A.Close(x)) = A.Close(x) (* no continuation here to delay *)
  | cost_send (Before,f) (A.Close(x)) = f(A.Close(x))
  | cost_send sf (A.Wait(x,P)) = A.Wait(x,cost_send sf P)

  | cost_send sf (A.Assert(x,phi,P)) = A.Assert(x,phi,cost_send sf P)
  | cost_send sf (A.Assume(x,phi,P)) = A.Assume(x,phi,cost_send sf P)
  | cost_send sf (A.SendNat(x,e,P)) = A.SendNat(x,e,cost_send sf P) (* free *)
  | cost_send sf (A.RecvNat(x,v,P)) = A.RecvNat(x,v,cost_send sf P) (* free *)
  | cost_send sf (A.Imposs) = A.Imposs

  | cost_send sf (A.Work(p,P)) = A.Work(p,cost_send sf P)   (* allow in source *)
  | cost_send sf (A.Pay(x,p,P)) = A.Pay(x,p,cost_send sf P)
  | cost_send sf (A.Get(x,p,P)) = A.Get(x,p,cost_send sf P)

  | cost_send sf (A.Delay(t,P)) = A.Delay(t,cost_send sf P)  (* allow in source *)
  | cost_send sf (A.Now(x,P)) = A.Now(x,cost_send sf P)
  | cost_send sf (A.When(x,P)) = A.When(x,cost_send sf P)

  | cost_send sf (A.Marked(marked_P)) =
    A.Marked(Mark.mark'(cost_send sf (Mark.data marked_P), Mark.ext marked_P))
and cost_send_branches sf nil = nil
  | cost_send_branches sf ((l,ext,P)::branches) =
    (l,ext,cost_send sf P)::cost_send_branches sf branches

(* applying cost models *)
(* sf => before/after and quantity *)
(* Flags => operation: recv/recvsend/send/none *)
(* P => program *)
fun cost_model sf (Flags.None) P = P
  | cost_model sf (Flags.Free) P = P
  | cost_model (_,f) (Flags.Recv) P = cost_recv f P
  | cost_model (sf as (_,f)) (Flags.RecvSend) P = cost_send sf (cost_recv f P)
  | cost_model sf (Flags.Send) P = cost_send sf P

fun apply_cost_model P =
    let val P = cost_model (After, fn k => A.Delay(R.Int(1),k)) (!Flags.time) P
        val P = cost_model (Before, fn k => A.Work(R.Int(1),k)) (!Flags.work) P
    in
        P
    end 

fun apply_cost_work P = cost_model (Before, fn k => A.Work(R.Int(1),k)) (!Flags.work) P
fun apply_cost_time P = cost_model (After, fn k => A.Delay(R.Int(1),k)) (!Flags.time) P

end (* structure Cost *)
