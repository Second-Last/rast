signature COST =
sig

    val apply_cost_model : Ast.exp -> Ast.exp
    val apply_cost_work : Ast.exp -> Ast.exp
    val apply_cost_time : Ast.exp -> Ast.exp

end (* signature COST *)

structure Cost :> COST =
struct

structure R = Arith
structure A = Ast

fun cost_recv f (A.Id) = A.Id
  | cost_recv f (A.Cut(P,pot,A,Q)) = A.Cut(cost_recv f P, pot, A, cost_recv f Q)
  | cost_recv f (A.Spawn(P,Q)) = A.Spawn(cost_recv f P, cost_recv f Q)
  | cost_recv f (A.ExpName(g,es)) = A.ExpName(g,es)

  | cost_recv f (A.LabR(k,P)) = A.LabR(k, cost_recv f P)
  | cost_recv f (A.CaseL(branches)) = A.CaseL(cost_recv_branches f branches)

  | cost_recv f (A.CaseR(branches)) = A.CaseR(cost_recv_branches f branches)
  | cost_recv f (A.LabL(k,P)) = A.LabL(k, cost_recv f P)

  | cost_recv f (A.CloseR) = A.CloseR
  | cost_recv f (A.WaitL(P)) = A.WaitL(f(cost_recv f P))

  | cost_recv f (A.AssertR(phi,P)) = A.AssertR(phi,cost_recv f P)
  | cost_recv f (A.AssumeL(phi,P)) = A.AssumeL(phi,cost_recv f P)
  | cost_recv f (A.AssumeR(phi,P)) = A.AssumeR(phi,cost_recv f P)
  | cost_recv f (A.AssertL(phi,P)) = A.AssertL(phi,cost_recv f P)

  | cost_recv f (A.Imposs) = A.Imposs

  | cost_recv f (A.Work(p,P)) = A.Work(p,cost_recv f P)
  | cost_recv f (A.PayR(p,P)) = A.PayR(p,cost_recv f P)
  | cost_recv f (A.GetL(p,P)) = A.GetL(p,cost_recv f P)
  | cost_recv f (A.GetR(p,P)) = A.GetR(p,cost_recv f P)
  | cost_recv f (A.PayL(p,P)) = A.PayL(p,cost_recv f P)

  | cost_recv f (A.Delay(t,P)) = A.Delay(t,cost_recv f P)  (* allow in source *)
  | cost_recv f (A.WhenR(P)) = A.WhenR(cost_recv f P)
  | cost_recv f (A.NowL(P)) = A.NowL(cost_recv f P)
  | cost_recv f (A.WhenL(P)) = A.WhenL(cost_recv f P)
  | cost_recv f (A.NowR(P)) = A.NowR(cost_recv f P)

  | cost_recv f (A.Marked(marked_P)) =
    A.Marked(Mark.mark'(cost_recv f (Mark.data marked_P), Mark.ext marked_P))
and cost_recv_branches f nil = nil
  | cost_recv_branches f ((l,ext,P)::branches) =
    (l,ext,f(cost_recv f P))::cost_recv_branches f branches

datatype Sequence = Before | After

fun cost_send sf (A.Id) = A.Id
  | cost_send sf (A.Cut(P,pot,A,Q)) = A.Cut(cost_send sf P, pot, A, cost_send sf Q)
  | cost_send sf (A.Spawn(P,Q)) = A.Spawn(cost_send sf P, cost_send sf Q)
  | cost_send sf (A.ExpName(f,es)) = A.ExpName(f,es)

  | cost_send (After,f) (A.LabR(k,P)) = A.LabR(k, f(cost_send (After,f) P))
  | cost_send (Before,f) (A.LabR(k,P)) = f(A.LabR(k, cost_send (Before,f) P))
  | cost_send sf (A.CaseL(branches)) = A.CaseL(cost_send_branches sf branches)

  | cost_send sf (A.CaseR(branches)) = A.CaseR(cost_send_branches sf branches)
  | cost_send (After,f) (A.LabL(k,P)) = A.LabL(k, f(cost_send (After,f) P))
  | cost_send (Before,f) (A.LabL(k,P)) = f(A.LabL(k, cost_send (Before, f) P))

  | cost_send (After,f) (A.CloseR) = A.CloseR (* no continuation here to delay *)
  | cost_send (Before,f) (A.CloseR) = f(A.CloseR)
  | cost_send sf (A.WaitL(P)) = A.WaitL(cost_send sf P)

  | cost_send sf (A.AssertR(phi,P)) = A.AssertR(phi,cost_send sf P)
  | cost_send sf (A.AssumeL(phi,P)) = A.AssumeL(phi,cost_send sf P)
  | cost_send sf (A.AssumeR(phi,P)) = A.AssumeR(phi,cost_send sf P)
  | cost_send sf (A.AssertL(phi,P)) = A.AssertL(phi,cost_send sf P)
  | cost_send sf (A.Imposs) = A.Imposs

  | cost_send sf (A.Work(p,P)) = A.Work(p,cost_send sf P)   (* allow in source *)
  | cost_send sf (A.PayR(p,P)) = A.PayR(p,cost_send sf P)
  | cost_send sf (A.GetL(p,P)) = A.GetL(p,cost_send sf P)
  | cost_send sf (A.GetR(p,P)) = A.GetR(p,cost_send sf P)
  | cost_send sf (A.PayL(p,P)) = A.PayL(p,cost_send sf P)

  | cost_send sf (A.Delay(t,P)) = A.Delay(t,cost_send sf P)  (* allow in source *)
  | cost_send sf (A.NowR(P)) = A.NowR(cost_send sf P)
  | cost_send sf (A.WhenL(P)) = A.WhenL(cost_send sf P)
  | cost_send sf (A.WhenR(P)) = A.WhenR(cost_send sf P)
  | cost_send sf (A.NowL(P)) = A.NowL(cost_send sf P)

  | cost_send sf (A.Marked(marked_P)) =
    A.Marked(Mark.mark'(cost_send sf (Mark.data marked_P), Mark.ext marked_P))
and cost_send_branches sf nil = nil
  | cost_send_branches sf ((l,ext,P)::branches) =
    (l,ext,cost_send sf P)::cost_send_branches sf branches

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
