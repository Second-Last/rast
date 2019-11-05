(* Time Reconstruction Utilities *)
(* Shared between the synthesizing and backtracking versions *)

signature TRECON_UTIL =
sig

    val build_cut : Ast.exp -> Ast.pot -> Ast.tp -> Ast.exp -> Ast.exp
    val build_delay : Ast.time -> Ast.exp -> Ast.exp

    val size : Ast.exp -> int

end (* signature TRECON_UTIL *)

structure TReconUtil :> TRECON_UTIL =
struct

structure R = Arith
structure A = Ast

(* build_cut P lpot B Q = PQ where PQ ~ P [|{lpot}- B] Q
 * PQ may be optimized by eliding cuts with identity
 * PQ may have less source extent information than P and Q
 *)
fun build_cut (A.Marked(marked_P)) lpot B Q = build_cut (Mark.data marked_P) lpot B Q
  | build_cut P lpot B (A.Marked(marked_Q)) = build_cut P lpot B (Mark.data marked_Q)
  | build_cut (A.Id) lpot B Q = Q
  | build_cut P lpot B (A.Id) = P
  | build_cut (A.ExpName(f,es)) lpot B Q = (* Q <> A.Id *)
    A.Spawn(A.ExpName(f,es), Q) 
  | build_cut P lpot B Q = A.Cut(P,lpot,B,Q)

(* build_delay s P = P' where P' ~ delay{s} ; P
 * P' may be optimized by combining multiple consecutive delays
 * P' may have less source extent information than P
 *)
fun build_delay s (A.Marked(marked_P)) = build_delay s (Mark.data marked_P)
  | build_delay s (A.Delay(t,P)) = build_delay (R.plus(s,t)) P
  | build_delay s P = A.Delay(s,P)
                      
(* size P = n, the number of constructors in P where cut counts as 2
 * Used to pick the smaller of different reconstructions
 *)
fun size (A.Id) = 1
  | size (A.Cut(P,lpot,B,Q)) = size P + size Q + 2
  | size (A.Spawn(P,Q)) = size P + size Q + 1
  | size (A.ExpName(f,es)) = 1
  (* structural types *)
  | size (A.LabR(k,P)) = size P + 1
  | size (A.CaseL(branches)) = size_branches branches + 1
  | size (A.CaseR(branches)) = size_branches branches + 1
  | size (A.LabL(k,P)) = size P + 1
  | size (A.CloseR) = 1
  | size (A.WaitL(P)) = size P + 1
  (* quantified types *)
  | size (A.AssertR(phi,P)) = size P + 1
  | size (A.AssumeL(phi,P)) = size P + 1
  | size (A.AssumeR(phi,P)) = size P + 1
  | size (A.AssertL(phi,P)) = size P + 1
  | size (A.Imposs) = 1
  (* work *)
  | size (A.Work(p, P)) = size P + 1
  | size (A.PayR(p, P)) = size P + 1
  | size (A.GetL(p, P)) = size P + 1
  | size (A.GetR(p, P)) = size P + 1
  | size (A.PayL(p, P)) = size P + 1
  (* time, after partial reconstruction *)
  | size (A.Delay(t,P)) = size P + 1
  | size (A.NowR(P)) = size P + 1
  | size (A.WhenL(P)) = size P + 1
  | size (A.WhenR(P)) = size P + 1
  | size (A.NowL(P)) = size P + 1
  (* marked expressions *)
  | size (A.Marked(marked_P)) = size (Mark.data marked_P)

and size_branches nil = 0
  | size_branches ((l,ext,P)::branches) =
    size P + size_branches branches

end (* structure TReconUtil *)
