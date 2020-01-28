(* Time Reconstruction, backtracking version *)
(* At present only for constant times *)
(* Unlike quantifier and work reconstruction this allows
 * insertion of identity coercions before spawns, following
 * the rules of the ICFP'18 paper
 *)

(* This version backtracks and therefore provides no
 * particularly useful error message.  It also returns the first
 * reconstruction, without comparing multiple reconstructions
 *)

structure TReconBT :> RECON =
struct

structure R = Arith
structure A = Ast
structure PP = PPrint
structure C = Constraints
structure TC = TypeCheck
structure TRU = TReconUtil
val ERROR = ErrorMsg.ERROR

fun strip_next0 env ctx con (A as A.Next(t,A')) =
    if C.entails ctx con (R.Eq(t,R.Int(0)))
    then strip_next0 env ctx con A'
    else A
  | strip_next0 env ctx con (A.TpName(a,es)) =
    strip_next0 env ctx con (A.expd_tp env (a,es))
  | strip_next0 env ctx con A = A

(* If digging right or left or right/left (subtyping):
 * Next/Next, DiaL, BoxR are invertible
 * Box/Next, BoxL are alternatives
 * Next/Dia, DiaR are alternatives
 *
 * Do we need to try BoxL if right is structural (digging right)?
 * Do we need to try DiaR if left is structural (digging left)?
 * Guess is not, because the rule can still be applied after the right rule
 * Attention if the left-hand side is empty
 *)                    

(*************)
(* Utilities *)
(*************)

val one = R.Int(1)
val zero = R.Int(0)

fun delay1 P = TRU.build_delay one P

fun dec1 (A.Next(R.Int(1),A)) = A
  | dec1 (A.Next(t,A)) = A.Next(R.minus(t,one),A)

(* decL env ctx con A ext = SOME([A]_L^-1) if defined, NONE o.w. *)
(* assumes A is stripped and will strip but not expand the result *)
fun decL env ctx con (A.Next(t,A)) ext =
    let val t' = R.minus(t,one)
        val is_zero = C.entails ctx con (R.Eq(t',zero))
    in if is_zero then SOME(A) else SOME(A.Next(t',A)) end
  | decL env ctx con (A.Box(A)) ext = SOME(A.Box(A))
  | decL env ctx con (A.TpName(a,es)) ext = decL env ctx con (A.expd_tp env (a,es)) ext
  | decL env ctx con (A.Dot) ext = SOME(A.Dot)
  | decL env ctx con _ ext = NONE

(* decR env ctx con A ext = SOME([A]_R^-1) if defined, NONE o.w. *)
(* assumes A is stripped and will strip but not expand the result *)
fun decR env ctx con (A.Next(t,A)) ext =
    let val t' = R.minus(t,one)
        val is_zero = C.entails ctx con (R.Eq(t',zero))
    in if is_zero then SOME(A) else SOME(A.Next(t',A)) end
  | decR env ctx con (A.Dia(A)) ext = SOME(A.Dia(A))
  | decR env ctx con (A.TpName(a,es)) ext = decL env ctx con (A.expd_tp env (a,es)) ext
  | decR env ctx con _ ext = NONE

(*********************)
(* Typing Statistics *)
(*********************)

local
    val calls = ref 0
    val backtracks = ref 0
in
fun stat_reset () = ( calls := 0 ; backtracks := 0 )
fun stat_call () = ( calls := !calls+1 )
fun stat_backtrack () = ( backtracks := !backtracks+1 )
fun stat_print () = "% calls: " ^ Int.toString (!calls)
                    ^ ", backtracked: " ^ Int.toString (!backtracks)
end

(******************)
(* Explicit Rules *)
(******************)

(*
 * We try the explicit rules first, followed by attempting
 * the implicit ones if they fail.  The implicit ones are
 * tried in a fixed order which I believe to be complete.
 *)

(* trecon env ctx con A P C sc fc ext
 *   = sc P'   if A |- P ~> P' : C for some P'
 *   = fc ()   if there is no such P'
 *
 * sc : exp -> 'a  is the success continuation, called with the reconstruction of P
 * fc : unit -> 'a is the failure continuation, if no reconstruction of P is possible
 *)
fun trecon env ctx con A P C sc fc ext =
    let
        val () = stat_call ()
        val A' = strip_next0 env ctx con A
        val C' = strip_next0 env ctx con C
    in
        trecon' env ctx con A' P C' sc fc ext
    end

(* trecon' env ctx con A P C sc fc ext
 * see trecon above, except A and C must be stripped
 *)
and (* judgmental constructs: id, cut spawn, call *)
    trecon' env ctx con A (P as A.Id) C sc fc ext =
    if TC.eq_tp env ctx con A C
    then sc P
    else next_next env ctx con A P C sc fc ext

  | trecon' env ctx con A (PQ as A.Cut(P,lpot,B,Q)) C sc fc ext =
    (* Q: should we try the explicit rules first? *)
    next_next env ctx con A PQ C sc (* try implicit rules *)
              (fn () => trecon env ctx con A P B (fn P' => (* if all fail, reconstruct structurally *)
                              trecon env ctx con B Q C (fn Q' =>
                                     sc (TRU.build_cut P' lpot B Q')) fc ext) fc ext) ext
  | trecon' env ctx con A (PQ as A.Spawn(P,Q)) C sc fc ext =
    (* Q: should we try the explicit rules first? *)
    (* for spawn f || Q, possibly insert coercion <-> || (f || Q')
     * for A to match the left-hand type of f *)
    next_next env ctx con A PQ C sc (* try implicit rules *)
              (fn () => case TC.syn_call env P ext (* no error here, due to approx typing invariant *)
                         of (A.Dot, lpot, P_expd, B) => (* A = A.Dot by approximate typing *)
                            trecon env ctx con B Q C (fn Q' =>  (* cannot insert A.Id if context empty *)
                                  sc (A.Spawn(P,Q'))) fc ext
                          | (A', lpot, P_expd, B) => (* A' <> A.Dot *)
                            trecon env ctx con A (A.Id) A' (fn I =>  (* A |- I : A' that is I : A <: A' *)
                                  trecon env ctx con B Q C (fn Q' =>
                                        sc (TRU.build_cut (TRU.build_cut I (R.Int(0)) A' P) lpot B Q')) fc ext) fc ext) ext
  | trecon' env ctx con A (P as A.ExpName _) C sc fc ext =
    (* expand call f == f || <-> *)
    trecon' env ctx con A (A.Spawn(P, A.Id)) C sc fc ext

  (* structural types +{...}, &{...}, 1 *)
  | trecon' env ctx con A (A.LabR(k,P)) (A.Plus(choices)) sc fc ext =
    trecon env ctx con A P (TC.syn_alt env choices k) (fn P' => sc (A.LabR(k,P'))) fc ext (* no backtracking *)
  | trecon' env ctx con (A.Plus(choices)) (A.CaseL(branches)) C sc fc ext =
    trecon_branchesL env ctx con choices branches C (fn branches' => sc (A.CaseL(branches'))) fc ext (* no backtracking *)

  | trecon' env ctx con A (A.CaseR(branches)) (A.With(choices)) sc fc ext =
    trecon_branchesR env ctx con A branches choices (fn branches' => sc (A.CaseR(branches'))) fc ext (* no bt *)
  | trecon' env ctx con (A.With(choices)) (A.LabL(k,P)) C sc fc ext =
    trecon env ctx con (TC.syn_alt env choices k) P C (fn P' => sc (A.LabL(k,P'))) fc ext

  | trecon' env ctx con (A.Dot) (P as A.CloseR) (A.One) sc fc ext = sc P
  | trecon' env ctx con (A.One) (A.WaitL(P)) C sc fc ext =
    trecon env ctx con (A.Dot) P C (fn P' => sc (A.WaitL(P'))) fc ext

  (* quantified types ?{phi}.A, !{phi}.A *)
  | trecon' env ctx con A (A.AssertR(phi,P)) (A.Exists(phi',C)) sc fc ext =
    trecon env ctx (R.And(con,phi')) A P C (fn P' => sc (A.AssertR(phi,P'))) fc ext (* or phi? *)
  | trecon' env ctx con (A.Exists(phi',A)) (A.AssumeL(phi,P)) C sc fc ext =
    trecon env ctx (R.And(con,phi')) A P C (fn P' => sc (A.AssumeL(phi,P'))) fc ext

  | trecon' env ctx con A (A.AssumeR(phi,P)) (A.Forall(phi',C)) sc fc ext =
    trecon env ctx (R.And(con,phi')) A P C (fn P' => sc (A.AssumeR(phi,P'))) fc ext
  | trecon' env ctx con (A.Forall(phi',A)) (A.AssertL(phi,P)) C sc fc ext =
    trecon env ctx (R.And(con,phi')) A P C (fn P' => sc (A.AssertL(phi,P'))) fc ext

  | trecon' env ctx con A (P as A.Imposs) C sc fc ext = sc P

  (* ergometric types *)
  | trecon' env ctx con A (A.Work(p,P)) C sc fc ext =
    trecon env ctx con A P C sc fc ext
  | trecon' env ctx con A (A.PayR(p,P)) (A.PayPot(p',C)) sc fc ext =
    trecon env ctx con A P C (fn P' => sc (A.PayR(p,P'))) fc ext
  | trecon' env ctx con (A.PayPot(p',A)) (A.GetL(p,P)) C sc fc ext =
    trecon env ctx con A P C (fn P' => sc (A.GetL(p,P'))) fc ext
  | trecon' env ctx con A (A.GetR(p,P)) (A.GetPot(p',C)) sc fc ext =
    trecon env ctx con A P C (fn P' => sc (A.GetR(p,P'))) fc ext
  | trecon' env ctx con (A.GetPot(p',A)) (A.PayL(p,P)) C sc fc ext =
    trecon env ctx con A P C (fn P' => sc (A.PayL(p,P'))) fc ext

  (* temporal types: only explicit Delay is allowed *)
  (* Q: do we need to try implicit rules here or not? *)
  | trecon' env ctx con A (A.Delay(t,P)) C sc fc ext =
    (case (decL env ctx con A t, decR env ctx con C t)
      of (SOME(A'), SOME(C')) => trecon env ctx con A' P C' (fn P' => sc (TRU.build_delay t P')) fc ext
       | _ => fc ()             (* backtrack *)
    )
  (* other temporal operators are impossible *)

  | trecon' env ctx con A (A.Marked(marked_P)) C sc fc ext =
    trecon env ctx con A (Mark.data marked_P) C (fn P' =>
          sc (A.Marked(Mark.mark'(P', Mark.ext marked_P)))) fc ext
           
  | trecon' env ctx con A P C sc fc ext =
    (* try implicit rules, at the end of which we backtrack *)
    next_next env ctx con A P C sc fc ext

and trecon_branchesL env ctx con nil nil C sc fc ext = sc nil
  | trecon_branchesL env ctx con ((l,A)::choices) ((l',ext',P)::branches) C sc fc ext =
    (* invariant l = l', by approximate typing *)
    trecon env ctx con A P C (fn P' =>
          trecon_branchesL env ctx con choices branches C (fn branches' =>
                          sc ((l',ext',P')::branches')) fc ext) fc ext

and trecon_branchesR env ctx con A nil nil sc fc ext = sc nil
  | trecon_branchesR env ctx con A ((l',ext',P)::branches) ((l,C)::choices) sc fc ext =
    (* invariant l = l', by approximate typing *)
    trecon env ctx con A P C (fn P' =>
          trecon_branchesR env ctx con A branches choices (fn branches' =>
                          sc ((l',ext',P')::branches')) fc ext) fc ext

(******************)
(* Implicit Rules *)
(******************)
    
(*
 * Order in which implicit rules are tried:
 * First, invertible ones: ()(), <>L, []R
 * Second, noninvertible ones: [](), ()<>, []L, <>R
 * Fail if none of them succeed
 *)

(*
 * Some small(?) optimization looks possible.  For example,
 * when interacting on the right, don't try boxL because it can always
 * be postponed.  Similarly for diaR when interacting on the left
 *)

(* next/next is invertible for P = Id or if P is a structural interaction *)
(* However, it is NOT invertible if P is a cut or spawn! *)
and next_next env ctx con A P C sc fc ext =
    (* room for statistics or debugging *)
    next_next' env ctx con A P C sc fc ext

and next_next' env ctx con (A as A.Next(s,A')) P (C as A.Next(t,C')) sc fc ext =
    trecon env ctx con (dec1 A) P (dec1 C) (fn P' => sc (delay1 P')) fc ext (* no backtracking *)
  | next_next' env ctx con (A.Dot) P (C as A.Next(t,C')) sc fc ext =
    trecon env ctx con (A.Dot) P (dec1 C) (fn P' => sc (delay1 P')) fc ext (* no backtracking *)
  | next_next' env ctx con A P C sc fc ext =
    diaL env ctx con A P C sc fc ext

(* diaL is invertible *)
and diaL env ctx con (A as A.Dia(A')) P C sc fc ext =
    if TC.eventually_dia env C
    then trecon env ctx con A' P C (fn P' => sc (A.WhenL P')) fc ext (* no backtracking *)
    else boxR env ctx con A P C sc fc ext
  | diaL env ctx con A P C sc fc ext =
    boxR env ctx con A P C sc fc ext

(* boxR is invertible *)
and boxR env ctx con A P (C as A.Box(C')) sc fc ext =
    if TC.eventually_box env A
    then trecon env ctx con A P C' (fn P' => sc (A.WhenR P')) fc ext (* no backtracking *)
    else box_next env ctx con A P C sc fc ext
  | boxR env ctx con A P C sc fc ext =
    box_next env ctx con A P C sc fc ext

(* box_next is not invertible *)
and box_next env ctx con (A as A.Box(A')) P (C as A.Next(t,C')) sc fc ext =
    trecon env ctx con A P (dec1 C) (fn P' => sc (delay1 P'))
           (fn () => boxL env ctx con A P C sc fc ext) ext (* backtrack to boxL because next_dia will fail *)
  | box_next env ctx con A P C sc fc ext =
    next_dia env ctx con A P C sc fc ext

(* next_dia is not invertible *)
and next_dia env ctx con (A as A.Next(s,A')) P (C as A.Dia(C')) sc fc ext =
    trecon env ctx con (dec1 A) P C (fn P' => sc (delay1 P'))
           (fn () => diaR env ctx con A P C sc fc ext) ext (* backtrack to diaR because boxL definitely fails *)
  | next_dia env ctx con A P C sc fc ext =
    boxL env ctx con A P C sc fc ext

(* boxL is not invertible *)
and boxL env ctx con (A as A.Box(A')) P C sc fc ext =
    trecon env ctx con A' P C (fn P' => sc (A.NowL(P')))
           (fn () => diaR env ctx con A P C sc fc ext) ext
  | boxL env ctx con A P C sc fc ext =
    diaR env ctx con A P C sc fc ext

(* diaR is not invertible *)
and diaR env ctx con A P (C as A.Dia(C')) sc fc ext =
    (* last possibility: backtrack from it by calling fc *)
    trecon env ctx con A P C' (fn P' => sc (A.NowR(P'))) fc ext
  | diaR env ctx con A P C sc fc ext =
    (* does not match any pattern *)
    (* backtrack by calling failure continuation *)
    ( stat_backtrack () ; fc () )

fun recon env ctx con A pot P C ext =
    let
        val () = stat_reset ()
        val fc_error = fn () => ERROR ext "backtracking checker failed"
        val P' = trecon env ctx con A P C (fn P' => P') fc_error ext
        val () = if !Flags.verbosity >= 2
                 then TextIO.print ("% backtracking time reconstruction succeeded\n")
                 else ()
        val () = if !Flags.verbosity >= 2
                 then TextIO.print ("% source expression of size " ^ Int.toString (TRU.size P) ^ "\n"
                                    ^ "% reconstructed exp of size " ^ Int.toString (TRU.size P') ^ "\n"
                                    ^ stat_print () ^ "\n")
                 else ()
    in
        P'
    end

end (* structure TReconBT *)
