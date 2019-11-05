(* Time and Quantifier Reconstruction *)
(* At present only for constant times *)
(* Allows insertion of identity coercion
 * before spawns, following the rules of the ICFP'18 paper,
 * augmented with similarly implicit rules for the quantifiers.
 * This combined reconstruction is necessary due to some
 * incompleteness of the phases are done separately.  The
 * files tests/tqrecon*.ss show examples of the incompleteness
 * in detail.
 *)

(* This version synthesizes typings bottom up,
 * raises an error for the first subexpression encountered
 * that has no legal typing
 *)

(* TODO: stop upward propagation and filter out possibilities
 * if constraints are insufficient? see tests/errmsg.ss
 * Assume we start with constraints con and retain the
 * invariant that con |= con' for every typing con' ; A |- P : C
 * we synthesize, where exactly does unsatisfiability arise?
 * Note the independence of the constraints from left and right...
 *)

structure TQRecon :> RECON =
struct

structure R = Arith
structure A = Ast
structure PP = PPrint
structure C = Constraints
structure E = TpError
structure TC = TypeCheck
structure TRU = TReconUtil
val ERROR = ErrorMsg.ERROR

(**************************)
(* Program Simplification *)
(**************************)

(* Temporal modalities, without continuation type
 * These are pushed onto a stack to act as a "bound"
 * to enforce the subformula property for applying inference
 * rules in the forward direction
 *)
datatype temporal = Circle of R.arith (* (t), t > 0 *)
                  | Eventual          (* <> *)
                  | Always            (* [] *)
                  | Some of R.prop    (* ?{phi} *)
                  | All of R.prop     (* !{phi} *)

fun pp_stack nil = "."
  | pp_stack (Circle(t)::st) = pp_stack st ^ "(" ^ PP.pp_time t ^ ")"
  | pp_stack (Eventual::st) = pp_stack st ^ "<>"
  | pp_stack (Always::st) = pp_stack st ^ "[]"
  | pp_stack (Some(phi)::st) = pp_stack st ^ "?" ^ PP.pp_con phi
  | pp_stack (All(phi)::st) = pp_stack st ^ "!" ^ PP.pp_con phi

(* eq_stack st st' = true if st = st'
 * requires they are both postfixes of a common initial stack st0
 * Next-time operators are broken down one by one, so stacks have
 * a common prefix only modulo (n+1) = ()(n).  All numbers
 * are constants, so we can compare them directly.
 *)
fun eq_stack (Circle(R.Int(0))::st) st' = eq_stack st st' (* may be redundant *)
  | eq_stack st (Circle(R.Int(0))::st') = eq_stack st st' (* may be redundant *)
  | eq_stack (Circle(R.Int(s))::st) (Circle(R.Int(t))::st') =
    if s = t then eq_stack st st'
    else if s < t then eq_stack st (Circle(R.Int(t-s))::st')
    else (* s > t *) eq_stack (Circle(R.Int(s-t))::st) st'
  | eq_stack (Eventual::st) (Eventual::st') = eq_stack st st'
  | eq_stack (Always::st) (Always::st') = eq_stack st st'
  | eq_stack (Some(phi)::st) (Some(phi')::st') = eq_stack st st' (* phi = phi', by postfix invariant *)
  | eq_stack (All(phi)::st) (All(phi')::st') = eq_stack st st' (* phi = phi', by postfix invariant *)
  | eq_stack nil nil = true
  | eq_stack _ _ = false

(* Tpj(ctx, con, stA, A, P, C, stC) represents the
 * typing judgment ctx ; con ; A |- P : C
 * where stA | A and stC | C are subformulas
 *)
datatype tpj = Tpj of R.ctx * R.prop * temporal list * A.tp * A.exp * A.tp * temporal list

datatype direction = Left | Right

(* extract env ctx con dir A st = (ctx', con', st', A')
 * where st' is the stack of temporal modalities and quantifiers
 * at the beginning of A pushed onto st.  ctx' = ctx and
 * con' are the constraints we can assume if A is on the Left or
 * Right, according to direction dir.
 *)
fun extract env ctx con dir (A as A.Next(t,A')) st =
    ((case R.evaluate t
      of 0 => extract env ctx con dir A' st
       | n => extract env ctx con dir A' (Circle(R.Int(n))::st))
     handle R.NotClosed => ERROR NONE
                                 ("Illegal type: " ^ PP.pp_tp_compact env A ^ "\n"
                                  ^ "time reconstruction supports only constant time; use explicit syntax"))
  | extract env ctx con dir (A.Dia(A')) st = extract env ctx con dir A' (Eventual::st)
  | extract env ctx con dir (A.Box(A')) st = extract env ctx con dir A' (Always::st)
  | extract env ctx con Right (A.Exists(phi,A')) st = extract env ctx con Right A' (Some(phi)::st)
  | extract env ctx con Left (A.Exists(phi,A')) st = extract env ctx (R.And(con,phi)) Left A' (Some(phi)::st)
  | extract env ctx con Right (A.Forall(phi,A')) st = extract env ctx (R.And(con,phi)) Right A' (All(phi)::st)
  | extract env ctx con Left (A.Forall(phi,A')) st = extract env ctx con Left A' (All(phi)::st)
  | extract env ctx con dir (A.TpName(a,es)) st = extract env ctx con dir (A.expd_tp env (a,es)) st
  | extract env ctx con dir A st = (ctx,con,st,A)

(* restore st A = st | A *)
fun restore (Circle(t)::st) A = restore st (A.Next(t,A))
  | restore (Eventual::st) A = restore st (A.Dia(A))
  | restore (Always::st) A = restore st (A.Box(A))
  | restore (Some(phi)::st) A = restore st (A.Exists(phi,A))
  | restore (All(phi)::st) A = restore st (A.Forall(phi,A))
  | restore (nil) A = A

(* restore1 (op::st) A = (st, op(A)) *)
fun restore1 (Circle(t)::st) A = (st, A.Next(t,A))
  | restore1 (Eventual::st) A = (st, A.Dia(A))
  | restore1 (Always::st) A = (st, A.Box(A))
  | restore1 (Some(phi)::st) A = (st, A.Exists(phi,A))
  | restore1 (All(phi)::st) A = (st, A.Forall(phi,A))

val one = R.Int(1)

(* subone stA = stA', subtracting 1 from the Next-time modality
 * at the top of operator stack stA.  Assumes stA starts with
 * Next-time operator Circle(t).
 *)
fun subone (Circle(R.Int(1))::st) = st
  | subone (Circle(t)::st) = Circle(R.minus(t,one))::st

fun delay1 P = TRU.build_delay one P

(* Functions to apply inference rules from the premise to
 * conclusion, when applicable, returning a list of possible
 * typings.  A typing is a tuple (stA, A, P, B, stB) such
 * that A |- P : B and stA|A, stB|B are both valid subformulas
 * of the typing of B based on the subformula property of the
 * typing rules.
 *
 * For each function 'rule':
 *
 * rule env ctx con stA A P B stB = typings
 * requires (stA, A, P, B, stB) is a valid typing and
 * ensures all typings in the result a valid
 *)

(* cc = Circle/Circle *)
fun cc env ctx con nil (A.Dot) P B (stB as (Circle(t)::stB')) =
    [Tpj(ctx, con, nil, A.Dot, delay1 P, A.Next(one,B), subone stB)]
  | cc env ctx con (stA as (Circle(s)::stA')) A P B (stB as (Circle(t)::stB')) =
    [Tpj(ctx, con, subone stA, A.Next(one,A), delay1 P, A.Next(one,B), subone stB)]
  | cc env ctx con _ _ _ _ _ = []

(* bc = Box/Circle *)
fun bc env ctx con stA (A.Box(A)) P B (stB as (Circle(t)::stB')) =
    [Tpj(ctx, con, stA, A.Box(A), delay1 P, A.Next(one,B), subone stB)]
  | bc env ctx con _ _ _ _ _ = []

(* cd = Circle/Diamond *)
(* do not apply this rule if the left-hand side is empty, because the
 * resulting typing is redundant (same types, but different expression)
 * and that might create an infinite loop.
 * Use cd' to force the Circle/Diamond rule in the forward direction.
 *)
fun cd env ctx con (stA as (Circle(s)::stA')) A P (A.Dia(B)) stB =
    [Tpj(ctx, con, subone stA, A.Next(one,A), delay1 P, A.Dia(B), stB)]
  | cd env ctx con _ _ _ _ _ = []

(* cd' = Circle/Diamond *)
(* cd' cannot be called recursively on the output, but is needed
 * for explicit 'delay{n}' constructs in process expressions
 *)
fun cd' env ctx con nil (A.Dot) P (A.Dia(B)) stB =
    [Tpj(ctx, con, nil, A.Dot, delay1 P, A.Dia(B), stB)]
  | cd' env ctx con (stA as (Circle(s)::stA')) A P (A.Dia(B)) stB =
    [Tpj(ctx, con, subone stA, A.Next(one,A), delay1 P, A.Dia(B), stB)]
  | cd' env ctx con _ _ _ _ _ = []

(* br = BoxR *)
fun br env ctx con stA A P B (Always::stB) =
    if TC.eventually_box env A
    then [Tpj(ctx, con, stA, A, A.WhenR(P), A.Box(B), stB)]
    else []
  | br env ctx con _ _ _ _ _ = []

(* bl = BoxL *)
fun bl env ctx con (Always::stA) A P B stB =
    [Tpj(ctx, con, stA, A.Box(A), A.NowL(P), B, stB)]
  | bl env ctx con _ _ _ _ _ = []

(* dr = DiaR *)
fun dr env ctx con stA A P B (Eventual::stB) =
    [Tpj(ctx, con, stA, A, A.NowR(P), A.Dia(B), stB)]
  | dr env ctx con _ _ _ _ _ = []

(* dl = DiaL *)
fun dl env ctx con (Eventual::stA) A P B stB =
    if TC.eventually_dia env B
    then [Tpj(ctx, con, stA, A.Dia(A), A.WhenL(P), B, stB)]
    else []
  | dl env ctx con _ _ _ _ _ = []

(* refl, to get A <: A in its full generality *)
fun refl env ctx con (stA as (Circle(s)::stA')) A (A.Id) B (stB as (Circle(t)::stB')) =
    [Tpj(ctx, con, subone stA, A.Next(one,A), A.Id, A.Next(one,B), subone stB)]
  | refl env ctx con (Eventual::stA) A (A.Id) B (Eventual::stB) =
    [Tpj(ctx, con, stA, A.Dia(A), A.Id, A.Dia(B), stB)]
  | refl env ctx con (Always::stA) A (A.Id) B (Always::stB) =
    [Tpj(ctx, con, stA, A.Box(A), A.Id, A.Box(B), stB)]
  | refl env ctx con _ _ _ _ _ = []

(* imposs, to get A |- imposs : C in its full generality *)
fun imposs env ctx con (stA as (_::_)) A (A.Imposs) B (stB as (_::_)) =
    let val (stA', A') = restore1 stA A
        val (stB', B') = restore1 stB B
    in
        [Tpj(ctx, con, stA', A', A.Imposs, B,  stB ),
         Tpj(ctx, con, stA,  A,  A.Imposs, B', stB'),
         Tpj(ctx, con, stA', A', A.Imposs, B', stB')]
    end 
  | imposs env ctx con nil A (A.Imposs) B (stB as (_::_)) =
    let val (stB', B') = restore1 stB B
    in 
        [Tpj(ctx, con, nil,  A, A.Imposs, B', stB')]
    end
  | imposs env ctx con (stA as (_::_)) A (A.Imposs) B nil =
    let val (stA', A') = restore1 stA A
    in
        [Tpj(ctx, con, stA',  A', A.Imposs, B, nil )]
    end
  | imposs env ctx con _ _ _ _ _ = []

(* existsR *)
(* backwards:
     con |= phi          con ; A |- P :: B
  ------------------------------------------ ?R
   con ; A |- assertR{phi} ; P :: ?{phi}. B

   forwards:
           con ; A |- P :: B
   ------------------------------------------------ ?RF
    con /\ phi ; A |- assertR{phi} ; P :: ?{phi}.B

   ?RF is sound, because con /\ phi |= phi and con /\ phi |= con
   ?RF is complete, because if con |= phi then con |= con /\ phi 
*)
fun er env ctx con stA A P B (Some(phi)::stB) =
    [Tpj(ctx, R.And(con,phi), stA, A, A.AssertR(phi,P), A.Exists(phi,B), stB)]
  | er env ctx con _ _ _ _ _ = []

(* existsL *)
(* backwards:
   con /\ phi ; A |- P :: B
  ----------------------------------------- ?L
    con ; ?{phi}A |- assumeL{phi} ; P :: B

  forwards:
         con ; A |- P :: B
------------------------------------------------ ?LF
  phi => con ; ?{phi}A |- assumeL{phi} ; P :: B

  ?LF is sound, because (phi => con) /\ phi |= con
  ?LF is complete, because con |= phi => (con /\ phi) 
*)
fun el env ctx con (Some(phi)::stA) A P B stB =
    [Tpj(ctx, R.Implies(phi,con), stA, A.Exists(phi,A), A.AssumeL(phi,P), B, stB)]
  | el env ctx con _ _ _ _ _ = []

(* forallR *)
(* see existsL *)
fun fr env ctx con stA A P B (All(phi)::stB) =
    [Tpj(ctx, R.Implies(phi,con), stA, A, A.AssumeR(phi,P), A.Forall(phi,B), stB)]
  | fr env ctx con _ _ _ _ _ = []

(* forallL *)
(* see existsR *)
fun fl env ctx con (All(phi)::stA) A P B stB =
    [Tpj(ctx, R.And(con,phi), stA, A.Forall(phi,A), A.AssertL(phi,P), B, stB)]
  | fl env ctx con _ _ _ _ _ = []

(* all_children env typing = typings
 * returns all possible conclusion of applying a temporal type
 * reconstruction rule with exception of Circle/Diamond with an empty
 * left-hand side
 *)
fun all_children env (Tpj(ctx,con,stA,A,P,B,stB)) =
    List.concat [cc env ctx con stA A P B stB,
                 bc env ctx con stA A P B stB,
                 cd env ctx con stA A P B stB,
                 br env ctx con stA A P B stB,
                 bl env ctx con stA A P B stB,
                 dr env ctx con stA A P B stB,
                 dl env ctx con stA A P B stB,
                 refl env ctx con stA A P B stB,
                 er env ctx con stA A P B stB,
                 el env ctx con stA A P B stB,
                 fr env ctx con stA A P B stB,
                 fl env ctx con stA A P B stB,
                 imposs env ctx con stA A P B stB
                ]

(* delays env n typings = typings'
 * forces each process P in typings to be expanded to delay{n} ; P
 * by applying all applicable forward rules n times (including
 * Circle/Diamond)
 *)
fun add_delays env 0 typings = typings
  | add_delays env n (Tpj(ctx,con,stA,A,P,B,stB)::typings) = (* n > 0 *)
    add_delays env (n-1)
               (List.concat [cc env ctx con stA A P B stB,
                             bc env ctx con stA A P B stB,
                             cd' env ctx con stA A P B stB,
                             add_delays env n typings])
  | add_delays env n nil = nil

fun pp_typings env nil = "\n-----------------\n"
  | pp_typings env (Tpj(ctx, con, stA, A, P, C, stC)::typings) =
    (* PP.pp_tpj_compact env A (R.Int(0)) C ^ "\n" *)
    PP.pp_exp env P ^ "\n : "                  
    ^ PP.pp_prop con ^ " ; "
    ^ pp_stack stA ^ "|" ^ PP.pp_tp_compact env A
    ^ " |- "
    ^ pp_stack stC ^ "|" ^ PP.pp_tp_compact env C ^ "\n"
    ^ pp_typings env typings

(* add_unique tpg seen = seen'
   add tpg (_,A,P,C,_) to seen if the pair A |- C has not been seen yet

   If con ; A |- P :: B and con' |= con then con' ; A |- P :: B

   So if con ; A |- P :: B and con' ; A |- P :: B
   and con' |= con we only need to keep con ; A |- P :: B
   (the judgment with weaker assumptions)
 *)
fun add_unique tpg nil = tpg::nil
  | add_unique (tpg as Tpj(ctx, con, stA, A, P, C, stC))
               ((tpg' as Tpj(ctx', con', stA', A', P', C', stC'))::seen) =
    if eq_stack stA stA' andalso eq_stack stC stC' (* implies A = A' and C = C' *)
    then case (C.entails ctx con con', C.entails ctx con' con)
          of (true, true) => if TRU.size P < TRU.size P' (* pick the smaller one if types are the same *)
                             then tpg::seen
                             else tpg'::seen
           | (true, false) => tpg'::seen (* con |= con', keep con', drop con (fwd subsumption) *)
           | (false, true) => add_unique tpg seen  (* con' |= con, keep con, drop con' (bwd subsumption) *)
           | (false, false) => tpg'::add_unique tpg seen  (* incomparable: keep both *)
    else tpg'::add_unique tpg seen                        (* incomparable: keep both *)

(* gen_alltypings' env typings seen = seen'
 * generates the closure of the given typings and (accumulator) seen
 * by applying all forward inference rules that respect the subformula
 * property
 *)
fun gen_alltypings' env nil seen = seen
  | gen_alltypings' env (tpg::typings) seen =
    gen_alltypings' env (all_children env tpg @ typings)
                    (add_unique tpg seen) (* without redundancy elimination: (tpg::seen) *)

(* gen_alltypings env typings = typings'
 * generates the closure of the given typings by applying all forward
 * inference rules that respect the subformula property
 *)
fun gen_alltypings env typings =
    let 
        val typings' = gen_alltypings' env typings nil
        (* double-check typing invariant if needed for debugging *)
        (*
        val () = List.app (fn Tpj(ctx, con, stA, A, P, C, stC) =>
                              TC.check_exp false env ctx con A (R.Int(0)) P C NONE)
                          typings'
         *)
        val () = if !Flags.verbosity >= 3 then TextIO.print (pp_typings env typings') else ()
    in
        typings'
    end

(* cut_typing lpot (stA,A,P,B,stB) typings = typings'
 * where typings' are the typings for a cut with P as the first premise
 * with lpot as the potential of P
 *)
fun cut_typing lpot (tpgL as Tpj(ctx,con,stA,A,P,B,stB)) (Tpj(ctx',con',stB',B',Q,C,stC)::tpgRs) =
    if eq_stack stB stB' (* implies B = B', because stB | B = stB' | B' *)
    then let (* construct simplified process if possible *)
            val PQ = TRU.build_cut P lpot B Q
          in (* ctx = ctx' *)
              Tpj(ctx,R.And(con,con'),stA,A,PQ,C,stC)::cut_typing lpot tpgL tpgRs
         end
    else cut_typing lpot tpgL tpgRs
  | cut_typing lpot tpgL nil = nil

(* cut_typings lpot typingsL typingsR = typings'
 * where typings' are the typings for a cut with the left
 * typing as the first premise and right typing as the
 * second premise and left potential lpot
 *)
fun cut_typings lpot nil tpgRs = nil
  | cut_typings lpot (tpgL::tpgLs) tpgRs =
    cut_typing lpot tpgL tpgRs @ cut_typings lpot tpgLs tpgRs

(* A right branch typing is a tuple (branches, C, stC) where each
 * branch in branches has right type C and stC | C is a subformula
 *)

(* merge_branchL l ext tpgL branchtypings = branchtypings'
 * adding tpgL to each compatible branch typing.  The branch
 * created from tpgL has label l and extent ext.
 *)
fun merge_branchL l ext (tpgL as Tpj(ctx, con, nil, A, P, C, stC)) ((ctx', con', branches', C', stC')::tpgRs) =
    (* branches' <> nil, ctx = ctx' *)
    if eq_stack stC stC' (* implies C = C' because stC | C = stC' | C' *)
    then (ctx, R.And(con,con'), (l, ext, P)::branches', C', stC')::merge_branchL l ext tpgL tpgRs
    else merge_branchL l ext tpgL tpgRs
  | merge_branchL l ext tpgL nil =
    (* new branch is not compatible with any more previous ones; drop *)
    nil

(* merge_branchesL l ext tpgLs tpg_branches = tpg_branches'
 * adding each compatible typing in tpgL to tpg_branches.  Each
 * branch created from tpgL has label l and extent ext.
 *)
fun merge_branchesL l ext nil tpg_branches = nil
  | merge_branchesL l ext (tpg::tpgs) tpg_branches =
    merge_branchL l ext tpg tpg_branches @ merge_branchesL l ext tpgs tpg_branches

(* A left branch typings is a tuple (stA, A, branches) where each
 * branch in branches has left type A and stA | A is a subformula
 *)

(* merge_branchR, symmetric to merge_branchL *)
fun merge_branchR l ext (tpgR as Tpj(ctx, con, stA, A, P, C, nil)) ((ctx', con', stA', A', branches')::tpgLs) =
   (* branches' <> nil, ctx = ctx' *)
    if eq_stack stA stA' (* implies A = A' because stA | A = stA' | A' *)
    then (ctx, R.And(con,con'), stA', A', (l, ext, P)::branches')::merge_branchR l ext tpgR tpgLs
    else merge_branchR l ext tpgR tpgLs
 | merge_branchR l ext tpgR nil = nil

(* merge_banchesR, symmetric to merge_branchesL *)
fun merge_branchesR l ext nil tpg_branches = nil
  | merge_branchesR l ext (tpg::tpgs) tpg_branches =
    merge_branchR l ext tpg tpg_branches @ merge_branchesR l ext tpgs tpg_branches

(* filterL typings = typings', the set of typings where the
 * left stack has been exhausted.  Called at a left interaction.
 *)
fun filterL ((tpg as Tpj(ctx,con,nil,_,_,_,_))::typings) = tpg::filterL typings
  | filterL (_::typings) = filterL typings
  | filterL nil = nil

(* filterR typings = typings', the set of typings where the
 * right stack has been exhausted.  Called at a right interaction.
 *)
fun filterR ((tpg as Tpj(ctx,con,_,_,_,_,nil))::typings) = tpg::filterR typings
  | filterR (_::typings) = filterR typings
  | filterR nil = nil

(* filterLR typings = typings', where both left and right typings
 * have been exhausted.  Called at the top level.
 *)
fun filterLR typings = filterL (filterR typings)

(* filter_entails ctx con tpgs = tpgs', those typings among tpgs
 * with constrainted entailed by con.  Currently only called at
 * the top level, so the stacks on both sides must be empty.
 *)
fun filter_entailed ctx con ((tpg as Tpj(ctx', con', nil, A', P', C', nil))::tpgs) =
    (* ctx = ctx' *)
    if C.entails ctx con con'
    then tpg::filter_entailed ctx con tpgs
    else filter_entailed ctx con tpgs
  | filter_entailed ctx con nil = nil

fun syn_spawn env (A.ExpName(f,es)) = TC.synLR env (f,es)
  | syn_spawn env (A.Marked(marked_P)) = syn_spawn env (Mark.data marked_P)

fun project ((l,A)::choices) k =
    if l = k then A
    else project choices k
(* nil impossible, by invariant *)

(*********************)
(* Typing Statistics *)
(*********************)

(* collect a list of the lengths of possible typings *)
local
    val tpgstat = ref (nil:int list)
in
fun stat_reset () = ( tpgstat := nil )
fun stat_add (tpgs) = ( tpgstat := List.length tpgs :: !tpgstat )
fun stat_print () = List.foldr (fn (count, msg) => Int.toString count ^ " " ^ msg) "" (!tpgstat)
end

(* synth' env ctx con stA S P T stC ext = typings
 * S, T are structural (that is, non-temporal, non-quantified)
 * stA | S and stC | T are subformulas
 * ctx ; con ; S |- P : T, approximately
 * Results are the possible typings with reconstructions
 * of P obeying the subformula property.  For each typing
 * Tpj(ctx', con', stA', A', P', C', stC') we need no more than one
 * expression P'.
 * raise ErrorMsg.Error if there are no typings
 *)
fun synth' env ctx con stA S P T stC ext =
    let val typings = synth env ctx con stA S P T stC ext
        val () = stat_add typings
        val () = case typings
                  of nil => ERROR ext ("could not synthesize any types for\n"
                                       ^ PP.pp_exp env P ^ "\n : "
                                       ^ PP.pp_tpj_compact env (restore stA S) (R.Int(0)) (restore stC T))
                   | _ => ()
    in
        typings
    end

    (* start with non-structural cases *)
and synth env ctx con stA S (A.Id) T stC ext =
    (* generates all typings, capturing stA | S <= stC | T if S == T *)
    (* ctx and con are needed here to check if S == T *)
    if TC.eq_tp env ctx con S T
    then gen_alltypings env [Tpj(ctx,con,stA,S,A.Id,T,stC)]
    else []                     (* no typings possible if S <> T *)
  | synth env ctx con stA S (A.Cut(P,lpot,B,Q)) T stC ext =
    let val (ctx', con', stB', R') = extract env ctx con Right B nil
        val typingsL = synth' env ctx' con' stA S P R' stB' ext
        val typingsL' = filterR typingsL
        val (ctx'', con'', stB'', R'') = extract env ctx con Left B nil (* R' = R'', stB' = stB'' *)
        val typingsR = synth' env ctx'' con'' stB'' R'' Q T stC ext
        val typingsR' = filterL typingsR
        val typings = cut_typings lpot typingsL' typingsR'
    in
        gen_alltypings env typings
    end
  | synth env ctx con stA S (A.Spawn(P,Q)) T stC ext =
    (* for spawn f || Q, possibly insert coercion <-> || (f || Q')
     * to match the left type of f with stA | S
     *)
    let val (A',pot,B') = syn_spawn env P (* need: stA | S <= A' *)
        val (ctx', con', stB', U) = extract env ctx con Left B' nil
        val typingsR = synth' env ctx' con' stB' U Q T stC ext
        val typingsR' = filterL typingsR (* redundant? *)
        val typingsCut = cut_typings pot [Tpj(ctx,con,nil,A',P,B',nil)] typingsR'
        val (ctx'', con'', stA', R) = extract env ctx con Right A' nil
    (* can only insert coercion if R <> A.Dot *)
    in case R
        of A.Dot => gen_alltypings env typingsCut
         | _ => let val typingsL = synth' env ctx'' con'' stA S (A.Id) R stA' ext
                    val typingsL' = filterR typingsL (* redundant? *)
                    val typings = cut_typings (R.Int(0)) typingsL' typingsCut (* no potential needed for identity coercion *)
                in 
                    gen_alltypings env typings
                end
    end
  | synth env ctx con stA S (P as A.ExpName(f,es)) T stC ext =
    (* expand call as spawn + fwd *)
    synth env ctx con stA S (A.Spawn(P,A.Id)) T stC ext

  (* next, all the structural cases *)
  (* basic session types *)
  | synth env ctx con stA S (A.LabR(k,P)) (T as A.Plus(choices)) stC ext =
    let val Ck = project choices k
        val (ctx', con', stCk, Tk) = extract env ctx con Right Ck nil
        val typings_k = synth' env ctx' con' stA S P Tk stCk ext
        val typings_k' = filterR typings_k (* or the map-like operation could also filter *)
        val typings = List.map (fn Tpj(ctx', con', stA', A', P', Ck', nil) => (* Ck' = Ck for each Ck' *)
                                   Tpj(ctx', con', stA', A', A.LabR(k,P'), T, stC))
                               typings_k'
    in
        gen_alltypings env typings
    end
  | synth env ctx con stA (S as A.Plus(choices)) (A.CaseL(branches)) T stC ext =
    let val tpg_branches = synth_branchesL env ctx con choices branches T stC ext
        val typings = List.map (fn (ctx', con', branches, C', stC') =>
                                   Tpj(ctx', con', stA, S, A.CaseL(branches), C', stC'))
                               tpg_branches
    in
        gen_alltypings env typings
    end

  | synth env ctx con stA S (A.CaseR(branches)) (T as A.With(choices)) stC ext =
    let val tpg_branches = synth_branchesR env ctx con stA S branches choices ext
        val typings = List.map (fn (ctx', con', stA', A', branches) =>
                                   Tpj(ctx', con', stA', A', A.CaseR(branches), T, stC))
                               tpg_branches
    in
        gen_alltypings env typings
    end
  | synth env ctx con stA (S as A.With(choices)) (A.LabL(k,Q)) T stC ext =
    let val Ak = project choices k
        val (ctx', con', stAk, Sk) = extract env ctx con Left Ak nil
        val typings_k = synth' env ctx' con' stAk Sk Q T stC ext
        val typings_k' = filterL typings_k
        val typings = List.map (fn Tpj(ctx', con', nil, Ak', Q', C', stC') => (*  Ak' = Ak for each Ak' *)
                                   Tpj(ctx', con', stA, S, A.LabL(k,Q'), C', stC'))
                      typings_k'
    in
        gen_alltypings env typings
    end

  | synth env ctx con stA (A.Dot) (A.CloseR) (A.One) stC ext =
    (* TODO: should this be [Tpj(ctx, con, stA, A.Dot, A.CloseR, A.One, stC)]? *)
    gen_alltypings env [Tpj(ctx,R.True,stA,A.Dot,A.CloseR,A.One,stC)]

  | synth env ctx con stA (S as A.One) (A.WaitL(Q)) T stC ext =
    let val typings_Q = synth' env ctx con nil A.Dot Q T stC ext
                            (* filterL unnecessary, since empty context *)
        val typings = List.map (fn Tpj(ctx', con', nil, A.Dot, Q', C', stC') =>
                                   Tpj(ctx', con', stA, S, A.WaitL(Q'), C', stC'))
                      typings_Q
    in 
        gen_alltypings env typings
    end

  (* imposs, from branch reconstruction, brecon.sml *)
  | synth env ctx con stA S (P as A.Imposs) T stC ext =
    gen_alltypings env [Tpj(ctx, R.False, stA, S, P, T, stC)]

  (* delay{t} ; P from cost model or given in expression *)
  | synth env ctx con stA S (A.Delay(t,P)) T stC ext =
    let
        val R.Int(n) = t        (* only constants allowed for now *)
        val typings = synth' env ctx con stA S P T stC ext
        val typings' = add_delays env n typings
    in
        gen_alltypings env typings'
    end

  (* marked expression *)
  | synth env ctx con stA S (A.Marked(marked_P)) T stC ext =
    synth env ctx con stA S (Mark.data marked_P) T stC (Mark.ext marked_P)

  (* everything else should be impossible, by approximate typing *)

and synth_branchesL env ctx con ((l,Al)::nil) ((l',ext',Pl)::nil) T stC ext =
    (* l = l' *)
    let val (ctx', con', stAl, Sl) = extract env ctx con Left Al nil
        val typings_l = synth' env ctx' con' stAl Sl Pl T stC ext
        val typings_l' = filterL typings_l (* now typings match Al exactly: Tpj(_, _, nil, Al, Pl', C', stC') *)
        val typings_choices = List.map (fn Tpj(ctx', con', nil, Al', Pl', C', stC') => (* Al' = Al for each l *)
                                              (ctx', con', (l', ext', Pl')::nil, C', stC')) (* last branch *)
                              typings_l'
    in
        typings_choices
    end
  | synth_branchesL env ctx con ((l,Al)::choices) ((l',ext',Pl)::branches) T stC ext =
    (* l = l' by prior approximate reconstruction *)
    let val (ctx', con', stAl, Sl) = extract env ctx con Left Al nil
        val typings_l = synth' env ctx' con' stAl Sl Pl T stC ext
        val typings_l' = filterL typings_l (* now typings match Al exactly *)
        val typings_choices = synth_branchesL env ctx con choices branches T stC ext
    in
        (* have (nil, Al', Pl', T', stC') for each l *)
        (* need ([(l, ext, Pl'),...], T', stC') *)
        (* the right-hand sides have to match! *)
        merge_branchesL l' ext' typings_l' typings_choices
    end
    (* empty list of choices impossible *)

and synth_branchesR env ctx con stA S ((l,ext',Pl)::nil) ((l',Cl)::nil) ext =
    (* l = l' *)
    let val (ctx', con', stCl, Tl) = extract env ctx con Right Cl nil
        val typings_r = synth' env ctx' con' stA S Pl Tl stCl ext
        val typings_r' = filterR typings_r (* now typings Cl match exactly *)
        val typings_choices = List.map (fn Tpj(ctx', con', stA', A', Pl', Cl', nil) => (* Cl' = Cl for each l *)
                                              (ctx', con', stA', A', (l, ext', Pl')::nil))
                                       typings_r'
    in
        typings_choices
    end
  | synth_branchesR env ctx con stA S ((l,ext',Pl)::branches) ((l',Cl)::choices) ext =
    (* l = l' *)
    let val (ctx', con', stCl, Tl) = extract env ctx con Right Cl nil
        val typings_r = synth' env ctx' con' stA S Pl Tl stCl ext
        val typings_r' = filterR typings_r (* now typings match Cl exactly *)
        val typings_choices = synth_branchesR env ctx con stA S branches choices ext
    in
        merge_branchesR l ext' typings_r' typings_choices
    end
    (* empty list of choices impossible *)

fun recon env ctx con A pot P C ext =
    let val () = stat_reset ()
        val (ctx', con', stA, S) = extract env ctx con Left A nil
        val (ctx'', con'', stC, T) = extract env ctx con Right C nil
        val typings = synth' env ctx (R.And(con',con'')) stA S P T stC ext
        val typings' = filterLR typings (* |typings'| = 0 or 1 if there are no constraints *)
        val typings'' = filter_entailed ctx con typings' (* filter, keep only those whose constraint is entailed by con *)
        val () = stat_add typings''
        val () = if !Flags.verbosity >= 2
                 then TextIO.print ("% temporal synthesis statistics: number of possible typings for each subexpression\n"
                                    ^ "% top level first\n"
                                    ^ "% " ^ stat_print () ^ "\n")
                 else ()
    in
        case (typings'', typings')
         of (nil, nil) => ERROR ext ("could not synthesize temporal types matching\n"
                                     ^ PP.pp_tp_compact env A ^ " |- " ^ PP.pp_tp_compact env C)
          | (nil, _::_) => ERROR ext ("constraints insufficient for time reconstruction\n"
                                      ^ String.concat (List.map (fn Tpj(ctx', con', _, _, _, _, _) =>
                                                                    C.pp_jfail con con' ^ "\n")
                                                       typings'))
          | (Tpj(ctx',con',_,_,P',_,_)::_, _) => P'
    end

end (* structure TQRecon *)
