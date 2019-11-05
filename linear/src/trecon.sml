(* Time Reconstruction *)
(* At present only for constant times *)
(* Unlike quantifier and work reconstruction
 * this allows insertion of identity coercion
 * before spawns, following the rules of the ICFP'18 paper.
 *)

(* This version synthesizes typings bottom up,
 * raises an error for the first subexpression encountered
 * that has no legal typing
 *)

structure TRecon :> RECON =
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
datatype temporal = Circle of R.arith
                  | Eventual
                  | Always

(* extract env A st = st'
 * where st' is the stack of temporal modalities at the
 * beginning of A pushed onto st
 *)
fun extract env (A as A.Next(t,A')) st =
    ((case R.evaluate t
      of 0 => extract env A' st
       | n => extract env A' (Circle(R.Int(n))::st))
     handle R.NotClosed => ERROR NONE
                                 ("Illegal type: " ^ PP.pp_tp_compact env A ^ "\n"
                                  ^ "time reconstruction supports only constant time; use explicit syntax"))
  | extract env (A.Dia(A')) st = extract env A' (Eventual::st)
  | extract env (A.Box(A')) st = extract env A' (Always::st)
  | extract env (A.TpName(a,es)) st = extract env (A.expd_tp env (a,es)) st
  | extract env A st = (st,A)

(* restore env st A = st | A *)
fun restore env (Circle(t)::st) A = restore env st (A.Next(t,A))
  | restore env (Eventual::st) A = restore env st (A.Dia(A))
  | restore env (Always::st) A = restore env st (A.Box(A))
  | restore env (nil) A = A

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
    [(nil, A.Dot, delay1 P, A.Next(one,B), subone stB)]
  | cc env ctx con (stA as (Circle(s)::stA')) A P B (stB as (Circle(t)::stB')) =
    [(subone stA, A.Next(one,A), delay1 P, A.Next(one,B), subone stB)]
  | cc env ctx con _ _ _ _ _ = []

(* bc = Box/Circle *)
fun bc env ctx con stA (A.Box(A)) P B (stB as (Circle(t)::stB')) =
    [(stA, A.Box(A), delay1 P, A.Next(one,B), subone stB)]
  | bc env ctx con _ _ _ _ _ = []

(* cd = Circle/Diamond *)
(* do not apply this rule if the left-hand side is empty, because the
 * resulting typing is redundant (same types, but different expression)
 * and that might create an infinite loop.
 * Use cd' to force the Circle/Diamond rule in the forward direction.
 *)
fun cd env ctx con (stA as (Circle(s)::stA')) A P (A.Dia(B)) stB =
    [(subone stA, A.Next(one,A), delay1 P, A.Dia(B), stB)]
  | cd env ctx con _ _ _ _ _ = []

(* cd' = Circle/Diamond *)
(* cd' cannot be called recursively on the output, but is needed
 * for explicit 'delay{n}' constructs in process expression
 *)
fun cd' env ctx con nil (A.Dot) P (A.Dia(B)) stB =
    [(nil, A.Dot, delay1 P, A.Dia(B), stB)]
  | cd' env ctx con (stA as (Circle(s)::stA')) A P (A.Dia(B)) stB =
    [(subone stA, A.Next(one,A), delay1 P, A.Dia(B), stB)]
  | cd' env ctx con _ _ _ _ _ = []

(* br = BoxR *)
fun br env ctx con stA A P B (Always::stB) =
    if TC.eventually_box env A
    then [(stA,A,A.WhenR(P),A.Box(B),stB)]
    else []
  | br env ctx con _ _ _ _ _ = []

(* bl = BoxL *)
fun bl env ctx con (Always::stA) A P B stB =
    [(stA,A.Box(A),A.NowL(P),B,stB)]
  | bl env ctx con _ _ _ _ _ = []

(* dr = DiaR *)
fun dr env ctx con stA A P B (Eventual::stB) =
    [(stA,A,A.NowR(P),A.Dia(B),stB)]
  | dr env ctx con _ _ _ _ _ = []

(* dl = DiaL *)
fun dl env ctx con (Eventual::stA) A P B stB =
    if TC.eventually_dia env B
    then [(stA,A.Dia(A),A.WhenL(P),B,stB)]
    else []
  | dl env ctx con _ _ _ _ _ = []

(* refl, to get A <: A in its full generality *)
fun refl env ctx con (stA as (Circle(s)::stA')) A (A.Id) B (stB as (Circle(t)::stB')) =
    [(subone stA, A.Next(one,A), A.Id, A.Next(one,B), subone stB)]
  | refl env ctx con (Eventual::stA) A (A.Id) B (Eventual::stB) =
    [(stA, A.Dia(A), A.Id, A.Dia(B), stB)]
  | refl env ctx con (Always::stA) A (A.Id) B (Always::stB) =
    [(stA, A.Box(A), A.Id, A.Box(B), stB)]
  | refl env ctx con _ _ _ _ _ = []

(* all_children env ctx con typing = typings
 * returns all possible conclusion of applying a temporal type
 * reconstruction rule with exception of Circle/Diamond with an empty
 * left-hand side
 *)
fun all_children env ctx con (stA,A,P,B,stB) =
    List.concat [cc env ctx con stA A P B stB,
                 bc env ctx con stA A P B stB,
                 cd env ctx con stA A P B stB,
                 br env ctx con stA A P B stB,
                 bl env ctx con stA A P B stB,
                 dr env ctx con stA A P B stB,
                 dl env ctx con stA A P B stB,
                 refl env ctx con stA A P B stB]

(* delays env ctx con n typings = typings'
 * forces each process P in typings to be expanded to delay{n} ; P
 * by applying all applicable forward rules n times (including
 * Circle/Diamond)
 *)
fun add_delays env ctx con 0 typings = typings
  | add_delays env ctx con n ((stA,A,P,B,stB)::typings) = (* n > 0 *)
    add_delays env ctx con (n-1)
           (List.concat [cc env ctx con stA A P B stB,
                         bc env ctx con stA A P B stB,
                         cd' env ctx con stA A P B stB,
                         add_delays env ctx con n typings])
  | add_delays env ctx con n nil = nil

fun pp_typings env nil = "\n-----------------\n"
  | pp_typings env ((stA, A, P, C, stC)::typings) =
    PP.pp_exp env P ^ "\n : " ^ PP.pp_tpj_compact env A (R.Int(0)) C ^ "\n"
    ^ pp_typings env typings

(* add_unique tpg seen = seen'
 * add tpg (_,A,P,C,_) to seen if the pair A |- C has not been seen yet
 * If it is in the list of typings, retain the typing with the smaller process
 *)
fun add_unique tpg nil = tpg::nil
  | add_unique (tpg as (stA,A,P,C,stC)) ((tpg' as (stA',A',P',C',stC'))::seen) =
    if stA = stA' andalso stC = stC' (* implies A = A' and C = C' *)
    then if TRU.size P < TRU.size P' (* pick the smaller one if types are the same *)
         then tpg::seen
         else tpg'::seen
    else tpg'::add_unique tpg seen

(* gen_alltypings' env ctx con typings seen = seen'
 * generates the closure of the given typings and (accumulator) seen
 * by applying all forward inference rules that respect the subformula
 * property *)
fun gen_alltypings' env ctx con nil seen = seen
  | gen_alltypings' env ctx con (tpg::typings) seen =
    gen_alltypings' env ctx con (all_children env ctx con tpg @ typings)
                    (add_unique tpg seen) (* without redundancy elimination: (tpg::seen) *)

(* gen_alltypings env ctx con typings = typings'
 * generates the closure of the given typings by applying all forward
 * inference rules that respect the subformula property
 *)
fun gen_alltypings env ctx con typings =
    let val typings' = gen_alltypings' env ctx con typings nil
        val () = if !Flags.verbosity >= 3 then TextIO.print (pp_typings env typings') else ()
    in
        typings'
    end
    
(* cut_typing lpot (stA,A,P,B,stB) typings = typings'
 * where typings' are the typings for a cut with P as the first premise
 * with lpot as the potential of P
 *)
fun cut_typing lpot (tpgL as (stA,A,P,B,stB)) ((stB',B',Q,C,stC)::tpgRs) =
    if stB = stB' (* implies B = B', because stB | B = stB' | B' *)
    then let val PQ = TRU.build_cut P lpot B Q
         in  (* construct simplified process if possible *)
             (stA,A,PQ,C,stC)::cut_typing lpot tpgL tpgRs
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
fun merge_branchL l ext (tpgL as (nil, A, P, C, stC)) ((branches', C', stC')::tpgRs) =
    (* branches' <> nil *)
    if stC = stC' (* implies C = C' because stC | C = stC' | C' *)
    then ((l, ext, P)::branches', C', stC')::merge_branchL l ext tpgL tpgRs
    else merge_branchL l ext tpgL tpgRs
  | merge_branchL l ext tpgL nil = nil

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
fun merge_branchR l ext (tpgR as (stA, A, P, C, nil)) ((stA', A', branches')::tpgLs) =
(* branches' <> nil *)
    if stA = stA' (* implies A = A' because stA | A = stA' | A' *)
    then (stA', A', (l, ext, P)::branches')::merge_branchR l ext tpgR tpgLs
    else merge_branchR l ext tpgR tpgLs
 | merge_branchR l ext tpgR nil = nil

(* merge_banchesR, symmetric to merge_branchesL *)
fun merge_branchesR l ext nil tpg_branches = nil
  | merge_branchesR l ext (tpg::tpgs) tpg_branches =
    merge_branchR l ext tpg tpg_branches @ merge_branchesR l ext tpgs tpg_branches

(* filterL typings = typings', the set of typings where the
 * left stack has been exhausted.  Called at a left interaction.
 *)
fun filterL ((tpg as (nil,_,_,_,_))::typings) = tpg::filterL typings
  | filterL (_::typings) = filterL typings
  | filterL nil = nil

(* filterR typings = typings', the set of typings where the
 * right stack has been exhausted.  Called at a right interaction.
 *)
fun filterR ((tpg as (_,_,_,_,nil))::typings) = tpg::filterR typings
  | filterR (_::typings) = filterR typings
  | filterR nil = nil

(* filterLR typings = typings', where both left and right typings
 * have been exhausted.  Called at the top level
 *)
fun filterLR typings = filterL (filterR typings)

fun syn_spawn env (A.ExpName(f,es)) = TC.synLR env (f,es)
  | syn_spawn env (A.Marked(marked_P)) =
    syn_spawn env (Mark.data marked_P)

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
 * S, T are structural (that is, non-temporal)
 * stA | S and stC | T are subformulas
 * S |- P : T, approximately
 * Results are the possible typings with reconstructions
 * of P obeying the subformula property.  For each types
 * (stA', A', P', C', stC') we need no more than one
 * expression P'.
 * raise ErrorMsg.Error if there are no typings
 *)
fun synth' env ctx con stA S P T stC ext =
    let val typings = synth env ctx con stA S P T stC ext
        val () = stat_add typings
        val () = case typings
                  of nil => ERROR ext ("could not synthesize any types for\n"
                                       ^ PP.pp_exp env P ^ "\n : "
                                       ^ PP.pp_tpj_compact env (restore env stA S) (R.Int(0)) (restore env stC T))
                   | _ => ()
    in
        typings
    end

    (* start with non-structural cases *)
and synth env ctx con stA S (A.Id) T stC ext =
    (* generates all typings, capturing stA | S <= stC | T if S == T *)
    if TC.eq_tp env ctx con S T
    then gen_alltypings env ctx con [(stA,S,A.Id,T,stC)]
    else []                     (* no typings possible if S <> T *)
  | synth env ctx con stA S (A.Cut(P,lpot,B,Q)) T stC ext =
    let val (stB, R) = extract env B nil
        val typingsL = synth' env ctx con stA S P R stB ext
        val typingsL' = filterR typingsL
        val typingsR = synth' env ctx con stB R Q T stC ext
        val typingsR' = filterL typingsR
        val typings = cut_typings lpot typingsL' typingsR'
    in
        gen_alltypings env ctx con typings
    end
  | synth env ctx con stA S (A.Spawn(P,Q)) T stC ext =
    (* for spawn f || Q, possibly insert coercion <-> || (f || Q')
     * to match the left type of f with stA | S
     *)
    let val (A',pot,B') = syn_spawn env P (* need: stA | S <= A' *)
        val (stB', U) = extract env B' nil
        val typingsR = synth' env ctx con stB' U Q T stC ext
        val typingsR' = filterL typingsR (* redundant? *)
        val typingsCut = cut_typings pot [(nil,A',P,B',nil)] typingsR'
        val (stA', R) = extract env A' nil
    (* can only insert coercion if R <> A.Dot *)
    in case R
        of A.Dot => gen_alltypings env ctx con typingsCut
         | _ => let val typingsL = synth' env ctx con stA S (A.Id) R stA' ext
                    val typingsL' = filterR typingsL (* redundant? *)
                    val typings = cut_typings (R.Int(0)) typingsL' typingsCut (* no potential needed for identity coercion *)
                in 
                    gen_alltypings env ctx con typings
                end
    end
  | synth env ctx con stA S (P as A.ExpName(f,es)) T stC ext =
    (* expand call as spawn + fwd *)
    synth env ctx con stA S (A.Spawn(P,A.Id)) T stC ext

  (* next, all the structural cases *)
  (* basic session types *)
  | synth env ctx con stA S (A.LabR(k,P)) (T as A.Plus(choices)) stC ext =
    let val Ck = project choices k
        val (stCk, Tk) = extract env Ck nil
        val typings_k = synth' env ctx con stA S P Tk stCk ext
        val typings_k' = filterR typings_k (* or the map-like operation could also filter *)
        val typings = List.map (fn (stA', A', P', Ck', nil) => (* Ck' = Ck for each Ck' *)
                                   (stA', A', A.LabR(k,P'), T, stC))
                               typings_k'
    in
        gen_alltypings env ctx con typings
    end
  | synth env ctx con stA (S as A.Plus(choices)) (A.CaseL(branches)) T stC ext =
    let val tpg_branches = synth_branchesL env ctx con choices branches T stC ext
        val typings = List.map (fn (branches, C', stC') =>
                                   (stA, S, A.CaseL(branches), C', stC'))
                               tpg_branches
    in
        gen_alltypings env ctx con typings
    end

  | synth env ctx con stA S (A.CaseR(branches)) (T as A.With(choices)) stC ext =
    let val tpg_branches = synth_branchesR env ctx con stA S branches choices ext
        val typings = List.map (fn (stA', A', branches) =>
                                    (stA', A', A.CaseR(branches), T, stC))
                               tpg_branches
    in
        gen_alltypings env ctx con typings
    end
  | synth env ctx con stA (S as A.With(choices)) (A.LabL(k,Q)) T stC ext =
    let val Ak = project choices k
        val (stAk, Sk) = extract env Ak nil
        val typings_k = synth' env ctx con stAk Sk Q T stC ext
        val typings_k' = filterL typings_k
        val typings = List.map (fn (nil, Ak', Q', C', stC') => (*  Ak' = Ak for each Ak' *)
                                   (stA, S, A.LabL(k,Q'), C', stC'))
                      typings_k'
    in
        gen_alltypings env ctx con typings
    end

  | synth env ctx con stA (A.Dot) (A.CloseR) (A.One) stC ext =
    gen_alltypings env ctx con [(stA,A.Dot,A.CloseR,A.One,stC)]

  | synth env ctx con stA (S as A.One) (A.WaitL(Q)) T stC ext =
    let val typings_Q = synth' env ctx con nil A.Dot Q T stC ext
                            (* filterL unnecessary, since empty context *)
        val typings = List.map (fn (nil, A.Dot, Q', C', stC') =>
                                   (stA, S, A.WaitL(Q'), C', stC'))
                      typings_Q
    in 
        gen_alltypings env ctx con typings
    end

  (* quantifiers *)
  | synth env ctx con stA S (A.AssertR(phi,P)) (T as A.Exists(phi',C)) stC ext =
    let val (stC', T') = extract env C nil
        val typingsR = synth' env ctx con stA S P T' stC' ext
        val typingsR' = filterR typingsR
        val typings = List.map (fn (stA', A', P', C', nil) =>
                                   (stA', A', A.AssertR(phi,P'), T, stC))
                               typingsR'
    in
      gen_alltypings env ctx con typings
    end

  | synth env ctx con stA (S as A.Exists(phi',A)) (A.AssumeL(phi,Q)) T stC ext =
    let val (stA', S') = extract env A nil
        val typingsL = synth' env ctx con stA' S' Q T stC ext
        val typingsL' = filterL typingsL
        val typings = List.map (fn (nil, A', Q', C', stC') =>
                                   (stA, S, A.AssumeL(phi,Q'), C', stC'))
                               typingsL'
    in
      gen_alltypings env ctx con typings
    end

  (*
  | synth env ctx con stA (S as A.Exists(phi',A)) (Q as A.ImpossL(phi)) T stC ext =
    gen_alltypings env ctx con [(stA,S,Q,T,stC)]
  *)

  | synth env ctx con stA S (A.AssumeR(phi,P)) (T as A.Forall(phi',C)) stC ext =
    let val (stC', T') = extract env C nil
        val typingsR = synth' env ctx con stA S P T' stC' ext
        val typingsR' = filterR typingsR
        val typings = List.map (fn (stA', A', P', C', nil) =>
                                   (stA', A', A.AssumeR(phi,P'), T, stC))
                               typingsR'
    in
      gen_alltypings env ctx con typings
    end

  (*
  | synth env ctx con stA S (P as A.ImpossR(phi)) (T as A.Forall(phi',C)) stC ext =
    gen_alltypings env ctx con [(stA,S,P,T,stC)]
  *)

  | synth env ctx con stA (S as A.Forall(phi',A)) (A.AssertL(phi,Q)) T stC ext =
    let val (stA', S') = extract env A nil
        val typingsL = synth' env ctx con stA' S' Q T stC ext
        val typingsL' = filterL typingsL
        val typings = List.map (fn (nil, A', Q', C', stC') =>
                                   (stA, S, A.AssertL(phi,Q'), C', stC'))
                               typingsL'
    in
      gen_alltypings env ctx con typings
    end

  (* work constructors *)
  | synth env ctx con stA S (A.Work(p,P)) T stC ext =
    let val typings = synth' env ctx con stA S P T stC ext
        val typings' = List.map (fn (stA', A', Q', C', stC') =>
                                    (stA', A', A.Work(p,Q'), C', stC'))
                                typings
    in
        gen_alltypings env ctx con typings'
    end

  | synth env ctx con stA S (A.PayR(p,P)) (T as A.PayPot(p',C)) stC ext =
    let val (stC', T') = extract env C nil
        val typingsR = synth' env ctx con stA S P T' stC' ext
        val typingsR' = filterR typingsR
        val typings = List.map (fn (stA', A', P', C', nil) =>
                                   (stA', A', A.PayR(p,P'), T, stC))
                               typingsR'
    in
      gen_alltypings env ctx con typings
    end

  | synth env ctx con stA (S as A.PayPot(p',A)) (A.GetL(p,Q)) T stC ext =
    let val (stA', S') = extract env A nil
        val typingsL = synth' env ctx con stA' S' Q T stC ext
        val typingsL' = filterL typingsL
        val typings = List.map (fn (nil, A', Q', C', stC') =>
                                   (stA, S, A.GetL(p,Q'), C', stC'))
                               typingsL'
    in
      gen_alltypings env ctx con typings
    end

  | synth env ctx con stA S (A.GetR(p,P)) (T as A.GetPot(p',C)) stC ext =
    let val (stC', T') = extract env C nil
        val typingsR = synth' env ctx con stA S P T' stC' ext
        val typingsR' = filterR typingsR
        val typings = List.map (fn (stA', A', P', C', nil) =>
                                   (stA', A', A.GetR(p,P'), T, stC))
                               typingsR'
    in
      gen_alltypings env ctx con typings
    end

  | synth env ctx con stA (S as A.GetPot(p',A)) (A.PayL(p,Q)) T stC ext =
    let val (stA', S') = extract env A nil
        val typingsL = synth' env ctx con stA' S' Q T stC ext
        val typingsL' = filterL typingsL
        val typings = List.map (fn (nil, A', Q', C', stC') =>
                                   (stA, S, A.PayL(p,Q'), C', stC'))
                               typingsL'
    in
      gen_alltypings env ctx con typings
    end

  (* delay{t} ; P from cost model or given in expression *)
  | synth env ctx con stA S (A.Delay(t,P)) T stC ext =
    let
        val R.Int(n) = t        (* only constants allowed for now *)
        val typings = synth' env ctx con stA S P T stC ext
        val typings' = add_delays env ctx con n typings
    in
        gen_alltypings env ctx con typings'
    end

  (* marked expression *)
  | synth env ctx con stA S (A.Marked(marked_P)) T stC ext =
    synth env ctx con stA S (Mark.data marked_P) T stC (Mark.ext marked_P)

  (* everything else should be impossible, by approximate typing *)

and synth_branchesL env ctx con ((l,Al)::nil) ((l',ext',Pl)::nil) T stC ext =
    let val (stAl, Sl) = extract env Al nil
        val typings_l = synth' env ctx con stAl Sl Pl T stC ext
        val typings_l' = filterL typings_l (* now typings match Al exactly: (nil, Al, Pl', C', stC') *)
        val typings_choices = List.map (fn (nil, Al', Pl', C', stC') => (* Al' = Al for each l *)
                                           ((l', ext', Pl')::nil, C', stC')) (* last branch *)
                              typings_l'
    in
        typings_choices
    end
  | synth_branchesL env ctx con ((l,Al)::choices) ((l',ext',Pl)::branches) T stC ext =
    (* l = l' by prior approximate reconstruction *)
    let val (stAl, Sl) = extract env Al nil
        val typings_l = synth' env ctx con stAl Sl Pl T stC ext
        val typings_l' = filterL typings_l (* now typings match Al exactly *)
        val typings_choices = synth_branchesL env ctx con choices branches T stC ext
    in
        (* have (nil, Al', Pl', T', stC') for each l *)
        (* need ([(l, ext, Pl'),...], T', stC') *)
        (* the right-hand sides have to match! *)
        merge_branchesL l' ext' typings_l' typings_choices
    end
    (* empty list of choices impossible *)

and synth_branchesR env ctx con stA S ((l,ext',Pl)::nil) ((l',Cl)::nil) ext = (* l = l' *)
    let val (stCl, Tl) = extract env Cl nil
        val typings_r = synth' env ctx con stA S Pl Tl stCl ext
        val typings_r' = filterR typings_r (* now typings Cl match exactly *)
        val typings_choices = List.map (fn (stA', A', Pl', Cl', nil) => (* Cl' = Cl for each l *)
                                           (stA', A', (l,ext',Pl')::nil))
                                       typings_r'
    in
        typings_choices
    end
  | synth_branchesR env ctx con stA S ((l,ext',Pl)::branches) ((l',Cl)::choices) ext = (* l = l' *)
    let val (stCl, Tl) = extract env Cl nil
        val typings_r = synth' env ctx con stA S Pl Tl stCl ext
        val typings_r' = filterR typings_r (* now typings match Cl exactly *)
        val typings_choices = synth_branchesR env ctx con stA S branches choices ext
    in
        merge_branchesR l ext' typings_r' typings_choices
    end
    (* empty list of choices impossible *)
    
fun recon env ctx con A pot P C ext =
    let val () = stat_reset ()
        val (stA,S) = extract env A nil
        val (stC,T) = extract env C nil
        val typings = synth' env ctx con stA S P T stC ext
        val typings' = filterLR typings (* |typings'| = 0 or 1 *)
        val () = stat_add typings'
        val () = if !Flags.verbosity >= 2
                 then TextIO.print ("% temporal synthesis statistics: number of possible typings for each subexpression\n"
                                    ^ "% top level first\n"
                                    ^ "% " ^ stat_print () ^ "\n")
                 else ()
    in
        case typings'
         of nil => ERROR ext ("could not synthesize temporal types matching\n"
                              ^ PP.pp_tp_compact env A ^ " |- " ^ PP.pp_tp_compact env C)
          | ((_,_,P',_,_)::_) => P' (* should be a minimal reconstruction *)
    end

end (* structure TRecon *)
