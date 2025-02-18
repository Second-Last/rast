(* Flags *)
(* User option given on the command line or in the
 * #options pragma in the source file
 *)

signature FLAGS =
sig
    (* cost model *)
    datatype cost = None | Free | Recv | RecvSend | Send
    val parseCost : string -> cost option
    val pp_cost : cost -> string

    (* syntax *)
    datatype syntax = Implicit | Explicit
    val parseSyntax : string -> syntax option
    val pp_syntax : syntax -> string

    (* recursion *)
    datatype recursion = Equi | Iso
    val parseRecursion : string -> recursion option
    val pp_recursion : recursion option -> string

    (* cost model parameters *)
    val time : cost ref
    val work : cost ref
    val syntax : syntax ref
    val terminate : recursion option ref
    val verbosity : int ref
    val help : bool ref

    (* reset all flags to their default value *)
    val reset : unit -> unit
end  (* signature FLAGS *)

structure Flags :> FLAGS =
struct

(* Cost Model *)
datatype cost =
         None                   (* none *)
       | Free                   (* only explicit work or delay constructs *)
       | Recv                   (* each receive costs 1 unit  *)
       | RecvSend               (* each receive and send costs 1 unit *)
       | Send                   (* each send costs 1 unit *)

fun parseCost "none" = SOME(None)
  | parseCost "recv" = SOME(Recv)
  | parseCost "recvsend" = SOME(RecvSend)
  | parseCost "send" = SOME(Send)
  | parseCost "free" = SOME(Free)
  | parseCost _ = NONE

fun pp_cost (None) = "none"
  | pp_cost (Recv) = "recv"
  | pp_cost (RecvSend) = "recvsend"
  | pp_cost (Send) = "send"
  | pp_cost (Free) = "free"

(* Syntax *)
(* Explicit syntax performs no reconstruction
 * Implicit syntax reconstructs non-structural types
 * (quantifiers, work, time)
 *)
datatype syntax = Implicit | Explicit
fun parseSyntax "implicit" = SOME(Implicit)
  | parseSyntax "explicit" = SOME(Explicit)
  | parseSyntax _ = NONE

fun pp_syntax (Implicit) = "implicit"
  | pp_syntax (Explicit) = "explicit"

(* Recursion *)
datatype recursion = Equi | Iso

fun parseRecursion "equi" = SOME(Equi)
  | parseRecursion "iso" = SOME(Iso)
  | parseRecursion "none" = NONE
  | parseRecursion _ = NONE

fun pp_recursion (SOME(Equi)) = "equi"
  | pp_recursion (SOME(Iso)) = "iso"
  | pp_recursion NONE = "none"

(* Default values *)
val time = ref None
val work = ref None
val syntax = ref Implicit
val terminate = ref (NONE:recursion option)
val verbosity = ref 1           (* ~1 = print nothing, 0 = quiet, 1 = normal, 2 = verbose, 3 = debug *)
val help = ref false

fun reset () =
    ( time := None
    ; work := None
    ; syntax := Implicit
    ; terminate := NONE
    ; verbosity := 1
    ; help := false )

end (* structure Flags *)
