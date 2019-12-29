(* Top Level *)

(*
 * Use in a SML read/eval/print loop
 * and for building stand-along executables
 *)

signature TOP =
sig
    val load : Ast.env -> string list -> Ast.env (* Top.load env [<file>,...] = env' *)
    val run : Ast.env -> Ast.decl list -> unit   (* Top.run env decls = () *)

    val ss : string -> OS.Process.status         (* Top.ss "<command line arguments>" = status *)
    val main : string * string list -> OS.Process.status (* for stand-alone executable *)
end (* signature TOP *)

structure Top :> TOP =
struct

structure G = GetOpt  (* from $/smlnj-lib/Util/getopt-sig.sml *)
structure R = Arith
structure A = Ast
structure PP = PPrint

(************************)
(* Command Line Options *)
(************************)

datatype option =
         Time of string
       | Work of string
       | Syntax of string
       | Terminate of string
       | Equality of string
       | Verbose of int
       | Help of bool

(* printing error/success messages to stdErr *)
fun say s = TextIO.output (TextIO.stdErr, s ^ "\n")

val usage =
    if "sml" = #file (OS.Path.splitDirFile (CommandLine.name ()))
    then "Top.ss \"<option>* <file>*\";"
    else "ss <option>* <file>*"
val header = "Usage: " ^ usage ^ "\nwhere <option> is"
val options : option G.opt_descr list =
    [
     {short = "v", long = ["verbose"],
      desc = G.NoArg (fn () => Verbose(2)),
      help = "Give verbose status messages"},
     {short = "q", long = ["quiet"],
      desc = G.NoArg (fn () => Verbose(0)),
      help = "Run quietly"},
     {short = "d", long = ["debug"],
      desc = G.NoArg (fn () => Verbose(3)),
      help = "Print some debugging information"},
     {short = "h", long = ["help"],
      desc = G.NoArg (fn () => Help(true)),
      help = "Give short usage message and exit"},
     {short = "t", long = ["time"],
      desc = G.ReqArg ((fn cm => Time(cm)), "<cost_model>"),
      help = "Cost model for time, one of 'none' (default), 'free', 'recv', 'recvsend', or 'send'"},
     {short = "w", long = ["work"],
      desc = G.ReqArg ((fn cm => Work(cm)), "<cost_model>"),
      help = "Cost model for work, one of 'none' (default), 'free', 'recv', 'recvsend', or 'send'"},
     {short = "s", long = ["syntax"],
      desc = G.ReqArg ((fn s => Syntax(s)), "<syntax>"),
      help = "Syntax, one of 'implicit' (default) or 'explicit'"},
     {short = "e", long = ["terminate"],
      desc = G.ReqArg ((fn r => Terminate(r)), "<recursion>"),
      help = "Perform termination checking, on 'equi' or 'iso' recursive syntax"},
     {short = "u", long = ["equality"],
      desc = G.ReqArg ((fn r => Equality(r)), "<type equality algorithm>"),
      help = "Type equality algorithm, one of 'subsumerefl' (default), 'subsume', or 'refl'"}
    ]

val usage_info = G.usageInfo {header = header, options = options}
exception OS_FAILURE
exception OS_SUCCESS
fun exit_failure msg = ( say msg ; raise OS_FAILURE )
fun exit_success msg = ( say msg ; raise OS_SUCCESS )

fun get_options (args) =
    G.getOpt {argOrder = G.RequireOrder,
              options = options,
              errFn = exit_failure}
             args

fun process_option (Time(s)) =
    (case Flags.parseCost s
      of NONE => exit_failure ("cost model " ^ s ^ " not recognized")
       | SOME(cm) => Flags.time := cm)
  | process_option (Work(s)) =
    (case Flags.parseCost s
      of NONE => exit_failure ("cost model " ^ s ^ " not recognized")
       | SOME(cm) => Flags.work := cm)
  | process_option (Syntax(s)) =
    (case Flags.parseSyntax s
      of NONE => exit_failure ("syntax " ^ s ^ " not recognized")
       | SOME(syn) => Flags.syntax := syn)
  | process_option (Terminate(r)) =
    (case Flags.parseRecursion r
      of NONE => exit_failure ("recursion style " ^ r ^ " not recognized")
       | SOME(recursion) => Flags.terminate := SOME(recursion))
  | process_option (Equality(r)) =
    (case Flags.parseEquality r
      of NONE => exit_failure ("type equality algorithm " ^ r ^ " not recognized")
       | SOME(equality) => Flags.equality := equality )
  | process_option (Verbose(level)) = Flags.verbosity := level
  | process_option (Help(true)) = exit_success usage_info
  | process_option (Help(false)) = ()

(*********************************)
(* Loading and Elaborating Files *)
(*********************************)

fun readable file = OS.FileSys.access (file, [OS.FileSys.A_READ])

fun reset () =
    ( ParseState.reset ()
    ; ErrorMsg.reset ()
    )

fun apply_options line =
    let val args = String.tokens Char.isSpace line
        val (options, filenames) = get_options args (* may exit_failure(msgs) *)
        val () = List.app process_option options
        val () = case filenames of nil => () | (_::_) =>
                 ( ErrorMsg.error NONE ("spurious options: " ^ line ^ "\n")
                 ; raise ErrorMsg.Error )
    in () end

fun apply_pragmas (A.Pragma("#options",line,_)::decls) =
    let val () = if !Flags.verbosity >= 1
                 then TextIO.print ("#options" ^ line ^ "\n")
                 else ()
        val () = apply_options line
    in apply_pragmas decls end
  | apply_pragmas (A.Pragma("#test",line,ext)::decls) =
    (* ignore #test pragma *)
    apply_pragmas decls
  | apply_pragmas (A.Pragma(pragma,line,ext)::decls) =
    ( ErrorMsg.error ext ("unrecognized pragma: " ^ pragma)
    ; raise ErrorMsg.Error )
  | apply_pragmas decls = decls

fun load env (file::filenames) =
    let val () = reset ()     (* internal lexer and parser state *)
        val decls = Parse.parse file (* may raise ErrorMsg.Error *)
        val () = Elab.check_redecl env decls (* may raise ErrorMsg.Error *)
        (* pragmas apply only to type-checker and execution *)
        (* may only be at beginning of file; apply now *)
        val decls' = apply_pragmas decls (* remove pragmas; may raise ErrorMsg.Error *)
    in (* allow for mutually recursive definitions in the same file *)
        case Elab.elab_decls (env @ decls') decls'
         of SOME(env') => load (env @ env') filenames
          | NONE => raise ErrorMsg.Error (* error during elaboration *)
    end
  | load env nil = env

(**********************)
(* Executing Programs *)
(**********************)

fun init_pot env f =
  (case A.lookup_expdec env f
    of SOME(_,_,(_,pot,_)) => R.evaluate pot
    |  NONE => raise ErrorMsg.Error) 

(* measure cost = true if 'cost' is measured *)
fun measure Flags.None = false
  | measure _ = true

(*
fun run env (A.Exec(f,ext)::decls) =
    let val () = if !Flags.verbosity >= 1
                 then TextIO.print (PP.pp_decl env (A.Exec(f,ext)) ^ "\n")
                 else ()
        val p = init_pot env f
        val config = Exec.exec env [A.Proc(0,(0,p),A.ExpName(f,[]))] (* may raise Exec.SoftError/Exec.HardError *)
        val () = if !Flags.verbosity >= 1
                 then TextIO.print (PP.pp_config (measure (!Flags.time)) (measure (!Flags.work)) config
                                    ^ "%------------------------------\n")
                 else ()
    in
        run env decls
    end
  | run env (_::decls) = run env decls
  | run env nil = ()
*)

fun run env decls = ()

fun test args =
    let val () = Flags.reset()
        val () = Constraints.approx := false
        val (options, filenames) = get_options args
        val () = List.app process_option options
        val env = load nil filenames (* env after elaboration *)
            handle ErrorMsg.Error => exit_failure "% parsing or type-checking failed"
        val () = Constraints.solve_global ()
        val () = run env env  (* run all 'exec' decls in env *)
            (*
            handle Exec.SoftError => exit_failure "% execution failed (soft)"
                 | Exec.HardError => exit_failure "% execution failed (hard)"
            *)
    in
        exit_success (if !Constraints.approx then "% approx success" else "% success")
    end handle OS_SUCCESS => OS.Process.success
             | OS_FAILURE => OS.Process.failure

fun ss argstring = test (String.tokens Char.isSpace argstring)
fun main (name, args) = test args

end (* structure Top *)
