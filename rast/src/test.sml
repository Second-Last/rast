(* Simple regression testing for RAST *)

signature TEST =
sig
    val test : string list -> OS.Process.status (* Test.test [<file>,...] = status *)
    val main : string * string list -> OS.Process.status (* for stand-alone executable *)
end

structure Test :> TEST =
struct

structure G = GetOpt        (* from $/smlnj-lib/Util/getopt-sig.sml *)

(* options for the compiler *)
(* printing: v - verbose, q - quiet, d - debug *)
datatype option =
         Verbose of int
       | Help of bool

fun say s = TextIO.output (TextIO.stdErr, s ^ "\n")

val usage = "rast-test <option>* <file>*"
val header = Flags.version ^ "\n" ^ usage
val options : option G.opt_descr list =
    [
     {short = "v", long = ["verbose"],
      desc = G.NoArg (fn () => Verbose(2)),
      help = "Run verbosely"},
     {short = "q", long = ["quiet"],
      desc = G.NoArg (fn () => Verbose(0)),
      help = "Run quietly"},
     {short = "h", long = ["help"],
      desc = G.NoArg (fn () => Help(true)),
      help = "Give short usage message and exit"}
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

structure TestFlags :> sig
    val verbosity : int ref
    val reset : unit -> unit
end =
struct
    val verbosity = ref 1
    fun reset () = ( verbosity := 1 )
end (* structure TestFlags *)

(* set flags according to options given by the programmer *)
fun process_option (Verbose(level)) = TestFlags.verbosity := level
  | process_option (Help(true)) = exit_success usage_info
  | process_option (Help(false)) = ()

(* outcomes of compiling and executing programd *)
datatype outcome =
         StaticError            (* includes lexer, parser, type-checker error *)
       | Success                (* parses, type-checks, and runs successfully *)
       | ApproxDynSuccess       (* parses, fuzzily type-checks and runs successfully *)
       | ApproxDynError         (* parses, fuzzily type-checks but fails at runtime in a controlled way *)
       (* remaining ones are never expected, right now *)
       | DynamicError           (* should not happen *)
       | UncaughtException      (* uncaught exception should always be a bug *)
       | IllegalTestFormat      (* #test pragma not parsable *)
       | FileNotReadable        (* file is not readable *)
       | None                   (* no outcome at all... *)

fun parse_outcome ("error"::nil) = StaticError
  | parse_outcome ("success"::nil) = Success
  | parse_outcome ("approx"::"success"::nil) = ApproxDynSuccess
  | parse_outcome ("approx"::"error"::nil) = ApproxDynError
  | parse_outcome _ = IllegalTestFormat

fun pp_outcome outcome = case outcome of
    StaticError => "static error (lexing, parsing, type-checking)"
  | Success => "success"
  | ApproxDynSuccess => "approx success"
  | ApproxDynError => "approx error"
  | DynamicError => "dynamic error (execution)"
  | UncaughtException => "uncaught exception"
  | IllegalTestFormat => "illegal #test format"
  | FileNotReadable => "file not readable"
  | None => "none"

fun extract_outcome nil = (* nothing specified, default to Success *)
    Success
  | extract_outcome (Ast.Pragma("#test", line, ext)::preamble) =
    (* ignore remaining preamble *)
    parse_outcome (String.tokens Char.isSpace line)
  | extract_outcome (Ast.Pragma _::preamble) =
    extract_outcome preamble
  (* should only be pragmas allowed here *)

exception Outcome of outcome * outcome (* expected, actual *)

fun accept_outcome (StaticError, StaticError) = true
  | accept_outcome (Success, Success) = true
  | accept_outcome (ApproxDynSuccess, ApproxDynSuccess) = true
  | accept_outcome (ApproxDynSuccess, Success) = true (* constraint actually solved *)
  | accept_outcome (ApproxDynError, ApproxDynError) = true
  | accept_outcome (_, _) = false

fun test_file2 expected filename =
    let val env = Top.load nil [filename]
            handle ErrorMsg.Error => raise Outcome(expected, StaticError)
        val () = Top.run env env
            (*
            handle Exec.SoftError => raise Outcome(expected, if !Constraints.approx then ApproxDynError else DynamicError)
                 | Exec.HardError => raise Outcome(expected, DynamicError)
            *)
    in
        raise Outcome(expected, if !Constraints.approx then ApproxDynSuccess else Success)
    end handle e as Outcome(expected, actual) => raise e
             | e => raise Outcome(expected, UncaughtException)

fun test_file1 filename =
    let 
        val () = ParseState.reset ()
        val () = ErrorMsg.reset ()
        val () = Flags.reset ()
        val () = Flags.verbosity := ~1 (* really quiet *)
        val () = Constraints.approx := false
        val preamble = Parse.parse_preamble filename
            handle IO.Io _ => raise Outcome(None, FileNotReadable)
        val expected = extract_outcome preamble
            handle ErrorMsg.Error => raise Outcome(None, IllegalTestFormat)
    in
        test_file2 expected filename
    end handle e as Outcome(expected, actual) => raise e
             | e => raise Outcome(None, UncaughtException)

val total = ref 0
val succeeded = ref 0
val failed = ref 0

fun success (expected, actual) =
    ( if !TestFlags.verbosity >= 1 then TextIO.print "[OK]\n" else ()
    ; succeeded := !succeeded+1 )

fun failure (expected, actual) =
    ( if !TestFlags.verbosity >= 1
      then ( TextIO.print ("[FAIL]\n")
           ; TextIO.print ("Expected: " ^ pp_outcome expected ^ "\n")
           ; TextIO.print ("Actual:   " ^ pp_outcome actual ^ "\n") )
      else ()
    ; failed := !failed+1 )

fun test_file filename =
    ( if !TestFlags.verbosity >= 1
      then ( TextIO.print (filename ^ "... ")
           ; TextIO.flushOut (TextIO.stdOut) )
      else ()
    ; test_file1 filename
      handle Outcome(expected, actual) =>
             ( total := !total+1
             ; if accept_outcome (expected,actual)
               then success (expected, actual)
               else failure (expected, actual) ))

fun reset_counts () =
    ( total := 0
    ; succeeded := 0
    ; failed := 0 )

fun print_results () =
    ( TextIO.print ("Total tests: " ^ Int.toString (!total) ^ "\n")
    ; TextIO.print ("Succeeded:   " ^ Int.toString (!succeeded) ^ "\n")
    ; TextIO.print ("Failed:      " ^ Int.toString (!failed) ^ "\n")
    )
      
fun test args =
    let val () = reset_counts ()
        val () = TestFlags.reset ()
        val (options, filenames) = get_options args
        val () = List.app process_option options
        val () = List.app test_file filenames
        val () = print_results ()
    in
        if !total = !succeeded
        then ( TextIO.print "% regression testing succeeded\n"
             ; OS.Process.success )
        else ( TextIO.print "% regression testing failed\n"
             ; OS.Process.failure )
    end

fun main (name, args) = test args

end (* structure Test *)
