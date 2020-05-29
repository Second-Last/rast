(* Type Errors *)
(* Author: Frank Pfenning <fp@cs.cmu.edu> *)
(* Shared between various reconstruction and checking modules
 * Each function raises exception ErrorMsg.Error
 *)

signature TP_ERROR =
sig
    (* all of these will raise ErrorMsg.error *)
    val error_undeclared : Ast.expname * Ast.ext -> 'a

    val error_implicit : Ast.exp * Ast.ext -> 'a
    val error_label_missing_alt : Ast.label * Ast.ext -> 'a
    val error_label_invalid : Ast.env * Ast.tp * Ast.ext -> 'a
    val error_label_missing_branch : Ast.label * Ast.ext -> 'a

    val error_channel_number : string -> int * int -> Ast.ext -> 'a
    val error_index_number : string -> int * int -> Ast.ext -> 'a
                                                                 
    val error_channel_mismatch : string -> Ast.chan * Ast.chan -> Ast.ext -> 'a
    val error_type_mismatch : Ast.env -> string -> Ast.chan_tp * Ast.chan_tp -> Ast.ext -> 'a
    val error_channel_type_mismatch : Ast.env -> string * Ast.chan_tp -> Ast.ext -> 'a

    val error_channels_open : string -> Ast.context -> Ast.ext -> 'a
end

structure TpError =
struct

structure A = Ast
structure PP = PPrint
val ERROR = ErrorMsg.ERROR

fun error_undeclared (f, ext) =
    ERROR ext ("process " ^ f ^ " undeclared")

fun error_implicit (P, ext) =
    ERROR ext ("not allowed in implicit syntax")

fun error_label_missing_alt (l, ext) =
    ERROR ext ("label " ^ l ^ " does not appear among the alternatives in the type")

fun error_label_invalid env (l, A, ext) =
    ERROR ext ("label " ^ l ^ " not a valid alternative in type " ^ PP.pp_tp_compact env A)

fun error_label_missing_branch (l, ext) =
    ERROR ext ("label " ^ l ^ " does not appear among the branches")

fun error_channel_number msg (n,k) ext =
    ERROR ext ("incorrect number of channels in " ^ msg ^ ":\n"
               ^ "expected " ^ Int.toString n ^ "\n"
               ^ "found    " ^ Int.toString k)

fun error_index_number msg (n,k) ext =
    ERROR ext ("incorrect number of index objects in " ^ msg ^ ":\n"
               ^ "expected " ^ Int.toString n ^ "\n"
               ^ "found    " ^ Int.toString k)

fun error_channel_mismatch msg (x, y) ext =
    ERROR ext ("channel mismatch in " ^ msg ^ ":\n"
               ^ "expected " ^ x ^ "\n"
               ^ "found    " ^ y)

fun error_type_mismatch env msg ((x,A), (y,B)) ext =
    let
        val (x_len,y_len) = (String.size x, String.size y)
        val var_len = Int.max(x_len, y_len)
        val (x_str,y_str) = (StringCvt.padRight #" " var_len x,
                             StringCvt.padRight #" " var_len y)
    in
        ERROR ext ("type mismatch in " ^ msg ^ ":\n"
                   ^ "expected " ^ x_str ^ " : " ^ PP.pp_tp_compact env A ^ "\n"
                   ^ "found    " ^ y_str ^ " : " ^ PP.pp_tp_compact env B)
    end

fun error_channel_type_mismatch env (expected, (x,A)) ext =
    ERROR ext ("type mismatch:\n"
               ^ "expected " ^ x ^ " : " ^ expected ^ "\n"
               ^ "found    " ^ x ^ " : " ^ PP.pp_tp_compact env A)

fun pp_channels ((x,A)::nil) = x
  | pp_channels ((x,A)::D) = x ^ " " ^ pp_channels D

fun error_channels_open msg D ext =
    ERROR ext ("open channels at " ^ msg ^ ": " ^ pp_channels D)
    

end (* structure TpError *)
