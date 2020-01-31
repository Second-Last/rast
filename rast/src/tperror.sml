(* Type Errors *)
(* Author: Frank Pfenning <fp@cs.cmu.edu> *)
(* Shared between various reconstruction and checking modules
 * Each function raises exception ErrorMsg.Error
 *)

signature TP_ERROR =
sig
    val error_undeclared : Ast.expname * Ast.ext -> 'a

    val error_implicit : Ast.exp * Ast.ext -> 'a
    val error_label_missing_alt : Ast.label * Ast.ext -> 'a
    val error_label_invalid : Ast.env * Ast.tp * Ast.ext -> 'a
    val error_label_mismatch : Ast.label * Ast.label * Ast.ext -> 'a
    val error_label_missing_branch : Ast.label * Ast.ext -> 'a
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

fun error_label_mismatch (l, l', ext) =
    ERROR ext ("label " ^ l ^ " is different from " ^ l' ^ "\n"
               ^ "[Hint: the order of branches must follow the order of the alternatives the type]")

fun error_label_missing_branch (l, ext) =
    ERROR ext ("label " ^ l ^ " does not appear among the branches")

end (* structure TpError *)
