(* Reconstruction *)
(* Generic signature for various phases of reconstruction:
 * approximate, quantifiers, work, time
 *)

signature RECON =
sig

    val recon : Ast.env -> Arith.ctx -> Arith.prop
                -> Ast.tp -> Ast.pot -> Ast.exp -> Ast.tp -> Ast.ext
                -> Ast.exp

end  (* signature RECON *)
