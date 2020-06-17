(* Reconstruction *)
(* Authors: Ankush Das <ankushd@cs.cmu.edu>
 *          Frank Pfenning <fp@cs.cmu.edu>
 *)

(* Generic signature for various phases of reconstruction:
 * approximate, quantifiers, work, time
 *)

signature RECON =
sig

    (* recon env ctx con D pot P (z:C) ext = P' *)
    val recon : Ast.env -> Ast.tp_ctx -> Arith.ctx -> Arith.prop
                -> Ast.context -> Ast.pot -> Ast.exp -> Ast.chan_tp -> Ast.ext
                -> Ast.exp

end  (* signature RECON *)
