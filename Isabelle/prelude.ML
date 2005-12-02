structure Header :
sig
val dest_thm_axm : Proofterm.proof -> (string * (string * string list) list) * Proofterm.proof
val get_axioms : Proofterm.proof -> string list
val record : string -> unit
val initialize : string list -> unit 
end

= struct

open Proofterm

fun dest_thm_axm (PThm (nt, prf, _, _)) = (nt, prf)
  | dest_thm_axm (PAxm (n, _, _)) = ((n ^ " (Ax)", []), MinProof ([], [], []))
  | dest_thm_axm _ = (("", []), MinProof ([], [], []))

fun get_axioms (AbsP (_, _, prf)) = get_axioms prf
  | get_axioms (Abst (_, _, prf)) = get_axioms prf
  | get_axioms (prf1 %% prf2) = get_axioms prf1 @ get_axioms prf2
  | get_axioms (prf % _) = get_axioms prf
  | get_axioms (MinProof (thms, axms, _)) = 
      fold append (map (get_axioms o Proofterm.proof_of_min_thm) thms) [] @
      fold append (map (get_axioms o Proofterm.proof_of_min_axm) axms) []
  | get_axioms prf = 
      let val ((name, tags), prf') = dest_thm_axm prf
      in
          name :: get_axioms prf'
      end

fun record1 name = 
  let val t = thm name
      val p = Thm.proof_of t
      val axs = get_axioms p
  in
  (map writeln axs; ())
  end

fun record name =
    record1 name handle _ => ()

fun initialize l = ()

end;

proofs:=1;
