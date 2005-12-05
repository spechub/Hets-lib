structure Header :
sig
val dest_thm_axm : Proofterm.proof -> (string * (string * string list) list) * Proofterm.proof
val get_axioms : Proofterm.proof -> string list
val record : string -> unit
val record1 : string -> unit
val initialize : string list -> unit 
val thmlist : string list ref
end

= struct

open Proofterm

infix mem;

val thmlist = ref [""]

fun axname s =
   let val (_,an) = take_prefix  (fn x => x<>".") (explode s)
   in if null an then "" else implode (tl an)
   end

fun dest_thm_axm (PThm (nt, prf, _, _)) = (nt, prf)
  | dest_thm_axm (PAxm (n, _, _)) = ((n, []), MinProof ([], [], []))
  | dest_thm_axm _ = (("", []), MinProof ([], [], []))

fun get_axioms (AbsP (_, _, prf)) = get_axioms prf
  | get_axioms (Abst (_, _, prf)) = get_axioms prf
  | get_axioms (prf1 %% prf2) = get_axioms prf1 @ get_axioms prf2
  | get_axioms (prf % _) = get_axioms prf
  | get_axioms (MinProof (thms, axms, _)) = 
      List.concat (map (get_axioms o Proofterm.proof_of_min_thm) thms) @
      List.concat (map (get_axioms o Proofterm.proof_of_min_axm) axms) 
  | get_axioms prf = 
      let val ((name, tags), prf') = dest_thm_axm prf
      in
         if axname name mem (!thmlist) then  name :: get_axioms prf' else []
      end


fun record1 name = 
  let val thy = the_context ()
      val thms = PureThy.thms_of thy
  in if name mem (map (axname o fst) thms) then
     let
      val t = thm name
      val p = Thm.proof_of t
      val _ = writeln (Int.toString (length axs))
      val txt = foldl (fn (s,t) => s^"\n"^t) "" axs
      val filename = Context.theory_name thy^"_"^name
     in
        File.write (Path.basic filename) txt
     end
     else ()
  end

fun record name =
    record1 name handle _ => ()

fun initialize l = (thmlist := l)

end;

proofs:=1;
