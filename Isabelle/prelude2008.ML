structure Header :
    sig val record : string -> Context.theory -> Context.theory
        val initialize : string list -> Context.theory -> Context.theory
    end =
struct

open Proofterm

infix mem;

val thmlist = ref [""];
val thyname = ref ""

fun axname s =
   let val (_,an) = take_prefix  (fn x => x <> ".") (explode s)
   in if null an then "" else implode (tl an)
   end

fun get_axioms name =
     let val (l, r) = List.partition (fn s => s mem (!thmlist))
               (filter (fn s => s <> name)
               (filter (fn s => length (filter
                          (fn c => c = ".") (explode s)) < 2)
               (filter (String.isPrefix (!thyname))
                       (Symtab.keys (thms_of_proof
                                    (Thm.proof_of (thm name)) Symtab.empty)))))
     in if null r then l
        else l @ List.concat (map get_axioms r)
     end

fun record name thy =
  let val thms = PureThy.thms_of thy
  in if name mem (map (axname o fst) thms) then
     let
      val axs = map axname (get_axioms (!thyname ^ "." ^ name))
      val txt = foldl (fn (s, t) => s ^ "\n" ^ t) "" axs
      val filename = !thyname ^ "_" ^ name ^ ".deps"
     in
        File.write (Path.basic filename) txt;
        thy
     end
     else thy
  end

fun initialize l ctxt =
    let val thy = Context.theory_name ctxt
    in thmlist := map (fn s => thy ^ "." ^ s) l;
       thyname := thy;
       ctxt
    end

end;

proofs:=1;
