structure Header :
    sig val record : string -> unit
        val initialize : string list -> unit
    end =
struct

val thmlist = ref [""];

fun record1 name =
    let val ctxt = OldGoals.the_context ()
        val thm = PureThy.get_thm ctxt name
        val thy = ctxt |> Context.theory_name
        val thm_name = Thm.get_name thm
        fun incl f = String.isPrefix (thy ^ ".") f andalso
              length (filter (fn c => c = ".") (explode f)) = 1 andalso
              thm_name <> f andalso
              f mem (!thmlist)
        fun g (f, _, _) acc = if incl f then f :: acc else acc
        val used_thms = Proofterm.fold_body_thms g [Thm.proof_body_of thm] []
        val txt = foldl (fn (s, t) => s ^ "\n" ^ t) "" used_thms
        val filename = thy ^ "_" ^ name ^ ".deps"
    in
        File.write (Path.basic filename) txt
    end

fun record name =
    record1 name handle _ => ()

fun initialize l =
    let val ctxt = OldGoals.the_context ()
        val thy = ctxt |> Context.theory_name
    in
        thmlist := map (fn s => thy ^ "." ^ s) l
    end

end;

proofs := 1;
