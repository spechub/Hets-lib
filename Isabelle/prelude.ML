structure Header :
    sig val record : string -> Context.theory -> Context.theory
        val initialize : string list -> Context.theory -> Context.theory
    end =
struct

val thmlist = ref [""];

fun record1 name ctxt =
    let val thm = PureThy.get_thm ctxt name
        val thy = ctxt |> Context.theory_name
        val thm_name = Thm.get_name_hint thm
        fun incl f = String.isPrefix (thy ^ ".") f andalso
              length (filter (fn c => c = ".") (explode f)) = 1 andalso
              thm_name <> f andalso
              List.exists (equal f) (!thmlist)
        fun g (f, _, _) acc = if incl f then f :: acc else acc
        val used_thms = Proofterm.fold_body_thms g [Thm.proof_body_of thm] []
        val txt = List.foldl (fn (s, t) => s ^ "\n" ^ t) "" used_thms
        val filename = thy ^ "_" ^ name ^ ".deps"
    in
        File.write (Path.basic filename) txt;
        ctxt
    end

fun record name ctxt =
    record1 name ctxt handle _ => ctxt

fun initialize l ctxt =
    let val thy = ctxt |> Context.theory_name
    in
        thmlist := map (fn s => thy ^ "." ^ s) l;
        ctxt
    end

end;

proofs := 1;
