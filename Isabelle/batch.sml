fun output_theorems : string -> theory -> [string] -> ()
(* Input: file name, theory, list of theorem names
   Functionality: extract theorems (with used axioms) from theory
     write this to file in format that Haskell can read it in
     (of type [Proof_status ()], see HetCATS/Logic/Prover.hs)
     use: get_thm, and see p.58 how to extract proof term and p.57
          how to extract used axioms
   Add to thy files the line
   use batch.sml
   ML {* output_theorems "file" theory.thy ["thm1", ... ,"thmn] *}
*)
