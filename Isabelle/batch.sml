fun output_theorems : string -> theory -> [string] -> ()
(* Input: file name, theory, list of theorem names
   Functionality: extract theorems (with used axioms) from theory
     write this to file in format that Haskell can read it in
     (see HetCATS/Logic/Prover.hs)
*)
