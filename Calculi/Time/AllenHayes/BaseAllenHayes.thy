
theory BaseAllenHayes = Main:

ML "val hetsLib = (OS.Process.getEnv \"HETS_LIB\"); 
case hetsLib of NONE => add_path \".\" 
| SOME s => add_path (s ^ \"/Isabelle\")"


ML "proofs := 1"

typedecl "Interval"

consts
"M" :: "Interval => Interval => bool"   ( "M" )


axioms
M1: "!! x :: Interval . !! y :: Interval . !! z :: Interval . !! u :: Interval . (M x y & M x u) & M z y ==> M z u"
M2a: "!! x :: Interval . !! y :: Interval . !! z :: Interval . !! u :: Interval . M x y & M z u ==> (M x u | (? v :: Interval . M x v & M v u)) | (? v :: Interval . M z v & M v y)"
M2b: "!! x :: Interval . !! y :: Interval . !! z :: Interval . !! u :: Interval . (M x y & M z u) & M x u ==> (Not (! v :: Interval . M x v & M v u)) & (Not (? v :: Interval . M z v & M v y))"
M2c: "!! x :: Interval . !! y :: Interval . !! z :: Interval . !! u :: Interval . (M x y & M z u) & (? v :: Interval . M x v & M v u) ==> (Not (M x u)) & (Not (? v :: Interval . M z v & M v y))"
M2d: "!! x :: Interval . !! y :: Interval . !! z :: Interval . !! u :: Interval . (M x y & M z u) & (? v :: Interval . M z v & M v y) ==> (Not (M x u)) & (Not (? v :: Interval . M x v & M v u))"
M3: "!! x :: Interval . ? y :: Interval . ? z :: Interval . M y x & M x z"
M4: "!! x :: Interval . !! y :: Interval . !! z :: Interval . !! u :: Interval . ((M x y & M y u) & M x z) & M z u ==> y = z"



theorem M_irrefl: "! x :: Interval . (Not (M x x))"
proof -
  from M1 M2a M2b M2c M2d M3 M4
  show ?thesis
    by blast
qed


theorem M_asym: "! x :: Interval . ! y :: Interval . M x y --> (Not (M y x))"
proof -
  from M1 M2a M2b M2c M2d M3 M4
  show ?thesis
    by blast
qed


theorem M_atrans: "! x :: Interval . ! y :: Interval . ! z :: Interval . M x y & M y z --> (Not (M x z))"
proof -
  from M1 M2a M2b M2c M2d M3 M4
  show ?thesis
    by blast
qed


end
