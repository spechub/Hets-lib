
theory BaseAllenHayes = Main:


(*
  author: Stefan Woelfl
  date:   05-11-2004
  
  Summary: 
  =======
  This thy file contains the basics of Allen and Hayes' first order
  axiomatization of intervals in linear time. 
  We prove that the basic Meet relation ("M") is irreflexiv, asymetric, and
  transitive.
 
  The proofs here are just brute force.
*)



typedecl "Interval"

consts
"M" :: "Interval => Interval => bool"   ( "M" )


axioms
M1: "!! x y z u :: Interval . 
  (M x y & M x u) & M z y ==> M z u"
M2a: "!! x y z u :: Interval . 
  M x y & M z u ==> (M x u | (? v :: Interval . M x v & M v u)) | (? v :: Interval . M z v & M v y)"
M2b: "!! x y z u :: Interval . M x y & M z u & M x u ==> 
  (Not (? v :: Interval . M x v & M v u)) & (Not (? v :: Interval . M z v & M v y))"
M2c: "!! x y z u :: Interval . (M x y & M z u) & (? v :: Interval . M x v & M v u) ==> 
  (Not (M x u)) & (Not (? v :: Interval . M z v & M v y))"
M2d: "!! x y z u :: Interval . (M x y & M z u) & (? v :: Interval . M z v & M v y) ==> 
  (Not (M x u)) & (Not (? v :: Interval . M x v & M v u))"
M3: "!! x :: Interval . ? y :: Interval . ? z :: Interval . M y x & M x z"
M4: "!! x y z u :: Interval . 
  ((M x y & M y u) & M x z) & M z u ==> y = z"



theorem M_irrefl[intro]: "!! x :: Interval . (Not (M x x))"
proof -
  fix x
  from M1 M2a M2b M2c M2d M3 M4
  show "Not(M x x)" by blast
qed


theorem M_asym[intro]: "!! x :: Interval . !! y :: Interval . M x y ==> (Not (M y x))"
proof -
  fix x y
  assume "M x y"
  with M1 M2a M2b M2c M2d M3 M4
  show "(Not (M y x))"
    by blast
qed


theorem M_atrans[intro]: "!! x :: Interval . !! y :: Interval . !! z :: Interval . M x y & M y z ==> (Not (M x z))"
proof -
  fix x y z
  assume " M x y & M y z"
  with M1 M2a M2b M2c M2d M3 M4
  show "Not (M x z)"
    by blast
qed


end
