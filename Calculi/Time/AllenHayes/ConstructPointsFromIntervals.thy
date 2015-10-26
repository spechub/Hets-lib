
theory ConstructPointsFromIntervals = AllenHayesLadkin:

(*
  author: Stefan Woelfl
  date:   05-11-2004
  
  Summary: 
     This thy file contains the basics of Ladkin's method of how 
     to construct instants from intervals. 
 
*)


consts
"Equiv" :: "Interval => Interval => Interval => Interval => bool"   ( "Equiv" )
"PointLess" :: "Interval => Interval => Interval => Interval => bool"   ( "PointLess" )


axioms
Equiv_def: "!! x :: Interval . !! y :: Interval . !! z :: Interval . !! u :: Interval . 
  Equiv x y z u = (M x y & M z u & M x u)"
PointLess_def: "!! x :: Interval . !! y :: Interval . !! z :: Interval . !! u :: Interval . 
  PointLess x y z u = (? r :: Interval . ? s :: Interval . ? t :: Interval . Equiv x y r s & Equiv z u s t)"


declare Equiv_def[iff]
declare PointLess_def[iff]



theorem Equiv_refl[elim]: "!! x :: Interval . !! y :: Interval . M x y ==> Equiv x y x y"
proof -
  fix x y 
  assume "M x y"
  thus "Equiv x y x y" by blast
qed

theorem Equiv_sym[sym]: "!! x :: Interval . !! y :: Interval . !! z :: Interval . !! u :: Interval . 
  Equiv x y z u ==> Equiv z u x y"
proof -
  fix x y z u
  assume  "Equiv x y z u"
  with M1 M2a M2b M2c M2d M3 M4
    show "Equiv z u x y"
    by blast
qed

theorem Equiv_trans[trans]: "!! x y z u v w :: Interval .  
  (* (M x y & M z u & M v w) --> *)
  Equiv x y z u & Equiv z u v w ==> Equiv x y v w"
proof -
  fix  x y z u v w
  assume "Equiv x y z u & Equiv z u v w"
  with M1 M2a M2b M2c M2d M3 M4
  show "Equiv x y v w"
    by blast
qed


theorem PointLess_irrefl: "!! x :: Interval . !! y :: Interval . 
  M x y ==> Not (PointLess x y x y)"
proof -
  fix x y
  assume "M x y"
  with M1 M2a M2b M2c M2d M3 M4
  show "Not (PointLess x y x y)"
    by blast
qed


(* ML "set Blast.trace"; *)

theorem PointLess_trans[trans]: "!! x y z u v w :: Interval .  
  PointLess x y z u & PointLess z u v w ==> PointLess x y v w"
proof -
  fix x y z u v w
  assume A: "PointLess x y z u & PointLess z u v w"
  from A obtain r1 s1 t1 where B: "Equiv x y r1 s1 & Equiv z u s1 t1" by blast
  from A obtain r2 s2 t2 where C: "Equiv z u r2 s2 & Equiv v w s2 t2" by blast
  from B C  M1 have "M s1 s2" by blast
  from M5var this obtain s1s2 where "! u . (M u s1 = M u s1s2) & (M s2 u = M s1s2 u)" by blast
  from B C M1 this have "M r1 s1s2 & M s1s2 t2" by blast 
  from this B C M1 have "Equiv x y r1 s1s2 & Equiv v w s1s2 t2" by blast
 from this show "PointLess x y v w" by blast
qed



theorem PointLess_linear[intro]: "!! x y z u :: Interval .
  M x y & M z u ==> PointLess x y z u | Equiv x y z u | PointLess z u x y"
proof -
  fix x y z u
  assume A: "M x y & M z u"
  from this M2a have "M x u | (EX v. M x v & M v u) | (EX v. M z v & M v y)" by blast
  moreover
  { assume "M x u"
    from this A M1 M3 M4 have "Equiv x y z u" by blast
  }
  moreover
  { assume "EX v. M x v & M v u"
    from this A M1 M3 M4 have "PointLess x y z u" by blast
  } 
  moreover
  { assume "EX v. M z v & M v y"
    from this A M1 M3 M4 have "PointLess z u x y" by blast
  }
    (* by (tactic{*Blast.depth_tac (claset ()) 25 1*}) *)
  ultimately show "PointLess x y z u | Equiv x y z u | PointLess z u x y" by blast 
qed



end
