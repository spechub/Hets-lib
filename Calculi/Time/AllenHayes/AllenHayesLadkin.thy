
theory AllenHayesLadkin = BaseAllenHayes:

axioms
M5exist: "!! x :: Interval . !! y :: Interval . 
  M x y ==> ? z :: Interval . ? u :: Interval . ? v :: Interval . 
      M z x & M x y & M y u & M z v & M v u"



(* 
  We show that, given the other axioms of BaseAllenLadkin, the following
  axiom M5var is equivalent to M5exist.
  

M5var: "!! x :: Interval . !! y :: Interval . M x y ==> ? z :: Interval . ! u :: Interval . 
  (M u x = M u z) & (M y u = M z u)"

*)

theorem M5var: "!! x :: Interval . !! y :: Interval . M x y ==> ? z :: Interval . ! u :: Interval . 
  (M u x = M u z) & (M y u = M z u)"
proof -
  fix x y :: Interval
  assume "M x y"
  from this M5exist obtain z u v where A: "M z x & M x y & M y u & M z v & M v u"  by fast 
  moreover
  { fix u0 :: Interval
    from M1 M3 M4 A have  "(M u0 x = M u0 v) & (M y u0 = M v u0)" by blast
  }
  from this have "! u . (M u x = M u v) & (M y u = M v u)" by blast 
  from this show "? z :: Interval . ! u :: Interval . (M u x = M u z) & (M y u = M z u)" by blast
qed

theorem M5exist_proved:  "!! x :: Interval . !! y :: Interval . 
  M x y ==> ? z :: Interval . ? u :: Interval . ? v :: Interval . 
      M z x & M x y & M y u & M z v & M v u"
proof -
  fix x y :: Interval
  assume "M x y"
  from this M3 M4 obtain z u where A: "M z x & M x y & M y u" by blast
  from this M5var obtain v where B: "! u . (M u x = M u v) & (M y u = M v u)" by blast
  from this A B have "M z x & M x y & M y u & M z v & M v u" by blast
  from this show "? z u  v :: Interval . M z x & M x y & M y u & M z v & M v u" by blast
qed
  
    

end
