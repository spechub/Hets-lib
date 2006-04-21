
theory HsHOLCF = HOLCF:

axclass hskTerm < type

types 
dInt = "int lift"

axclass Ord < type
axclass Eq < type

consts
hEq :: "('a::Eq) -> 'a -> tr"
hNEq :: "('a::Eq) -> 'a -> tr"

instance "->" :: ("hskTerm","hskTerm") hskTerm ..
instance "*" :: ("hskTerm","hskTerm") hskTerm ..

instance bool :: hskTerm
by intro_classes 
instance int :: hskTerm
by intro_classes 
instance bool :: Eq .. 
instance int :: Eq ..

instance lift :: (Eq) Eq .. 
instance lift :: (hskTerm) hskTerm .. 

constdefs 
fliftbin :: "(('a::type) => ('b::type) => ('c::type)) => ('a lift -> 'b lift -> 'c lift)"
"fliftbin f == (LAM y. (LAM x. (((flift1 (%u. (flift2 (%v. f v u))))$x)$y)))"  

(* a type of lazy lists (from Fixrec_ex) *)
domain 'a llist = lNil | lCons (lazy lHd ::'a) (lazy lTl ::"'a llist")

instance llist :: ("{hskTerm,pcpo}") hskTerm ..
instance llist :: ("{Eq,pcpo}") Eq ..

defs
tr_hEq_def: "hEq == LAM (a::tr) b. if (a = UU) | (b = UU) then UU else Def (a = b)"
dInt_hEq_def: "hEq == LAM (a::dInt) b. if (a = UU) | (b = UU) then UU else Def (a = b)"

axioms 

ax1: "hEq $ p $ p == Def true"

ax2: "[| hEq $ q $ r = Def true; hEq $ p $ q = Def true |] ==> 
   hEq $ p $ r = Def true"

ax3: "hEq $ p $ q = Def true == hNEq $ p $ q = Def false"

end
