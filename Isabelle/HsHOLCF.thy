theory HsHOLCF
imports HOLCF
begin

types
dInt = "int lift"

axclass Eq < type

consts
hEq :: "('a::Eq) -> 'a -> tr"
hNEq :: "('a::Eq) -> 'a -> tr"

instance bool :: Eq ..
instance int :: Eq ..

instance lift :: (Eq) Eq ..

constdefs
fliftbin ::
"(('a::type) => ('b::type) => ('c::type)) => ('a lift -> 'b lift -> 'c lift)"
"fliftbin f == (LAM y. (LAM x. (((flift1 (%u. (flift2 (%v. f v u))))$x)$y)))"

domain 'a llist = lNil | lCons (lHd ::'a) (lTl ::"'a llist")

instance llist :: ("{Eq,pcpo}") Eq ..

constdefs 
fliftbinA :: 
"(('a::pcpo) => ('b::pcpo) => ('c::type)) => ('a -> 'b -> 'c lift)"
"fliftbinA f == LAM y. (LAM x. (Def (f y x)))"  

defs
tr_hEq_def: "hEq == fliftbinA (% (a::tr) b. a = b)"
dInt_hEq_def: "hEq == fliftbinA (% (a::dInt) b. a = b)"

axioms 
axEq: "ALL x::bool. 
       (hEq $ p $ q = Def x) = (hNEq $ p $ q = Def (~x))"

end
