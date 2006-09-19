theory HsHOL
imports Main
begin

axclass Eq < type

consts
hEq :: "('a::Eq) => 'a => bool"
hNEq :: "('a::Eq) => 'a => bool"

instance bool :: Eq
by intro_classes
instance list :: ("Eq") Eq
by intro_classes
instance int :: Eq
by intro_classes

defs
tr_hEq_def: "hEq == % (a::bool) b. a = b"
dInt_hEq_def: "hEq == % (a::int) b. a = b"

axioms 
axEq: "hEq p q == ~ hNEq p q"

end
