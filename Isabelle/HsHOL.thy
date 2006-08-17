theory HsHOL
imports Main
begin

axclass hskTerm < type

axclass Ord < type
axclass Eq < type

consts
hEq :: "('a::Eq) => 'a => bool"
hNEq :: "('a::Eq) => 'a => bool"

instance "*" :: ("hskTerm","hskTerm") hskTerm ..

instance bool :: hskTerm
by intro_classes
instance int :: hskTerm
by intro_classes
instance bool :: Eq
by intro_classes
instance list :: ("Eq") Eq
by intro_classes
instance int :: Eq
by intro_classes

instance list :: ("hskTerm") hskTerm ..

axioms

ax1: "hEq p p"

ax2: "[| hEq q r; hEq p q |] ==> hEq p r"

ax3: "hEq p q == ~ hNEq p q"

end
