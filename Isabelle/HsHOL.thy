
theory HsHOL = Main:

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

(*
axioms 

ax1: "hEq p p == Some true"

ax2: "[| hEq q r = Some true; hEq p q = Some true|] ==> hEq p r = Some true"

ax3: "hEq p q = Some true == hNEq p q = Some false"
*)

axioms 

ax1: "hEq p p"

ax2: "[| hEq q r; hEq p q |] ==> hEq p r"

ax3: "hEq p q == ~ hNEq p q"

end


(*

types 
 opBool = "bool option"
 opInt = "int option"

constdefs 
opAnd :: "opBool => opBool => opBool"
"opAnd a b == case a of 
   None => None 
   | Some x => case b of 
      None => None 
      | Some y => Some (x & y)"

constdefs
opOr :: "opBool => opBool => opBool"
"opOr a b == case a of 
   None => case b of
      None => None
      | Some y => b
   | Some x => case b of 
      None => a
      | Some y => Some (x | y)"

constdefs
fopbin :: "(('a::type) => ('b::type) => ('c::type)) => ('a option => 'b option => 'c option)"
"fopbin f a b == case a of 
   None => None
   | Some x => case b of 
      None => None
      | Some y => Some (f x y)"

opTrue :: opBool 
"opTrue == Some True"

opFalse :: opBool 
"opFalse == Some False"


end
*)
