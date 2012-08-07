theory HsHOL
imports "$ISABELLE_HOME/src/HOL/Complex_Main"
begin

type_synonym 'a maybeT = "'a option"
type_synonym 'a listT  = "'a list"

class Eq = equal
class Num = zero + one + plus + minus + uminus + times + ord + abs + sgn

instance unit :: Eq ..
instance int :: Eq ..
instance bool :: Eq ..
instance rat :: Eq .. 
instance char :: Eq ..
instance int :: Num ..

instance list :: (Eq) Eq ..
instance option :: (Eq) Eq ..

(*
 Maybe give definitions obtained through class Num?
*)
consts 
negateH :: "'a::Num => 'a"
absH    :: "'a::Num => 'a"
signumH :: "'a::Num => 'a"
fromIntegerH :: "int => 'a::Num"

consts
eqHI :: "('a::Eq) => 'a => bool"
neqHI :: "('a::Eq) => 'a => bool"
failDF :: "string => 'a"
mbbind :: "'a => 'b => 'b"

end
