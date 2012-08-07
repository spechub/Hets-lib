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

consts
eqH :: "('a::Eq) => 'a => bool"
neqH :: "('a::Eq) => 'a => bool"

defs
eqH_def: "eqH x y == x = y"
neqH_def: "neqH x y == ~(x = y)"

(*
 Maybe give definitions obtained through class Num?
*)
consts 
addH   :: "'a::Num => 'a => 'a"
diffH  :: "'a::Num => 'a => 'a"
prodH   :: "'a::Num => 'a => 'a"
negateH :: "'a::Num => 'a"
absH    :: "'a::Num => 'a"
signumH :: "'a::Num => 'a"
fromIntegerH :: "int => 'a::Num"
zeroH        :: "'a::Num"
oneH         :: "'a::Num"
twoH         :: "'a::Num"

consts
eqHI :: "('a::Eq) => 'a => bool"
neqHI :: "('a::Eq) => 'a => bool"
failDF :: "string => 'a"
mbbind :: "'a => 'b => 'b"

end
