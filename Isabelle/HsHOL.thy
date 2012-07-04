theory HsHOL
imports "$ISABELLE_HOME/src/HOL/Complex_Main"
begin

type_synonym 'a maybeT = "'a option"
type_synonym 'a listT  = "'a list"

datatype sOrdering = LT | EQ | GT

class Bounded
class Eq
class Num = Eq
class Ord = Eq
class Enum

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

primrec eqHList where
  "eqHList [] (ys:: ('a::Eq) list) = (ys = [])"
| "eqHList (x#xs) (ys:: ('a::Eq) list) = ((eqH x (hd ys)) & (eqHList xs (tl ys)))" 

defs (overloaded)
list_eqH_def: "eqH (x:: ('a::Eq) list) y == eqHList x y"
bool_eqH_def: "eqH (x::bool) y == x = y" 
bool_neqH_def: "neqH (x::bool) y == ~eqH x y"
int_eqH_def: "eqH (x::int) y == x = y" 
int_neqH_def: "neqH (x::int) y == ~eqH x y"

defs (overloaded)
list_neqH_def: "neqH (x::('a::Eq) list) y == ~eqH x y"

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
