theory HsHOL
imports Main
begin

types
unitT  = unit
boolT  = bool
intT   = int 
integerT = int
charT  = char
stringT = string
'a maybeT = "'a option"
'a listT  = "'a list"

axclass Eq < type

instance unit :: Eq ..
instance int :: Eq ..
instance bool :: Eq ..
(* instance rat :: Eq .. *)
instance char :: Eq ..

instance list :: (Eq) Eq ..
instance "*" :: (Eq, Eq) Eq .. 
instance "+" :: (Eq,Eq) Eq .. 
instance option :: (Eq) Eq ..

consts
hEq :: "'a => 'a => bool"
hNEq :: "'a => 'a => bool"

defs
bool_hEq_def: "hEq (x::bool) y == x = y" 
bool_hNEq_def: "hNEq (x::bool) y == ~hEq x y"
int_hEq_def: "hEq (x::int) y == x = y" 
int_hNEq_def: "hNEq (x::int) y == ~hEq x y"

primrec
"hEq [] (ys:: 'a list) = (ys = [])"
"hEq (x#xs) (ys:: 'a list) = ((hEq x (hd ys)) & (hEq xs (tl ys)))" 

defs
list_hNEq_def: "hNEq (x::'a list) y == ~hEq x y"

consts
failDF :: "string => 'a"
mbbind :: "'a => 'b => 'b"

end
