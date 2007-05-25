theory HsHOL
imports Main
begin

consts
hEq :: "'a => 'a => bool"
hNEq :: "'a => 'a => bool"

axclass Eq < type
  axEq: "hEq p q == ~ hNEq p q"

defs
bool_hEq_def: "hEq (x::bool) y == x = y" 
bool_hNEq_def: "hNEq (x::bool) y == ~hEq x y"

instance bool :: Eq
apply (intro_classes, unfold bool_hEq_def bool_hNEq_def)
apply auto
done

defs
int_hEq_def: "hEq (x::int) y == x = y" 
defs
int_hNEq_def: "hNEq (x::int) y == ~hEq x y"

instance int :: Eq
apply (intro_classes, unfold int_hEq_def int_hNEq_def)
apply auto
done

primrec
"hEq [] (ys:: 'a list) = (ys = [])"
"hEq (x#xs) (ys:: 'a list) = ((hEq x (hd ys)) & (hEq xs (tl ys)))" 

defs
list_hNEq_def: "hNEq (x::'a list) y == ~hEq x y"

instance list :: ("Eq") Eq
apply (intro_classes, unfold list_hNEq_def)
apply auto
done

end
