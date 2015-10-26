theory Basics_SetsWithComprehension_E1
imports "$HETS_LIB/Isabelle/MainHCPairs"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"set_comprehension\", \"abbrev_of_set_comprehension\",
     \"function_image\", \"emptySet_empty\", \"allSet_contains_all\",
     \"def_of_isIn\", \"def_of_subset\", \"def_of_union\",
     \"def_of_bigunion\", \"def_of_intersection\",
     \"def_of_difference\", \"def_of_disjoint\", \"def_of_productset\",
     \"emptySet_union_right_unit\", \"function_image_structure\"]"

typedecl ('a1) Set

consts
XLBrace__XRBrace :: "('S => bool) => 'S => bool"
X__XBslashXBslash__X :: "('S => bool) * ('S => bool) => 'S => bool"
X__Xx__X :: "('S => bool) * ('T => bool) => 'S * 'T => bool"
X__disjoint__X :: "('S => bool) => ('S => bool) => bool" ("(_/ disjoint/ _)" [44,44] 42)
X__intersection__X :: "('S => bool) * ('S => bool) => 'S => bool"
X__isIn__X :: "'S => ('S => bool) => bool" ("(_/ isIn/ _)" [44,44] 42)
X__subset__X :: "('S => bool) => ('S => bool) => bool" ("(_/ subset/ _)" [44,44] 42)
X__union__X :: "('S => bool) * ('S => bool) => 'S => bool"
X_allSet :: "'S => bool" ("allSet/'(_')" [3] 999)
X_emptySet :: "'S => bool" ("emptySet/'(_')" [3] 999)
X_image :: "('S => 'T) * ('S => bool) => 'T => bool"
bigunion :: "(('S => bool) => bool) => 'S => bool"
setFromProperty :: "('S => bool) => 'S => bool"

axioms
set_comprehension [rule_format] : "ALL s. XLBrace__XRBrace s = s"

abbrev_of_set_comprehension [rule_format] :
"setFromProperty = XLBrace__XRBrace"

function_image [rule_format] :
"ALL XX. ALL f. X_image (f, XX) = (% x. EX y. y isIn XX & f y = x)"

emptySet_empty [rule_format] : "ALL x. ~ x isIn X_emptySet"

allSet_contains_all [rule_format] : "ALL x. x isIn X_allSet"

def_of_isIn [rule_format] : "ALL s. ALL x. (x isIn s) = s x"

def_of_subset [rule_format] :
"ALL s. ALL s'. (s subset s') = (ALL x. x isIn s --> x isIn s')"

def_of_union [rule_format] :
"ALL s.
 ALL s'.
 ALL x. (x isIn X__union__X (s, s')) = (x isIn s | x isIn s')"

def_of_bigunion [rule_format] :
"ALL XXXX.
 ALL x. (x isIn bigunion XXXX) = (EX XX. XX isIn XXXX & x isIn XX)"

def_of_intersection [rule_format] :
"ALL s.
 ALL s'.
 ALL x.
 (x isIn X__intersection__X (s, s')) = (x isIn s & x isIn s')"

def_of_difference [rule_format] :
"ALL s.
 ALL s'.
 ALL x.
 (x isIn X__XBslashXBslash__X (s, s')) = (x isIn s & ~ x isIn s')"

def_of_disjoint [rule_format] :
"ALL s.
 ALL s'.
 (s disjoint s') = (X__intersection__X (s, s') = X_emptySet)"

def_of_productset [rule_format] :
"ALL s.
 ALL t.
 ALL x.
 ALL y. ((x, y) isIn X__Xx__X (s, t)) = (x isIn s & y isIn t)"

declare emptySet_empty [simp]
declare allSet_contains_all [simp]
declare def_of_isIn [simp]

theorem emptySet_union_right_unit :
"ALL a. X__union__X (a, X_emptySet) = a"
  by (rule allI, rule set_ext,
  (subst mem_def)+,
    subst def_of_isIn [symmetric], 
    subst def_of_union,
    subst def_of_isIn [symmetric],
    subst not_not [symmetric], subst emptySet_empty, simp)

ML "Header.record \"emptySet_union_right_unit\""

theorem function_image_structure :
"ALL a.
 ALL f. ALL x. (x isIn X_image (f, a)) = (EX y. y isIn a & f y = x)"
unfolding function_image def_of_isIn by simp

ML "Header.record \"function_image_structure\""

end
