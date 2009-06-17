theory Nat_monadic
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"ga_selector_pre\", \"ga_injective_suc\", \"ga_disjoint_0_suc\",
     \"ga_selector_undef_pre_0\", \"X1_def_Nat\", \"X2_def_Nat\",
     \"X4_def_Nat\", \"X5_def_Nat\", \"X6_def_Nat\", \"X7_def_Nat\",
     \"X8_def_Nat\", \"X9_def_Nat\", \"decimal_def\",
     \"ga_comm___XPlus__\", \"ga_assoc___XPlus__\",
     \"ga_right_unit___XPlus__\", \"ga_left_unit___XPlus__\",
     \"ga_left_comm___XPlus__\", \"ga_comm___Xx__\",
     \"ga_assoc___Xx__\", \"ga_right_unit___Xx__\",
     \"ga_left_unit___Xx__\", \"ga_left_comm___Xx__\", \"ga_comm_min\",
     \"ga_assoc_min\", \"ga_left_comm_min\", \"ga_comm_max\",
     \"ga_assoc_max\", \"ga_right_unit_max\", \"ga_left_unit_max\",
     \"ga_left_comm_max\", \"leq_def1_Nat\", \"dvd_def_Nat\",
     \"leq_def2_Nat\", \"leq_def3_Nat\", \"geq_def_Nat\",
     \"less_def_Nat\", \"greater_def_Nat\", \"even_0_Nat\",
     \"even_suc_Nat\", \"odd_def_Nat\", \"factorial_0\",
     \"factorial_suc\", \"add_0_Nat\", \"add_suc_Nat\", \"mult_0_Nat\",
     \"mult_suc_Nat\", \"power_0_Nat\", \"power_suc_Nat\",
     \"min_def_Nat\", \"max_def_Nat\", \"subTotal_def1_Nat\",
     \"subTotal_def2_Nat\", \"sub_dom_Nat\", \"sub_def_Nat\",
     \"divide_dom_Nat\", \"divide_0_Nat\", \"divide_Nat_Nat\",
     \"div_dom_Nat\", \"div_Nat\", \"mod_dom_Nat\", \"mod_Nat\",
     \"distr1_Nat\", \"distr2_Nat\", \"min_0\", \"div_mod_Nat\",
     \"power_Nat\"]"

datatype X_Nat = X0 ("0''") | X_suc "X_Nat" ("suc/'(_')" [3] 999)

consts
X1 :: "X_Nat" ("1''")
X2 :: "X_Nat" ("2''")
X3 :: "X_Nat" ("3''")
X4 :: "X_Nat" ("4''")
X5 :: "X_Nat" ("5''")
X6 :: "X_Nat" ("6''")
X7 :: "X_Nat" ("7''")
X8 :: "X_Nat" ("8''")
X9 :: "X_Nat" ("9''")
X__XAtXAt__X :: "X_Nat => X_Nat => X_Nat" ("(_/ @@/ _)" [54,54] 52)
X__XCaret__X :: "X_Nat => X_Nat => X_Nat" ("(_/ ^''/ _)" [54,54] 52)
X__XExclam :: "X_Nat => X_Nat" ("(_/ !'')" [58] 58)
X__XGtXEq__X :: "X_Nat => X_Nat => bool" ("(_/ >=''/ _)" [44,44] 42)
X__XGt__X :: "X_Nat => X_Nat => bool" ("(_/ >''/ _)" [44,44] 42)
X__XLtXEq__X :: "X_Nat => X_Nat => bool" ("(_/ <=''/ _)" [44,44] 42)
X__XLt__X :: "X_Nat => X_Nat => bool" ("(_/ <''/ _)" [44,44] 42)
X__XMinusXExclam__X :: "X_Nat => X_Nat => X_Nat" ("(_/ -!/ _)" [54,54] 52)
X__XMinusXQuest__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ -?/ _)" [54,54] 52)
X__XPlus__X :: "X_Nat => X_Nat => X_Nat" ("(_/ +''/ _)" [54,54] 52)
X__XSlashXQuest__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ '/?/ _)" [54,54] 52)
X__Xx__X :: "X_Nat => X_Nat => X_Nat" ("(_/ *''/ _)" [54,54] 52)
X__div__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ div''/ _)" [54,54] 52)
X__dvd__X :: "X_Nat => X_Nat => bool" ("(_/ dvd''/ _)" [44,44] 42)
X__mod__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ mod''/ _)" [54,54] 52)
X_even :: "X_Nat => bool" ("even''/'(_')" [3] 999)
X_max :: "X_Nat => X_Nat => X_Nat" ("max''/'(_,/ _')" [3,3] 999)
X_min :: "X_Nat => X_Nat => X_Nat" ("min''/'(_,/ _')" [3,3] 999)
X_odd :: "X_Nat => bool" ("odd''/'(_')" [3] 999)
X_pre :: "X_Nat => X_Nat partial" ("pre/'(_')" [3] 999)

axioms
ga_selector_pre [rule_format] :
"ALL XX1. pre(suc(XX1)) = makePartial XX1"

ga_injective_suc [rule_format] :
"ALL XX1. ALL Y1. suc(XX1) = suc(Y1) = (XX1 = Y1)"

ga_disjoint_0_suc [rule_format] : "ALL Y1. ~ 0' = suc(Y1)"

ga_selector_undef_pre_0 [rule_format] : "~ defOp (pre(0'))"

X1_def_Nat [rule_format] : "1' = suc(0')"

X2_def_Nat [rule_format] : "2' = suc(1')"

X4_def_Nat [rule_format] : "4' = suc(3')"

X5_def_Nat [rule_format] : "5' = suc(4')"

X6_def_Nat [rule_format] : "6' = suc(5')"

X7_def_Nat [rule_format] : "7' = suc(6')"

X8_def_Nat [rule_format] : "8' = suc(7')"

X9_def_Nat [rule_format] : "9' = suc(8')"

decimal_def [rule_format] :
"ALL m. ALL X_n. m @@ X_n = (m *' suc(9')) +' X_n"

ga_comm___XPlus__ [rule_format] : "ALL x. ALL y. x +' y = y +' x"

ga_assoc___XPlus__ [rule_format] :
"ALL x. ALL y. ALL z. (x +' y) +' z = x +' (y +' z)"

ga_right_unit___XPlus__ [rule_format] : "ALL x. x +' 0' = x"

ga_left_unit___XPlus__ [rule_format] : "ALL x. 0' +' x = x"

ga_left_comm___XPlus__ [rule_format] :
"ALL x. ALL y. ALL z. x +' (y +' z) = y +' (x +' z)"

ga_comm___Xx__ [rule_format] : "ALL x. ALL y. x *' y = y *' x"

ga_assoc___Xx__ [rule_format] :
"ALL x. ALL y. ALL z. (x *' y) *' z = x *' (y *' z)"

ga_right_unit___Xx__ [rule_format] : "ALL x. x *' 1' = x"

ga_left_unit___Xx__ [rule_format] : "ALL x. 1' *' x = x"

ga_left_comm___Xx__ [rule_format] :
"ALL x. ALL y. ALL z. x *' (y *' z) = y *' (x *' z)"

ga_comm_min [rule_format] : "ALL x. ALL y. min'(x, y) = min'(y, x)"

ga_assoc_min [rule_format] :
"ALL x. ALL y. ALL z. min'(min'(x, y), z) = min'(x, min'(y, z))"

ga_left_comm_min [rule_format] :
"ALL x. ALL y. ALL z. min'(x, min'(y, z)) = min'(y, min'(x, z))"

ga_comm_max [rule_format] : "ALL x. ALL y. max'(x, y) = max'(y, x)"

ga_assoc_max [rule_format] :
"ALL x. ALL y. ALL z. max'(max'(x, y), z) = max'(x, max'(y, z))"

ga_right_unit_max [rule_format] : "ALL x. max'(x, 0') = x"

ga_left_unit_max [rule_format] : "ALL x. max'(0', x) = x"

ga_left_comm_max [rule_format] :
"ALL x. ALL y. ALL z. max'(x, max'(y, z)) = max'(y, max'(x, z))"

leq_def1_Nat [rule_format] : "ALL X_n. 0' <=' X_n"

dvd_def_Nat [rule_format] :
"ALL m. ALL X_n. (m dvd' X_n) = (EX k. X_n = m *' k)"

leq_def2_Nat [rule_format] : "ALL X_n. ~ suc(X_n) <=' 0'"

leq_def3_Nat [rule_format] :
"ALL m. ALL X_n. (suc(m) <=' suc(X_n)) = (m <=' X_n)"

geq_def_Nat [rule_format] :
"ALL m. ALL X_n. (m >=' X_n) = (X_n <=' m)"

less_def_Nat [rule_format] :
"ALL m. ALL X_n. (m <' X_n) = (m <=' X_n & ~ m = X_n)"

greater_def_Nat [rule_format] :
"ALL m. ALL X_n. (m >' X_n) = (X_n <' m)"

even_0_Nat [rule_format] : "even'(0')"

even_suc_Nat [rule_format] : "ALL m. even'(suc(m)) = odd'(m)"

odd_def_Nat [rule_format] : "ALL m. odd'(m) = (~ even'(m))"

factorial_0 [rule_format] : "0' !' = 1'"

factorial_suc [rule_format] :
"ALL X_n. suc(X_n) !' = suc(X_n) *' X_n !'"

add_0_Nat [rule_format] : "ALL m. 0' +' m = m"

add_suc_Nat [rule_format] :
"ALL m. ALL X_n. suc(X_n) +' m = suc(X_n +' m)"

mult_0_Nat [rule_format] : "ALL m. 0' *' m = 0'"

mult_suc_Nat [rule_format] :
"ALL m. ALL X_n. suc(X_n) *' m = (X_n *' m) +' m"

power_0_Nat [rule_format] : "ALL m. m ^' 0' = 1'"

power_suc_Nat [rule_format] :
"ALL m. ALL X_n. m ^' suc(X_n) = m *' (m ^' X_n)"

min_def_Nat [rule_format] :
"ALL m. ALL X_n. min'(m, X_n) = (if m <=' X_n then m else X_n)"

max_def_Nat [rule_format] :
"ALL m. ALL X_n. max'(m, X_n) = (if m <=' X_n then X_n else m)"

subTotal_def1_Nat [rule_format] :
"ALL m. ALL X_n. m >' X_n --> X_n -! m = 0'"

subTotal_def2_Nat [rule_format] :
"ALL m. ALL X_n. m <=' X_n --> makePartial (X_n -! m) = X_n -? m"

sub_dom_Nat [rule_format] :
"ALL m. ALL X_n. defOp (m -? X_n) = (m >=' X_n)"

sub_def_Nat [rule_format] :
"ALL m. ALL X_n. ALL r. m -? X_n = makePartial r = (m = r +' X_n)"

divide_dom_Nat [rule_format] :
"ALL m.
 ALL X_n.
 defOp (m /? X_n) = (~ X_n = 0' & m mod' X_n = makePartial 0')"

divide_0_Nat [rule_format] : "ALL m. ~ defOp (m /? 0')"

divide_Nat_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ALL r. X_n >' 0' --> m /? X_n = makePartial r = (m = r *' X_n)"

div_dom_Nat [rule_format] :
"ALL m. ALL X_n. defOp (m div' X_n) = (~ X_n = 0')"

div_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 m div' X_n = makePartial r =
 (EX s. m = (X_n *' r) +' s & s <' X_n)"

mod_dom_Nat [rule_format] :
"ALL m. ALL X_n. defOp (m mod' X_n) = (~ X_n = 0')"

mod_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ALL s.
 m mod' X_n = makePartial s =
 (EX r. m = (X_n *' r) +' s & s <' X_n)"

distr1_Nat [rule_format] :
"ALL r. ALL s. ALL t. (r +' s) *' t = (r *' t) +' (s *' t)"

distr2_Nat [rule_format] :
"ALL r. ALL s. ALL t. t *' (r +' s) = (t *' r) +' (t *' s)"

min_0 [rule_format] : "ALL m. min'(m, 0') = 0'"

div_mod_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ~ X_n = 0' -->
 makePartial m =
 lift2partial (flip (mapPartial o X__XPlus__X) (m mod' X_n))
 (mapPartial (flip X__Xx__X X_n) (m div' X_n))"

power_Nat [rule_format] :
"ALL m. ALL r. ALL s. m ^' (r +' s) = (m ^' r) *' (m ^' s)"

declare ga_selector_pre [simp]
declare ga_selector_undef_pre_0 [simp]
declare ga_comm___XPlus__ [simp]
declare ga_assoc___XPlus__ [simp]
declare ga_right_unit___XPlus__ [simp]
declare ga_left_unit___XPlus__ [simp]
declare ga_left_comm___XPlus__ [simp]
declare ga_comm___Xx__ [simp]
declare ga_assoc___Xx__ [simp]
declare ga_right_unit___Xx__ [simp]
declare ga_left_unit___Xx__ [simp]
declare ga_left_comm___Xx__ [simp]
declare ga_comm_min [simp]
declare ga_assoc_min [simp]
declare ga_left_comm_min [simp]
declare ga_comm_max [simp]
declare ga_assoc_max [simp]
declare ga_right_unit_max [simp]
declare ga_left_unit_max [simp]
declare ga_left_comm_max [simp]
declare leq_def1_Nat [simp]
declare dvd_def_Nat [simp]
declare leq_def2_Nat [simp]
declare leq_def3_Nat [simp]
declare geq_def_Nat [simp]
declare less_def_Nat [simp]
declare greater_def_Nat [simp]
declare even_0_Nat [simp]
declare even_suc_Nat [simp]
declare odd_def_Nat [simp]
declare factorial_0 [simp]
declare factorial_suc [simp]
declare add_0_Nat [simp]
declare add_suc_Nat [simp]
declare mult_0_Nat [simp]
declare mult_suc_Nat [simp]
declare power_0_Nat [simp]
declare power_suc_Nat [simp]
declare subTotal_def1_Nat [simp]
declare subTotal_def2_Nat [simp]
declare sub_dom_Nat [simp]
declare divide_0_Nat [simp]
declare min_0 [simp]

end
