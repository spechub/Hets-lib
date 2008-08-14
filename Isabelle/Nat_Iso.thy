theory Nat_Iso
imports "$HETS_LIB/Isabelle/Ext_Nat"
uses "$HETS_LIB/Isabelle/prelude"
begin

typedecl Pos

datatype Nat = X0 ("0''") | sucX1 "Nat" ("suc''/'(_')" [3] 999)

consts
X1X1 :: "Nat" ("1''")
X1X2 :: "Pos" ("1''''")
X2 :: "Nat" ("2''")
X3 :: "Nat" ("3''")
X4 :: "Nat" ("4''")
X5 :: "Nat" ("5''")
X6 :: "Nat" ("6''")
X7 :: "Nat" ("7''")
X8 :: "Nat" ("8''")
X9 :: "Nat" ("9''")
X__XAtXAt__X :: "Nat => Nat => Nat" ("(_/ @@/ _)" [54,54] 52)
X__XCaret__X :: "Nat => Nat => Nat" ("(_/ ^''/ _)" [54,54] 52)
X__XExclam :: "Nat => Nat" ("(_/ !'')" [58] 58)
X__XGtXEq__X :: "Nat => Nat => bool" ("(_/ >=''/ _)" [44,44] 42)
X__XGt__X :: "Nat => Nat => bool" ("(_/ >''/ _)" [44,44] 42)
X__XLtXEq__X :: "Nat => Nat => bool" ("(_/ <=''/ _)" [44,44] 42)
X__XLt__X :: "Nat => Nat => bool" ("(_/ <''/ _)" [44,44] 42)
X__XMinusXExclam__X :: "Nat => Nat => Nat" ("(_/ -!/ _)" [54,54] 52)
X__XMinusXQuest__X :: "Nat => Nat => Nat option" ("(_/ -?/ _)" [54,54] 52)
X__XPlus__XX1 :: "Nat => Nat => Nat" ("(_/ +''/ _)" [54,54] 52)
X__XPlus__XX2 :: "Nat => Pos => Pos" ("(_/ +''''/ _)" [54,54] 52)
X__XPlus__XX3 :: "Pos => Nat => Pos" ("(_/ +'_3/ _)" [54,54] 52)
X__XSlashXQuest__X :: "Nat => Nat => Nat option" ("(_/ '/?/ _)" [54,54] 52)
X__Xx__XX1 :: "Nat => Nat => Nat" ("(_/ *''/ _)" [54,54] 52)
X__Xx__XX2 :: "Pos => Pos => Pos" ("(_/ *''''/ _)" [54,54] 52)
X__div__X :: "Nat => Nat => Nat option" ("(_/ div''/ _)" [54,54] 52)
X__mod__X :: "Nat => Nat => Nat option" ("(_/ mod''/ _)" [54,54] 52)
X_even :: "Nat => bool" ("even''/'(_')" [3] 999)
X_gn_inj_Pos_Nat :: "Pos => Nat" ("gn'_inj'_Pos'_Nat/'(_')" [3] 999)
X_gn_proj_Nat_Pos :: "Nat => Pos option" ("gn'_proj'_Nat'_Pos/'(_')" [3] 999)
X_max :: "Nat => Nat => Nat" ("max''/'(_,/ _')" [3,3] 999)
X_min :: "Nat => Nat => Nat" ("min''/'(_,/ _')" [3,3] 999)
X_odd :: "Nat => bool" ("odd''/'(_')" [3] 999)
X_pre :: "Nat => Nat option" ("pre/'(_')" [3] 999)
sucX2 :: "Nat => Pos" ("suc''''/'(_')" [3] 999)
X_dvd :: "Nat => Nat => bool" ("(_/ dvd''/ _)" [54,54] 52)

instance Nat:: type ..
instance Pos:: type ..

section "Nat axioms"

axioms
dvd_Nat [rule_format] : "ALL (m::Nat) (n::Nat) . (m dvd' n) = (EX k . n = m *' k)"

ga_function_monotonicity [rule_format] : "1' = gn_inj_Pos_Nat(1'')"

ga_function_monotonicity_1 [rule_format] :
"ALL x1.
 ALL x2.
 gn_inj_Pos_Nat(x1) *' gn_inj_Pos_Nat(x2) =
 gn_inj_Pos_Nat(x1 *'' x2)"

ga_function_monotonicity_2 [rule_format] :
"ALL x1.
 ALL x2. x1 +' gn_inj_Pos_Nat(x2) = gn_inj_Pos_Nat(x1 +'' x2)"

ga_function_monotonicity_3 [rule_format] :
"ALL x1.
 ALL x2. gn_inj_Pos_Nat(x1) +' x2 = gn_inj_Pos_Nat(x1 +_3 x2)"

ga_function_monotonicity_4 [rule_format] :
"ALL x1.
 ALL x2. gn_inj_Pos_Nat(x1) +'' x2 = x1 +_3 gn_inj_Pos_Nat(x2)"

ga_function_monotonicity_5 [rule_format] :
"ALL x1. suc'(x1) = gn_inj_Pos_Nat(suc''(x1))"

ga_embedding_injectivity [rule_format] :
"ALL x. ALL y. gn_inj_Pos_Nat(x) = gn_inj_Pos_Nat(y) --> x = y"

ga_projection_injectivity [rule_format] :
"ALL x.
 ALL y.
 exEqualOp (gn_proj_Nat_Pos(x), gn_proj_Nat_Pos(y)) --> x = y"

ga_projection [rule_format] :
"ALL x. gn_proj_Nat_Pos(gn_inj_Pos_Nat(x)) = Some x"

ga_selector_pre [rule_format] :
"ALL XX1. pre(suc'(XX1)) = Some XX1"

ga_injective_suc [rule_format] :
"ALL XX1. ALL Y1. suc'(XX1) = suc'(Y1) = (XX1 = Y1)"

ga_disjoint_0_suc [rule_format] : "ALL Y1. ~ 0' = suc'(Y1)"

ga_selector_undef_pre_0 [rule_format] : "~ defOp (pre(0'))"

X1_def_Nat [rule_format] : "1' = suc'(0')"

X2_def_Nat [rule_format] : "2' = suc'(1')"

X3_def_Nat [rule_format] : "3' = suc'(2')"

X4_def_Nat [rule_format] : "4' = suc'(3')"

X5_def_Nat [rule_format] : "5' = suc'(4')"

X6_def_Nat [rule_format] : "6' = suc'(5')"

X7_def_Nat [rule_format] : "7' = suc'(6')"

X8_def_Nat [rule_format] : "8' = suc'(7')"

X9_def_Nat [rule_format] : "9' = suc'(8')"

decimal_def [rule_format] :
"ALL m. ALL X_n. m @@ X_n = (m *' suc'(9')) +' X_n"

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

leq_def2_Nat [rule_format] : "ALL X_n. ~ suc'(X_n) <=' 0'"

leq_def3_Nat [rule_format] :
"ALL m. ALL X_n. (suc'(m) <=' suc'(X_n)) = (m <=' X_n)"

geq_def_Nat [rule_format] :
"ALL m. ALL X_n. (m >=' X_n) = (X_n <=' m)"

less_def_Nat [rule_format] :
"ALL m. ALL X_n. (m <' X_n) = (m <=' X_n & ~ m = X_n)"

greater_def_Nat [rule_format] :
"ALL m. ALL X_n. (m >' X_n) = (X_n <' m)"

even_0_Nat [rule_format] : "even'(0')"

even_suc_Nat [rule_format] : "ALL m. even'(suc'(m)) = odd'(m)"

odd_def_Nat [rule_format] : "ALL m. odd'(m) = (~ even'(m))"

factorial_0 [rule_format] : "0' !' = 1'"

factorial_suc [rule_format] :
"ALL X_n. suc'(X_n) !' = suc'(X_n) *' X_n !'"

add_0_Nat [rule_format] : "ALL m. 0' +' m = m"

add_suc_Nat [rule_format] :
"ALL m. ALL X_n. suc'(X_n) +' m = suc'(X_n +' m)"

mult_0_Nat [rule_format] : "ALL m. 0' *' m = 0'"

mult_suc_Nat [rule_format] :
"ALL m. ALL X_n. suc'(X_n) *' m = (X_n *' m) +' m"

power_0_Nat [rule_format] : "ALL m. m ^' 0' = 1'"

power_suc_Nat [rule_format] :
"ALL m. ALL X_n. m ^' suc'(X_n) = m *' (m ^' X_n)"

min_def_Nat [rule_format] :
"ALL m. ALL X_n. min'(m, X_n) = (if m <=' X_n then m else X_n)"

max_def_Nat [rule_format] :
"ALL m. ALL X_n. max'(m, X_n) = (if m <=' X_n then X_n else m)"

subTotal_def1_Nat [rule_format] :
"ALL m. ALL X_n. m >' X_n --> X_n -! m = 0'"

subTotal_def2_Nat [rule_format] :
"ALL m. ALL X_n. m <=' X_n --> Some (X_n -! m) = X_n -? m"

sub_dom_Nat [rule_format] :
"ALL m. ALL X_n. defOp (m -? X_n) = (m >=' X_n)"

sub_def_Nat [rule_format] :
"ALL m. ALL X_n. ALL r. m -? X_n = Some r = (m = r +' X_n)"

divide_dom_Nat [rule_format] :
"ALL m.
 ALL X_n. defOp (m /? X_n) = (~ X_n = 0' & m mod' X_n = Some 0')"

divide_0_Nat [rule_format] : "ALL m. ~ defOp (m /? 0')"

divide_Pos_Nat [rule_format] :
"ALL m.
 ALL X_n. ALL r. X_n >' 0' --> m /? X_n = Some r = (m = r *' X_n)"

div_dom_Nat [rule_format] :
"ALL m. ALL X_n. defOp (m div' X_n) = (~ X_n = 0')"

div_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 m div' X_n = Some r = (EX s. m = (X_n *' r) +' s & s <' X_n)"

mod_dom_Nat [rule_format] :
"ALL m. ALL X_n. defOp (m mod' X_n) = (~ X_n = 0')"

mod_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ALL s.
 m mod' X_n = Some s = (EX r. m = (X_n *' r) +' s & s <' X_n)"

distr1_Nat [rule_format] :
"ALL r. ALL s. ALL t. (r +' s) *' t = (r *' t) +' (s *' t)"

distr2_Nat [rule_format] :
"ALL r. ALL s. ALL t. t *' (r +' s) = (t *' r) +' (t *' s)"

Pos_def [rule_format] :
"ALL p. defOp (gn_proj_Nat_Pos(p)) = (p >' 0')"

X1_as_Pos_def [rule_format] : "1'' = suc''(0')"

declare even_0_Nat [simp]
declare even_suc_Nat [simp]
declare odd_def_Nat [simp]
declare ga_projection [simp]
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
declare leq_def2_Nat [simp]
declare leq_def3_Nat [simp]
declare even_0_Nat [simp]
declare even_suc_Nat [simp]
declare factorial_0 [simp]
declare add_0_Nat [simp]
declare mult_0_Nat [simp]
declare power_0_Nat [simp]
declare subTotal_def1_Nat [simp]
declare subTotal_def2_Nat [simp]
declare divide_0_Nat [simp]


section "Definition of the Isomorphism"

consts Nat2nat :: "Nat => nat"
consts nat2Nat :: "nat => Nat"

primrec
"Nat2nat  0' = 0 "
"Nat2nat  (suc'(x)) = Suc (Nat2nat x)"

primrec 
"nat2Nat 0 = 0'"
"nat2Nat (Suc x) = suc' (nat2Nat x)"

lemma iso1 [simp] : "! x . nat2Nat(Nat2nat x) = x"
by(auto, induct_tac x, auto)

lemma iso2 [simp] : "! x . Nat2nat(nat2Nat x) = x"
by (auto, induct_tac x, auto)

lemma left_unit [simp] : "! a. 0' +' a = a"
by (auto simp add: ga_left_unit___XPlus__)

lemma right_unit [simp] : "! a . a +' 0' = a"
by (auto simp add: ga_right_unit___XPlus__)

lemma suc : "! x . x +' 1' = suc'(x)"
apply (subst ga_comm___XPlus__)
apply (subst X1_def_Nat)
apply (subst add_suc_Nat)
by (auto)

section "Injectivity"

lemma diff_induct_Nat : "(!!(x::Nat). P x 0') ==> 
  (!!(y::Nat). P (0'::Nat) (suc'(y))) ==>
  (!!(x ::Nat) (y::Nat). P x y ==> P (suc'(x)) (suc' (y))) ==> P m n"
  apply (rule_tac x = m in spec)
  apply (induct n)
  prefer 2
  apply (rule allI)
  apply (induct_tac x, iprover+)
  done

theorem nat2Nat_inj [rule_format] : "!! x y . nat2Nat(x) = nat2Nat(y) --> x = y"
apply (rule diff_induct)
apply (auto)
apply (drule_tac f="% x . Nat2nat(x)" in arg_cong)
by (auto)

theorem Nat2nat_inj [rule_format] : "!! x y . Nat2nat(x) = Nat2nat(y) --> x = y"
apply (rule diff_induct_Nat)
apply (auto)
apply (drule_tac f="% x . nat2Nat(x)" in arg_cong)
by (auto)

theorem nat2Nat_wd [rule_format] : "!! x y . x = y --> nat2Nat(x) = nat2Nat(y)"
apply (rule diff_induct)
by (auto)

theorem Nat2nat_wd [rule_format] : "!! x y . x = y --> Nat2nat(x) = Nat2nat(y)"
apply (rule diff_induct_Nat)
by (auto)

section "Commutes with suc/pre"

theorem suc_1 [simp] : "! x . nat2Nat (Suc x) = suc' (nat2Nat x)"
by (auto)

theorem suc_2 [simp] : "! x . (Nat2nat (suc'(x))) = (Suc (Nat2nat x))"
by (auto)

lemma zero_Map : "0' = nat2Nat 0"
by (auto)

lemma zero_map : "0 = Nat2nat 0'"
by (auto)

theorem pre_1 [simp] : "!!x z . x > 0 --> (pre_nat x = Some z) =  (Some (nat2Nat z) = (pre (nat2Nat x)))"
apply (induct_tac x)
apply (auto)
apply (subst (asm) zero_Map)
apply (drule_tac f="Nat2nat" in arg_cong)
apply (force)
apply (rule sym)
apply (drule_tac f="Nat2nat" in arg_cong)
apply (force)
apply (rule sym)
apply (drule_tac f="Nat2nat" in arg_cong)
by (force)

theorem pre_2 [simp] : "!!x z . x >' 0' -->( (pre(x) = Some z) = (Some (Nat2nat z) = pre_nat (Nat2nat x)))"
apply (induct_tac x)
apply (auto simp add: greater_def_Nat less_def_Nat)
apply (subst (asm) zero_map[rule_format])
apply (drule_tac f="nat2Nat" in arg_cong)
apply (force)
apply (drule_tac f="nat2Nat" in arg_cong)
apply (force)
apply (drule_tac f="nat2Nat" in arg_cong)
by (force)

section "Commutes with addition"

theorem add1 [simp] : "! x . ! y . nat2Nat (x + y) = (nat2Nat x) +' (nat2Nat y)"
apply (auto)
apply (rule nat2Nat.induct)
apply (auto simp add: X1_def_Nat)
apply (subst suc [rule_format, THEN sym])
apply (subst suc [rule_format, THEN sym])
by (simp add: ga_assoc___XPlus__)

theorem add2 [simp] : "!x . ! y. Nat2nat (x +' y) = (Nat2nat x) + (Nat2nat y)"
apply (auto)
apply (rule Nat2nat.induct)
apply (auto)
apply (subst ga_comm___XPlus__)
apply (auto simp add: add_suc_Nat)
apply (subst ga_comm___XPlus__)
apply (subst add_suc_Nat)
by (auto)

lemma zero_minus_lemma [simp] : "0' -? 0' = Some 0'"
by (auto simp add: sub_def_Nat)

lemma equal_to_le [simp] : "! x y . x = y --> x <=' y"
apply (auto)
apply (induct_tac x)
by (auto)

lemma zero_minus_anything [simp] : "! x . 0' -! x = 0'"
apply (auto)
apply (case_tac "x >' 0'")
apply (rule subTotal_def1_Nat)
apply (auto)
apply (simp add: greater_def_Nat less_def_Nat)
apply (auto)
apply (rule sym)
apply (subst option.inject[THEN sym])
apply (subst zero_minus_lemma[rule_format, THEN sym])
apply (rule sym)
apply (rule subTotal_def2_Nat)
by (auto)

lemma anything_part_minus_zero [simp] : "! x . x -? 0' = Some x"
by (auto simp add: sub_def_Nat)

lemma some_intro [rule_format] : "! x y. Some x = Some y --> x = y"
by (auto)

lemma anything_minus_zero [simp] : "! x . x -! 0' = x"
apply (auto)
apply (rule some_intro)
apply (subst subTotal_def2_Nat)
by (auto)

lemma suc_com_1_isa : "! x y . x > y --> Suc x - y = Suc (x - y)"
by (auto)

section "Commutes with Multiplication"

theorem mult1 [simp] : "! x . ! y . nat2Nat (x * y) = (nat2Nat x) *' (nat2Nat y)"
apply (auto)
apply (rule nat2Nat.induct)
apply (auto)
apply (subst ga_comm___Xx__)
apply (auto simp add: mult_0_Nat)
apply (subst suc [rule_format, THEN sym])
apply (subst distr2_Nat)
by (auto simp add: ga_right_unit___Xx__)

theorem mult2 [simp] : "!x . ! y. Nat2nat (x *' y) = (Nat2nat x) * (Nat2nat y)"
apply (auto)
apply (rule Nat2nat.induct)
apply (subst ga_comm___Xx__)
apply (subst mult_0_Nat)
apply (auto)
apply (subst suc [rule_format, THEN sym])
apply (subst distr2_Nat)
by (auto simp add: ga_right_unit___Xx__)

section "Preserves Mult Unit"

theorem unitM1 [simp] : "Nat2nat(1') = 1"
by (auto simp add: X1_def_Nat)

theorem unitM2 [simp] : "nat2Nat(1) = 1'"
by (auto simp add: X1_def_Nat)

section "Perserves Add Unit"

theorem unitA1 : "Nat2nat(0') = 0"
by (auto)

theorem unitA2 : "nat2Nat(0) = 0'"
by (auto)

lemma suc_lemma : "!n . Suc(n) = n + 1"
by (auto)

lemma nat2Nat_comm : "!n . nat2Nat n +' 1' = nat2Nat (n + 1)"
apply (auto simp add: suc)
apply (subst ga_comm___XPlus__)
apply (subst suc)
by simp

section "Preserves Order"

lemma le_in_nat : "! x y . x <= (y::nat) = (x - y = 0)"
by (auto)

lemma minus_lem_isa_1 : "! x (y :: nat) . x <= y --> y = (y - x) + x"
by (auto)

lemma minus_lem_isa_2 : "! x (y :: nat) . y = (y - x) + x --> x <= y"
by (auto)

lemma minus_lem_1 : "! x y . (x <=' y) --> y = (y -! x) +' x"
apply (auto)
apply (drule subTotal_def2_Nat)
apply (drule sym)
apply (subst (asm) sub_def_Nat)
by auto

lemma minus_lem_2 : "! x y . y = (y -! x) +' x --> (x <=' y)"
apply (clarify)
apply (subst (asm) sub_def_Nat[THEN sym])
apply (subst geq_def_Nat[THEN sym])
apply (subst sub_dom_Nat[THEN sym])
by (auto)

lemma minus_question_right_unit : "! x . x -? 0' = Some x"
by (auto)

lemma le_lemma4 : "! x y . (x <=' y) = (x <' y | x = y)"
apply (clarify)
apply (subst less_def_Nat)
by (auto)

theorem order1 [simp] : "!! x . !! y. x <= y --> nat2Nat(x) <=' nat2Nat(y)"
by (rule diff_induct, auto)

theorem order2 [simp] : "!! x y. x < y --> nat2Nat (x) <' nat2Nat (y)"
apply (rule diff_induct)
apply (auto)
apply (subst less_def_Nat)
apply (auto)
apply (subst less_def_Nat)
apply (auto simp add: order1)
apply (subst (asm) less_def_Nat)+
by (auto)

lemma weaken_eq : "!! x y . (x = y) ==> (x ==> y)"
by auto

lemma make_conj : "!! x y . [|x;y|] ==> x & y"
by (auto)

lemma nothing_is_lt_zero [simp] : "!! x . ~ (x <' 0')"
apply (induct_tac x)
by (auto simp add: less_def_Nat)

lemma no_le_zero [simp] : "! x . x <=' 0' --> x = 0'"
apply (auto)
apply (case_tac "x = 0'")
apply (auto)
apply (drule_tac Q="x ~= 0'" in conjI)
prefer 2
apply (drule less_def_Nat[THEN sym,THEN weaken_eq, rule_format])
by (auto)

theorem order3 [simp] : "!! x y . x <=' y --> Nat2nat (x) <= Nat2nat (y)"
apply (rule diff_induct_Nat)
apply (auto)
apply (drule no_le_zero[rule_format])
apply (clarify)
by (auto)

lemma lt_2_le : "!! x y . ~ x <' y --> y <=' x"
apply (rule diff_induct_Nat)
apply (auto)
prefer 2
by (auto simp add: less_def_Nat)

lemma le_imp_lt : "!! (x :: nat) (y :: nat) . (x < y) = ((x <= y) & (x ~= y))"
by (auto)

lemma le_le_imp_eq : "!! x y . x <=' y & y <=' x --> y = x"
apply (rule diff_induct_Nat)
by (auto)

theorem order4 [simp] : "!! x y . x <' y --> Nat2nat (x) < Nat2nat (y)"
apply (rule diff_induct_Nat)
apply (auto)
apply (drule less_def_Nat[THEN weaken_eq, rule_format])
apply (auto)
apply (subst le_imp_lt)
apply (auto)
apply (drule lt_2_le[rule_format])
apply (drule not_sym)
by (auto simp add: le_le_imp_eq)

theorem order5 [simp] : "!! x . !! y. x >= y --> nat2Nat(x) >=' nat2Nat(y)"
by (auto simp add: geq_def_Nat)

theorem order6 [simp] : "!! x . !! y. x >=' y --> Nat2nat(x) >= Nat2nat(y)"
by (auto simp add: geq_def_Nat)

theorem order7 [simp] : "!! x . !! y. x > y --> nat2Nat(x) >' nat2Nat(y)"
by (auto simp add: greater_def_Nat)

theorem order8 [simp] : "!! x . !! y. x >' y --> Nat2nat(x) > Nat2nat(y)"
by (auto simp add: greater_def_Nat)

section "Total Minus"

(* Diff Induct for CASL *)

lemma suc_minus_nat_1 [simp] :"! x (y::nat) . y <= x --> Suc(x) -y = Suc(x - y)"
by (auto)

lemma suc_minus_nat_2 [simp] : "! x (y::nat) . x < y --> Suc(x) - y = 0"
by (auto)

lemma d_impE : "!! x y . (x --> y) ==> (x ==> y)"
by (auto)

lemma suc_less : "!! x y . suc'(x) <=' y --> x <=' y"
apply (rule diff_induct_Nat)
apply (force)
apply (force)
by (auto)

lemma less_suc : "!! x y . x <=' y --> x <=' suc'(y)"
apply (induct_tac x)
apply (simp add: leq_def1_Nat)
by (auto simp add: suc_less)

lemma Suc_minus_Nat_1 : "!! x (y::Nat) . y <=' x --> suc'(x) -! y = suc'(x -! y)"
apply (induct_tac y)
apply (auto)
apply (drule suc_less[rule_format])
apply (force)
apply (frule suc_less[rule_format])
apply (frule less_suc[rule_format])
apply (drule subTotal_def2_Nat)
apply (drule_tac f="Some" in arg_cong)
apply (simp)
apply (rule some_intro)
apply (auto)
apply (auto simp add: sub_def_Nat)
apply (subst suc[rule_format,THEN sym])+
apply (subst ga_assoc___XPlus__[THEN sym])
apply (subst suc[rule_format])+
apply (rule_tac f="% x . suc'(x)" in arg_cong)
apply (subst ga_comm___XPlus__)
apply (subst sub_def_Nat[THEN sym])
by (auto)

lemma less_lemma_1 : "!! x . x <' suc'(0') --> x <=' 0'"
apply (induct_tac x)
by (auto simp add: less_def_Nat)

lemma less_lemma_2 : "!! x y . x <' suc'(y) --> x <=' y"
apply (rule diff_induct_Nat)
apply (force simp add: less_lemma_1)
apply (force)
by (auto simp add: less_def_Nat)

lemma le_lemma_1 : "!! x y . x <' suc'(y) --> x <=' y"
apply (rule diff_induct_Nat)
by (auto simp add: less_def_Nat less_lemma_1 less_lemma_2)

lemma same_pMinus_1 : "!! x . x -? x = Some 0'"
by (auto simp add: sub_def_Nat)

lemma same_minus_1 : "!! x . x -! x = 0'"
apply (rule some_intro)
apply (subst same_pMinus_1[THEN sym, where x1="x"])
apply (subst subTotal_def2_Nat)
by (auto)

lemma Suc_minus_Nat_2 : "!! x (y::Nat) . x <' y --> suc'(x) -! y = 0'"
apply (induct_tac y)
apply (auto)
apply (drule less_lemma_2[rule_format])
apply (simp only: less_def_Nat)
apply (auto)
apply (rule some_intro)
apply (subst subTotal_def2_Nat)
apply (force)
apply (force simp add: sub_def_Nat)
apply (drule le_lemma_1[rule_format])
apply (thin_tac "suc'(x) -! Nat = 0'")
apply (case_tac "x = Nat")
apply (auto simp add: same_minus_1)
apply (rule subTotal_def1_Nat)
by (auto simp add: greater_def_Nat less_def_Nat)

lemma not_less_1 : "!! x y . (~(x <' y)) --> y <=' x"
apply (rule diff_induct_Nat)
by (auto simp add: less_def_Nat)

lemma not_le_1 : "!! x y . (~(x <=' y)) --> y <' x"
apply (rule diff_induct_Nat)
by (auto simp add: less_def_Nat)

lemma suc_minus : "!! x y . y <=' x --> x -! y = suc'(x) -! suc'(y)"
apply (auto)
apply (rule some_intro)
apply (rule sym)
apply (subst subTotal_def2_Nat)
apply (force)
apply (subst sub_def_Nat)
apply (rule sym)
apply (subst suc[rule_format, THEN sym])
apply (subst ga_assoc___XPlus__[THEN sym])
apply (subst suc[rule_format])
apply (rule_tac f="% x. suc'(x)" in arg_cong)
apply (rule sym)
apply (subst sub_def_Nat[THEN sym])
by (auto)

lemma suc_minus_2 : "!! x y . y <=' x --> suc'(x) -! suc'(y) = x -! y"
apply (auto)
apply (rule sym)
apply (rule some_intro)
apply (rule sym)
apply (subst subTotal_def2_Nat)
apply (force)
apply (subst sub_def_Nat)
apply (rule sym)
apply (subst suc[rule_format, THEN sym])
apply (subst ga_assoc___XPlus__[THEN sym])
apply (subst suc[rule_format])
apply (rule_tac f="% x. suc'(x)" in arg_cong)
apply (rule sym)
apply (subst sub_def_Nat[THEN sym])
by (auto)

theorem total_minus_1 [simp] : "!! x y . nat2Nat (x - y) = (nat2Nat(x) -! nat2Nat (y))"
apply (rule diff_induct)
apply (auto)
apply (case_tac "nat2Nat ya >' nat2Nat xa")
apply (auto)
apply (drule_tac f="Nat2nat" in arg_cong)
apply (auto simp add: Suc_minus_Nat_1 Suc_minus_Nat_2 greater_def_Nat)
apply (rule sym)
apply (rule subTotal_def1_Nat)
apply (subst greater_def_Nat)
apply (force simp add: less_def_Nat)
apply (drule not_less_1[rule_format])
apply (thin_tac "nat2Nat (xa - ya) = nat2Nat xa -! nat2Nat ya")
apply (rule some_intro)
apply (rule sym)
apply (subst subTotal_def2_Nat)
apply (force)
apply (subst sub_def_Nat)
apply (rule sym)
apply (subst suc[rule_format, THEN sym])
apply (subst ga_assoc___XPlus__[THEN sym])
apply (subst suc[rule_format])
apply (rule_tac f="% x. suc'(x)" in arg_cong)
apply (rule sym)
apply (subst sub_def_Nat[THEN sym])
by (auto)

lemma image_of_zero : "!! x y . x = 0' --> Nat2nat (x) = 0"
by (auto)

theorem total_minus_2 [simp] : "!! x y . Nat2nat (x -! y) = (Nat2nat (x) - Nat2nat(y))"
apply (rule diff_induct_Nat)
apply (force)
apply (force)
apply (auto)
apply (case_tac "ya <=' xa")
apply (subst suc_minus_2)
apply (force)
apply (force)
apply (drule not_le_1[rule_format])
apply (subst (asm) greater_def_Nat[THEN sym])
apply (auto simp add: subTotal_def1_Nat)
apply (subst (asm) greater_def_Nat)
apply (rule image_of_zero[rule_format])
apply (thin_tac "Nat2nat xa <= Nat2nat ya")
apply (rule subTotal_def1_Nat)
apply (auto simp add: greater_def_Nat)
by (auto simp add: less_def_Nat)

section "Factorial"

theorem fac_1 [simp] : "!! x . nat2Nat(fac(x)) = nat2Nat(x)!'"
apply (induct_tac x)
apply (auto simp add: X1_def_Nat)
apply (auto simp add: factorial_suc)
apply (subst ga_comm___XPlus__)
apply (subst mult_suc_Nat[THEN sym])
by (auto)

lemma mult_suc : "!! b (c::nat) . b + c * b = Suc(c) * b"
by (auto)

lemma fac_Suc : "! x . Suc(x) * fac(x) = fac(Suc(x))"
by (auto)

theorem fac_2 [simp] : "!! x . Nat2nat(x!') = fac(Nat2nat(x))"
apply (induct_tac x)
apply (force)
apply (auto)
apply (subst mult_suc)
by (auto simp add: factorial_suc)

section "Min/Max"

lemma min_0 [simp] : "! x . min'(x,0') = 0'"
by (auto simp add: min_def_Nat)

lemma min_0_0 [simp] : "! x . min'(0',x) = 0'"
by (auto simp add: min_def_Nat)

theorem min_1 [simp] : "!! x y . Nat2nat(min'(x,y)) = (min (Nat2nat(x)) (Nat2nat(y)))"
apply (rule diff_induct_Nat)
apply (force)
apply (force)
by (auto simp add: min_def_Nat)

theorem min_2 [simp] : "!! x y. nat2Nat(min x y) = min' (nat2Nat(x), nat2Nat(y))"
apply (rule diff_induct)
apply (force)
apply (force)
by (auto simp add: min_def_Nat)

theorem max_1 [simp] : "!! x y . Nat2nat(max'(x,y)) = (max (Nat2nat(x)) (Nat2nat(y)))"
apply (rule diff_induct_Nat)
apply (force)
apply (force)
by (auto simp add: max_def_Nat)

theorem max_2 [simp] : "!! x y. nat2Nat(max x y) = max' (nat2Nat(x), nat2Nat(y))"
apply (rule diff_induct)
apply (force)
apply (force)
by (auto simp add: max_def_Nat)

section "Exponentiation"

theorem exp_1 [simp] : "!! x y . nat2Nat(x ^ y) = nat2Nat(x) ^' nat2Nat(y)"
apply (induct_tac y)
by (auto simp add: X1_def_Nat power_suc_Nat)

theorem exp_2 [simp] : "!! x y . Nat2nat(x ^' y) = Nat2nat(x) ^ Nat2nat(y)"
apply (induct_tac y)
by (auto simp add: X1_def_Nat power_suc_Nat)

section "Division"

lemma divide_zero : "!! x . x ~= 0' --> 0' div' x = Some 0'"
apply (auto)
apply (subst div_Nat)
apply (auto)
apply (subst ga_comm___Xx__)
apply (subst mult_0_Nat)
by (auto simp add: less_def_Nat)

lemma lt_one : "!! x . x = 0' --> x <' 1'"
apply (auto simp add: less_def_Nat)
apply (subst (asm) X1_def_Nat)
by (auto simp add: ga_disjoint_0_suc)

lemma mod_less_Nat [simp] : "!! x y . x <' y --> x mod' y = Some x"
apply (auto)
apply (subst mod_Nat)
apply (auto)
apply (rule_tac x="0'" in exI)
apply (subst ga_comm___Xx__)
apply (subst mult_0_Nat)
by (auto)

lemma nat_lt_2_le : "!! x (y::nat) . ~ x < y --> y <= x"
by (auto)

theorem mod_1 [simp] : "!! x y . y ~= 0 --> Some (nat2Nat(x mod y)) = nat2Nat(x) mod' nat2Nat(y)"
apply (auto)
apply (rule sym)
apply (subst mod_Nat)
apply (rule_tac x="nat2Nat (x div y)" in exI)
apply (auto)
apply (subst mult1[rule_format,THEN sym])
apply (subst add1[rule_format,THEN sym])
apply (rule_tac f="nat2Nat" in arg_cong)
by (auto)

theorem div_1 [simp] : "!! x y . y ~= 0 --> Some (nat2Nat(x div y)) = nat2Nat(x) div' nat2Nat(y)"
apply (auto)
apply (rule sym)
apply (subst div_Nat)
apply (rule_tac x="nat2Nat (x mod y)" in exI)
apply (auto)
apply (subst mult1[rule_format,THEN sym])
apply (subst add1[rule_format,THEN sym])
apply (rule_tac f="nat2Nat" in arg_cong)
by (auto)

lemma mod_nat : "!! m n (s::nat) . n ~= 0 --> (m mod n = s) = (? (r::nat) . m = n * r + s & s < n)" 
apply (clarify)
apply (auto)
apply (rule_tac x="m div n" in exI)
apply (force)
apply (subst nat_add_commute)
apply (subst mod_mult_self2)
by (auto)

lemma mod_nat2 : "!! m n (s::nat) . n ~= 0 --> (m mod n = s) = (? r . m = n * (Nat2nat r) + s & s < n)" 
apply (clarify)
apply (auto simp add: mod_nat)
apply (rule_tac x="nat2Nat r" in exI)
by (auto)

lemma div_nat : "!! m n (r::nat) . n ~= 0 --> (m div n = r) = (? (s::nat) . m =  n * r + s & s < n)"
apply (clarify)
apply (auto)
apply (rule_tac x="m mod n" in exI)
apply (force)
apply (subst nat_add_commute)
apply (subst div_mult_self2)
by (auto)

lemma div_nat2 : "!! m n (r::nat) . n ~= 0 --> (m div n = r) = (? s . m =  n * r + (Nat2nat s) & (Nat2nat s) < n)"
apply (auto simp add: div_nat)
apply (rule_tac x="nat2Nat s" in exI)
by (auto)

lemma neq_zero_Nat : "!! y . y ~= 0' --> 0' <' y"
apply (induct_tac y)
by (auto simp add: less_def_Nat)

lemma ass_1[rule_format] : "!! a b c . ((a = b) = c) --> (a = (b = c))"
by (auto)

lemma ass_2[rule_format] : "!! a b c . (a = (b = c)) --> ((a = b) = c)"
by (auto)

lemma mod_implies_less : "!! x y z . x mod' y = Some z --> z <' y"
apply (clarify)
apply (subst (asm) mod_Nat)
by (auto)

lemma the_elim : "!! x y . x = y --> the x = the y"
by (auto)

theorem mod_2 [simp] : "!! x y z . y ~= 0' --> ((x mod' y = Some z) = (Nat2nat(z) = Nat2nat(x) mod Nat2nat(y)))"
apply (auto)
apply (rule sym)
apply (drule neq_zero_Nat[rule_format])
apply (subst mod_nat)
apply (auto)
apply (drule order4[rule_format])
apply (auto simp add: mod_Nat)
apply (drule sym)
apply (subst (asm) mod_nat2)
apply (auto)
apply (subst zero_map)
apply (rule order4[rule_format])
apply (drule neq_zero_Nat[rule_format])
apply (auto)
prefer 2
apply (drule sym)
apply (subst (asm) mod_nat)
apply (simp)
apply (drule  neq_zero_Nat[rule_format])
apply (subst zero_map)
apply (rule order4[rule_format])
apply (auto)
apply (drule order2[rule_format])
apply (auto)
apply (rule_tac x="r" in exI)
apply (drule_tac f="nat2Nat" in arg_cong)
by (auto)

theorem div_2 [simp] : "!! x y z . y ~= 0' --> ((x div' y = (Some z)) = (Nat2nat(z) = Nat2nat(x) div Nat2nat(y)))"
apply (auto)
apply (rule sym)
apply (drule neq_zero_Nat[rule_format])
apply (subst div_nat)
apply (auto)
apply (drule order4[rule_format])
apply (auto simp add: div_Nat)
apply (drule sym)
apply (subst (asm) div_nat2[rule_format])
apply (auto)
apply (subst zero_map)
apply (rule order4[rule_format])
apply (drule neq_zero_Nat[rule_format])
apply (auto)
apply (rule_tac x="s" in exI)
apply (drule_tac f="nat2Nat" in arg_cong)
apply (auto)
apply (drule order2[rule_format])
by (auto)

lemma dvd_nat : "!! m n . (m dvd n) = (? k . n = m * (Nat2nat k))"
apply (auto simp add: dvd_def)
apply (rule_tac x="nat2Nat k" in exI)
by (auto)

theorem dvd_1 [simp] : "!! x y . (x dvd' y )= (Nat2nat x dvd Nat2nat y)"
apply (auto simp add: dvd_Nat)
apply (auto simp add: dvd_nat)
apply (subst (asm) mult2[rule_format,THEN sym])
apply (rule_tac x="k" in exI)
apply (drule_tac f="% x . nat2Nat x" in arg_cong)
by (auto)

theorem dvd_2 [simp] : "!! x y . (x dvd y) = (nat2Nat x dvd' nat2Nat y)"
by (auto simp add: dvd_Nat)

theorem part_div_1 [simp] : "!! x y z . (0' <' y & defOp(x /? y)) --> (x /? y = Some z) = ((Some (Nat2nat z)) = Nat2nat x /?? Nat2nat y)"
apply (auto)
apply (subst (asm)  divide_Pos_Nat)
apply (auto simp add: greater_def_Nat)
apply (rule sym)
apply (subst divide_Pos_nat)
apply (auto)
apply (subst zero_map)
apply (rule order4[rule_format])
apply (force)
apply (drule sym)
apply (subst (asm) divide_Pos_nat)
apply (auto)
apply (subst zero_map)
apply (rule order4[rule_format])
apply (force)
apply (subst divide_Pos_Nat)
apply (auto simp add: greater_def_Nat)
apply (drule_tac f="nat2Nat" in arg_cong)
by (auto)

theorem part_div_2 [simp] : "!! x y z . (0 < y & defOp(x /?? y)) --> (x /?? y = Some z) = ((Some (nat2Nat z)) = nat2Nat x /? nat2Nat y)"
apply (auto)
apply (subst (asm) divide_Pos_nat)
apply (force)
apply (rule sym)
apply (subst divide_Pos_Nat[rule_format])
apply (auto simp add: greater_def_Nat)
apply (subst zero_Map)
apply (rule order2[rule_format])
apply (force)
apply (drule sym)
apply (subst (asm) divide_Pos_Nat)
apply (auto simp add: greater_def_Nat)
apply (subst zero_Map)
apply (rule order2[rule_format])
apply (auto)
apply (subst divide_Pos_nat)
apply (auto)
apply (subst (asm) mult1[rule_format, THEN sym])
apply (drule_tac f="Nat2nat" in arg_cong)
by(force)

theorem part_div_def_1 : "!!x y . defOp(x /? y) = defOp(Nat2nat x /?? Nat2nat y)"
apply (auto)
apply (subst divide_dom_nat)
apply (auto simp only: mod_nat2)
prefer 3
apply (subst (asm) divide_dom_nat)
apply (erule conjE)
apply (subst (asm) mod_nat2)
apply (force)
apply (auto simp only: divide_dom_Nat mod_Nat)
apply (force)
apply (auto)
apply (rule_tac x="r" in exI)
apply (drule_tac f="nat2Nat" in arg_cong)
apply (force)
apply (subst (asm) zero_map)
apply (drule order2[rule_format])
apply (force)
apply (subst zero_map)
apply (rule order4[rule_format])
by (force)

theorem part_div_def_2 : "!!x y . defOp(x /?? y) = defOp(nat2Nat x /? nat2Nat y)"
apply (auto)
apply (subst divide_dom_Nat)
apply (auto)
apply (subst (asm) divide_dom_nat)
apply (auto)
apply (drule_tac f="Nat2nat" in arg_cong)
apply (force)
apply (subst (asm) divide_dom_nat)
apply (auto simp add: mod_Nat)
apply (drule order2[rule_format])
apply (auto)
by (auto simp add: part_div_def_1)

section "Even odd"

lemma add_suc : "!! x y . suc'(x) +' suc'(y) = suc'(suc'(x +' y))"
apply (induct_tac x)
apply (auto)
apply (induct_tac y)
apply (auto simp add: add_suc_Nat)
apply (subst ga_comm___XPlus__)
apply (subst add_suc_Nat)
apply (subst add_suc_Nat)
apply (subst ga_comm___XPlus__)
by (force)

lemma times_two : "!! x . x *' 2' = x +' x"
apply (induct_tac x)
apply (auto)
apply (subst  ga_comm___Xx__)
apply (subst mult_suc_Nat)
apply (subst (2) X2_def_Nat)
apply (subst X1_def_Nat)
apply (subst ga_comm___XPlus__)
apply (subst add_suc_Nat)+
apply (subst ga_left_unit___XPlus__)
apply (auto simp add: ga_left_unit___XPlus__)
apply (rule sym)
apply (subst ga_comm___XPlus__)
apply (subst add_suc_Nat)
by (force)

lemma suc_even : "!! x. even'(x) --> even'(suc'(suc'(x)))"
by (auto)

lemma even_times_two [simp] : "!! x . even'(x *' 2')"
apply (induct_tac x)
apply (auto)
apply (subst ga_comm___Xx__)
apply (subst times_two)
apply (subst add_suc)
apply (subst times_two[rule_format, THEN sym])
by (auto simp add: suc_even)

lemma div_mult_same : "!! x y . y ~= 0' --> ((x *' y) div' y = Some x)"
apply (auto simp add: div_Nat)
apply (rule_tac x="0'" in exI)
by (auto simp add: neq_zero_Nat)

lemma the_div_elim : "!! x .  (EX y . x = y *' 2') --> the(x div' 2') *' 2' = x"
apply (induct_tac x)
apply (auto)
apply (subst divide_zero)
apply (auto simp add: X2_def_Nat)
apply (simp add: X2_def_Nat[THEN sym])
apply (subst div_mult_same)
apply (auto)
apply (subst (asm) X2_def_Nat)
apply (auto)
apply (subst (asm) X2_def_Nat[THEN sym])+
apply (subst X2_def_Nat[THEN sym])+
apply (subst div_mult_same)
by (auto simp add: X2_def_Nat)

lemma nat_suc : "!! x . ~ even'(x) --> even'(suc'(x))"
by(auto)

lemma even_two : "!! x . ? y . (x = y *' 2'  --> x div' 2' = Some y)"
apply (auto)
apply (rule_tac x="y" in exI)
apply (auto simp add: div_mult_same)
apply (subst div_Nat)
apply (auto)
apply (rule_tac x="0'" in exI)
by (auto simp add: less_def_Nat X2_def_Nat)

lemma ex_even_odd [simp] : "!! x . ? y . x = y *' 2' | suc'(x) = y *' 2'"
apply (induct_tac x)
apply (rule_tac x="0'" in exI)
apply (force)
apply (auto)
apply (rule_tac x="suc'(y)" in exI)
apply (subst times_two)+
by (auto simp add: add_suc)

lemma ex_even_odd_2 [simp] : "!! x . (? y . x = y *' 2') | (? y . suc'(x) = y *' 2')"
by (auto simp add: ex_disj_distrib[THEN sym])

lemma ex_even_2 [simp] : "!! x. (ALL y. x ~= y *' 2') --> (EX y. suc'(x) = y *' 2')"
by (simp add: imp_conv_disj)

lemma suc_intro : "!! x y . (x = y) = (suc'(x) = suc'(y))"
by(auto)

lemma even_mod [simp] : "!! x . even'(x) = (x mod' 2' = Some 0')"
apply (induct_tac x)
apply (subst mod_Nat)
apply (simp)
apply (rule conjI)
apply (rule_tac x="0'" in exI)
apply (force)
apply (subst X2_def_Nat)
apply (simp add: less_def_Nat)
apply (simp add: mod_Nat)
apply (auto)
apply (auto simp add: less_def_Nat X2_def_Nat)
apply (auto simp add: X2_def_Nat[THEN sym])
apply (drule_tac f="% x . (even'(x))" in arg_cong)
by (auto)

lemma lt_mod : "!! (x::nat) . 0 < x mod (Suc(Suc 0)) --> (Suc 0) = x mod (Suc(Suc 0))"
by (arith)

lemma odd_mod : "!! x . odd'(x) = (x mod' 2' = Some 1')"
apply (auto simp add: X1_def_Nat)
apply (auto simp add: X2_def_Nat)
by (erule lt_mod[rule_format])

lemma mult_with_2 : "!! (x :: nat) . x + x = 2 * x"
by (auto)

lemma def_n_2 : "2 = Suc( Suc 0)"
by (auto)

theorem even_1 [simp] : "!! x . even'(x) = ev_nat(Nat2nat(x))"
apply (case_tac "x=0'")
apply (auto simp add: ev_nat_def)
apply (simp add: mod_Nat)
apply (auto)
apply (rule_tac x="0'" in exI)
apply (force simp add: mult_0_Nat less_def_Nat X2_def_Nat)
apply (force simp add: mult_0_Nat less_def_Nat X2_def_Nat)
apply (simp add: mod_Nat)
apply (clarify)
apply (subst mult2[rule_format])
apply (simp add: X2_def_Nat X1_def_Nat)
apply (simp add: mult_with_2)
apply (drule_tac f="% x . nat2Nat(x)" in arg_cong)
apply (simp)
apply (subst def_n_2)
apply (subst suc_1)+
apply (auto simp add: X1_def_Nat[THEN sym] X2_def_Nat[THEN sym])
by (auto simp add: mod_Nat less_def_Nat X2_def_Nat)

theorem even_2 [simp] : "!! x . ev_nat(x) = even'(nat2Nat(x))"
apply (case_tac "x=0")
apply (auto simp add: ev_nat_def)
apply (simp add: mod_Nat)
apply (auto simp add: less_def_Nat X2_def_Nat)
apply (rule_tac x="0'" in exI)
apply (force simp add: mult_0_Nat)
apply (arith)
by (arith)

lemma even_not_odd_nat : "!! x . ev_nat(x) = (~(od_nat(x)))"
apply (auto simp only: ev_nat_def od_nat_def)
by (arith)

lemma even_not_odd_nat_2 : "!! x . od_nat(x) = (~ ev_nat(x))"
by (auto simp only: ev_nat_def od_nat_def)

theorem odd_1 [simp] : "!! x . odd'(x) = od_nat(Nat2nat(x))"
apply (auto simp only: even_not_odd_nat_2)
by (auto)

theorem odd_2 [simp] : "!! x . od_nat(x) = odd'(nat2Nat(x))"
apply (auto simp only: even_not_odd_nat_2)
by (auto)

section "Numbers"

theorem zero_1 : "0' = nat2Nat(0)"
by (auto)

theorem zero_2 : "0 = Nat2nat(0')"
by (auto)

theorem one_1 : "1' = nat2Nat(1)"
by (auto simp add: X1_def_Nat)

theorem one_2 : "1 = Nat2nat(1')"
by (auto simp add: X1_def_Nat)

theorem two_1 [simp] : "2' = nat2Nat(2)"
apply (rule Nat2nat_inj)
apply (auto)
by (auto simp add: X2_def_Nat)

theorem two_2  : "2 = Nat2nat(2')"
by (auto)

theorem three_1 [simp] : "3' = nat2Nat(3)"
apply (rule Nat2nat_inj)
apply (auto)
by (auto simp add: X3_def_Nat)

theorem three_2  : "3 = Nat2nat(3')"
by (auto)

theorem four_1 [simp] : "4' = nat2Nat(4)"
apply (rule Nat2nat_inj)
apply (auto)
by (auto simp add: X4_def_Nat)

theorem four_2  : "4 = Nat2nat(4')"
by (auto)

theorem five_1 [simp] : "5' = nat2Nat(5)"
apply (rule Nat2nat_inj)
apply (auto)
by (auto simp add: X5_def_Nat)

theorem five_2  : "5 = Nat2nat(5')"
by (auto)

theorem six_1 [simp] : "6' = nat2Nat(6)"
apply (rule Nat2nat_inj)
apply (auto)
by (auto simp add: X6_def_Nat)

theorem six_2  : "6 = Nat2nat(6')"
by (auto)

theorem seven_1 [simp] : "7' = nat2Nat(7)"
apply (rule Nat2nat_inj)
apply (auto)
by (auto simp add: X7_def_Nat)

theorem seven_2  : "7 = Nat2nat(7')"
by (auto)

theorem eight_1 [simp] : "8' = nat2Nat(8)"
apply (rule Nat2nat_inj)
apply (auto)
by (auto simp add: X8_def_Nat)

theorem eight_2  : "8 = Nat2nat(8')"
by (auto)

theorem nine_1 [simp] : "9' = nat2Nat(9)"
apply (rule Nat2nat_inj)
apply (auto)
by (auto simp add: X9_def_Nat)

theorem nine_2  : "9 = Nat2nat(9')"
by (auto)

section "Decimal"

theorem comb_1 [simp] : "!! x y . nat2Nat(x @@@ y) = nat2Nat(x) @@ nat2Nat(y)"
apply (auto simp add: decimal_def decimal_def_nat)
apply (rule Nat2nat_inj)
by (auto)

theorem comb_2 [simp] : "!! x y . Nat2nat( x @@ y) = Nat2nat(x) @@@ Nat2nat(y)"
by (auto simp add: decimal_def decimal_def_nat)

section "Missing operations"

text "/?, even, odd, !, pre are missing in Isabelles' nats"
text "fixed"

section "Problems"

text "Constants 2,3,... overwrite Isabelle constants"
text "fixed"

section "Additions"

text "Added dvd to CASL Nats"
text "Constants fixed"
text "added fac"
text "added pre"
text "added part div to Isa /??"
text "added even and odd"
text "added decimal combinator"

end
