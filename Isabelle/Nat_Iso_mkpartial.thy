theory Numbers_Nat
imports "$HETS_LIB/Isabelle/MainHCPairs" "Primes" "Parity"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"ga_function_monotonicity\", \"ga_function_monotonicity_1\",
     \"ga_function_monotonicity_2\", \"ga_function_monotonicity_3\",
     \"ga_function_monotonicity_4\", \"ga_function_monotonicity_5\",
     \"ga_embedding_injectivity\", \"ga_projection_injectivity\",
     \"ga_projection\", \"ga_selector_pre\", \"ga_injective_suc\",
     \"ga_disjoint_0_suc\", \"ga_selector_undef_pre_0\", \"X1_def_Nat\",
     \"X2_def_Nat\", \"X3_def_Nat\", \"X4_def_Nat\", \"X5_def_Nat\",
     \"X6_def_Nat\", \"X7_def_Nat\", \"X8_def_Nat\", \"X9_def_Nat\",
     \"decimal_def\", \"ga_comm___XPlus__\", \"ga_assoc___XPlus__\",
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
     \"divide_dom_Nat\", \"divide_0_Nat\", \"divide_Pos_Nat\",
     \"div_dom_Nat\", \"div_Nat\", \"mod_dom_Nat\", \"mod_Nat\",
     \"distr1_Nat\", \"distr2_Nat\", \"Pos_def\", \"X1_as_Pos_def\",
     \"min_0\", \"div_mod_Nat\", \"power_Nat\"]"

typedecl Pos

datatype X_Nat = X0 ("0''") | sucX1 "X_Nat" ("suc''/'(_')" [3] 999)

consts
X1X1 :: "X_Nat" ("1''")
X1X2 :: "Pos" ("1''''")
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
X__XPlus__XX1 :: "X_Nat => X_Nat => X_Nat" ("(_/ +''/ _)" [54,54] 52)
X__XPlus__XX2 :: "X_Nat => Pos => Pos" ("(_/ +''''/ _)" [54,54] 52)
X__XPlus__XX3 :: "Pos => X_Nat => Pos" ("(_/ +'_3/ _)" [54,54] 52)
X__XSlashXQuest__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ '/?/ _)" [54,54] 52)
X__Xx__XX1 :: "X_Nat => X_Nat => X_Nat" ("(_/ *''/ _)" [54,54] 52)
X__Xx__XX2 :: "Pos => Pos => Pos" ("(_/ *''''/ _)" [54,54] 52)
X__div__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ div''/ _)" [54,54] 52)
X__dvd__X :: "X_Nat => X_Nat => bool" ("(_/ dvd''/ _)" [44,44] 42)
X__mod__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ mod''/ _)" [54,54] 52)
X_even :: "X_Nat => bool" ("even''/'(_')" [3] 999)
X_gn_inj_Pos_Nat :: "Pos => X_Nat" ("gn'_inj'_Pos'_Nat/'(_')" [3] 999)
X_gn_proj_Nat_Pos :: "X_Nat => Pos partial" ("gn'_proj'_Nat'_Pos/'(_')" [3] 999)
X_max :: "X_Nat => X_Nat => X_Nat" ("max''/'(_,/ _')" [3,3] 999)
X_min :: "X_Nat => X_Nat => X_Nat" ("min''/'(_,/ _')" [3,3] 999)
X_odd :: "X_Nat => bool" ("odd''/'(_')" [3] 999)
X_pre :: "X_Nat => X_Nat partial" ("pre/'(_')" [3] 999)
sucX2 :: "X_Nat => Pos" ("suc''''/'(_')" [3] 999)

section "Extension of Naturals"
(* we introduce some new symbols *)
consts combine_nat :: "nat => nat => nat" ("(_/ @@@/ _)" [54,54] 52)
consts part_div :: "nat => nat => nat partial" ("(_/ '/??/ _)" [54,54] 52)
consts part_minus :: "nat => nat => nat partial" ("(_/ '-??/ _)" [54,54] 52)

primrec pre_nat
where
  pre_nat_0: "pre_nat 0 = noneOp"
  | pre_nat_suc: "pre_nat (Suc n) = makePartial n"


axioms
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
"ALL x. ALL y. gn_proj_Nat_Pos(x) =e= gn_proj_Nat_Pos(y) --> x = y"

ga_projection [rule_format] :
"ALL x. gn_proj_Nat_Pos(gn_inj_Pos_Nat(x)) = makePartial x"

ga_selector_pre [rule_format] :
"ALL XX1. pre(suc'(XX1)) = makePartial XX1"

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

dvd_def_Nat [rule_format] :
"ALL m. ALL X_n. (m dvd' X_n) = (EX k. X_n = m *' k)"

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

divide_Pos_Nat [rule_format] :
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

Pos_def [rule_format] :
"ALL p. defOp (gn_proj_Nat_Pos(p)) = (p >' 0')"

X1_as_Pos_def [rule_format] : "1'' = suc''(0')"

min_0 [rule_format] : "ALL m. min'(m, 0') = 0'"

div_mod_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ~ X_n = 0' -->
 makePartial m =
 (let (Xb5, Xc0) =
      let (Xb4, Xc3) = m div' X_n
      in if Xb4 then makePartial (Xc3 *' X_n) else noneOp
  in if Xb5
        then let (Xb2, Xc1) = m mod' X_n
             in if Xb2 then makePartial (Xc0 +' Xc1) else noneOp
        else noneOp)"

power_Nat [rule_format] :
"ALL m. ALL r. ALL s. m ^' (r +' s) = (m ^' r) *' (m ^' s)"

decimal_def_nat [rule_format] : 
"ALL m. ALL X_n. m @@@ X_n = (m * Suc(9)) + X_n"

divide_Pos_nat [rule_format] :
"ALL m. ALL X_n. ALL r. X_n > 0 --> m /?? X_n = makePartial r = (m = r * X_n)"

part_div_def : "x /??y = (if (x mod y = 0) then makePartial(x div y) else noneOp)"
part_minus_def : "x -?? y = (if (x>=y) then makePartial(x-y) else noneOp)"

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




section "Strong Equality"

lemma strong_equality : "!! (t::'a partial) (s::'a partial) . (t =s= s)  =  (! x . ((t = makePartial x) <-> (s = makePartial x)))"
apply (rule iffI)
defer
apply (unfold makePartial_def)
apply (unfold strongEqualOp_def)
apply (auto)
done

lemma normal2strong: "!!a b. (a=b) ==> (a =s= b)"
apply (unfold strongEqualOp_def)
apply (auto)
done

lemma makepartial_intro : "(s=makePartial t) = (defOp(s) & (snd(s)=t))"
apply (rule iffI)
apply (simp add: makePartial_def)
apply (subst defOp_def)
apply (simp)
apply (simp add: makePartial_def)
apply (case_tac "s")
apply (simp add: defOp_def)
done

lemma makepartial_intro_weak: "(s=makePartial t) ==> (snd(s)=t)"
apply (simp add: makePartial_def)
done


lemma makePartialproj: "snd (makePartial x) = x"
apply (simp add: makePartial_def)
done

section "Definition of the Isomorphism"

primrec Nat2nat
where 
  Nat2nat_0: "Nat2nat  0' = 0 " 
  | Nat2nat_suc: "Nat2nat  (suc'(x)) = Suc (Nat2nat x)"

primrec nat2Nat
where
  nat2Nat_0: "nat2Nat 0 = 0'"
| nat2Nat_Suc: "nat2Nat (Suc x) = suc' (nat2Nat x)"

lemma iso1 [simp] : "! x . nat2Nat(Nat2nat x) = x"
apply (auto)
apply (induct_tac x)
apply (auto)
done

lemma iso2 [simp] : "! x. Nat2nat(nat2Nat x) = x"
apply (auto)
apply (induct_tac x)
apply (auto)
done


lemma nat2Nat_injectivity : "nat2Nat(x) = nat2Nat(y) ==> x = y"
apply (drule_tac f="%x. Nat2nat(x)" in arg_cong)
apply (simp)
done

lemma Nat2nat_injectivity : "Nat2nat(x) = Nat2nat(y) ==>  x = y"
apply (drule_tac f="%x. nat2Nat(x)" in arg_cong)
apply (simp)
done

(* ask Lutz which version to use *)
lemma inj_predefined : "inj Nat2nat"
apply (simp add: inj_on_def)
apply (auto)
apply (drule_tac f="%x. nat2Nat(x)" in arg_cong)
apply (simp)
done

section "Simple Definitions"

(* the numbers need special treatment. we use the following strategy: 1' is manually proved
   for subsequent numbers: apply definition for n' -> suc( [n-1]'), use theorem for [n-1]', ripple out via nat2Nat_Suc *)

(* ============================== 1 ============================== *)

(*by (auto simp add: X1_def_Nat)*)
theorem nat2Nat_1_def_Nat : "1' = nat2Nat(1)"
apply (simp)
apply (subst X1_def_Nat)
apply (auto)
done

(* get backwards direction via the iso (already in the simplifier) and the other direction *)
theorem Nat2nat_1_def_Nat : "1=Nat2nat(1')"
apply (simp add: nat2Nat_1_def_Nat)
done

(* ============================== 2 ============================== *)

theorem nat2Nat_2_def_Nat : "2' = nat2Nat(2)"
apply (subst X2_def_Nat)
apply (subst nat2Nat_1_def_Nat)
apply (subst nat2Nat_Suc [rule_format, THEN sym])
apply (subgoal_tac "Suc 1 = 2")
apply (drule_tac f="%x. nat2Nat(x)" in arg_cong)
apply (auto)
done

theorem two_2  : "2 = Nat2nat(2')"
apply (simp add: nat2Nat_2_def_Nat)
done

(* ============================== 3 ============================== *)

theorem nat2Nat_3_def_Nat : "3' = nat2Nat(3)"
apply (subst X3_def_Nat)
apply (subst nat2Nat_2_def_Nat)
apply (subst nat2Nat_Suc [rule_format, THEN sym])
apply (simp)
done

theorem nat2Nat_3_def_nat : "3 = Nat2nat(3')"
apply (simp add: nat2Nat_3_def_Nat)
done

(* ============================== 4 ============================== *)

theorem nat2Nat_4_def_Nat : "4' = nat2Nat(4)"
apply (subst X4_def_Nat)
apply (subst nat2Nat_3_def_Nat)
apply (subst nat2Nat_Suc [rule_format, THEN sym])
apply (simp)
done

theorem Nat2nat_4_def_Nat : "4  = Nat2nat(4')"
apply (simp add: nat2Nat_4_def_Nat)
done

(* ============================== 5 ============================== *)

theorem nat2Nat_5_def_Nat : "5' = nat2Nat(5)"
apply (subst X5_def_Nat)
apply (subst nat2Nat_4_def_Nat)
apply (subst nat2Nat_Suc [rule_format, THEN sym])
apply (simp)
done

theorem Nat2nat_5_def_Nat : "5  = Nat2nat(5')"
apply (simp add: nat2Nat_5_def_Nat)
done

(* ============================== 6 ============================== *)

theorem nat2Nat_6_def_Nat : "6' = nat2Nat(6)"
apply (subst X6_def_Nat)
apply (subst nat2Nat_5_def_Nat)
apply (subst nat2Nat_Suc [rule_format, THEN sym])
apply (simp)
done

theorem Nat2nat_6_def_Nat : "6  = Nat2nat(6')"
apply (simp add: nat2Nat_6_def_Nat)
done

(* ============================== 7 ============================== *)

theorem nat2Nat_7_def_Nat : "7' = nat2Nat(7)"
apply (subst X7_def_Nat)
apply (subst nat2Nat_6_def_Nat)
apply (subst nat2Nat_Suc [rule_format, THEN sym])
apply (simp)
done

theorem Nat2nat_7_def_Nat : "7  = Nat2nat(7')"
apply (simp add: nat2Nat_7_def_Nat)
done

(* ============================== 8 ============================== *)

theorem nat2Nat_8_def_Nat : "8' = nat2Nat(8)"
apply (subst X8_def_Nat)
apply (subst nat2Nat_7_def_Nat)
apply (subst nat2Nat_Suc [rule_format, THEN sym])
apply (simp)
done

theorem Nat2nat_8_def_Nat : "8  = Nat2nat(8')"
apply (simp add: nat2Nat_8_def_Nat)
done

(* ============================== 9 ============================== *)

theorem nat2Nat_9_def_Nat : "9' = nat2Nat(9)"
apply (subst X9_def_Nat)
apply (subst nat2Nat_8_def_Nat)
apply (subst nat2Nat_Suc [rule_format, THEN sym])
apply (simp)
done

theorem Nat2nat_9_def_Nat : "9  = Nat2nat(9')"
apply (simp add: nat2Nat_9_def_Nat)
done


section "Recursive Definitions"

theorem nat2Nat_add [simp] : "nat2Nat (x + y) = (nat2Nat x) +' (nat2Nat y)"
apply (induct_tac x)
apply (auto simp only: nat2Nat_Suc nat2Nat_0 add_Suc add_0 add_suc_Nat add_0_Nat)
done

theorem Nat2nat_add : "Nat2nat (x +' y) = (Nat2nat x) + (Nat2nat y)"
apply (rule nat2Nat_injectivity)
apply (auto)
done

theorem nat2Nat_mul [simp] : "nat2Nat (x * y) = (nat2Nat x) *' (nat2Nat y)"
apply (induct_tac x)
apply (auto simp only: nat2Nat_Suc nat2Nat_0 nat2Nat_add mult_Suc mult_0 mult_suc_Nat mult_0_Nat)
apply (auto)
done

theorem Nat2nat_mul : "Nat2nat (x *' y) = (Nat2nat x) * (Nat2nat y)"
apply (rule nat2Nat_injectivity)
apply (auto)
done

theorem nat2Nat_power [simp] : "nat2Nat(x ^ y) = nat2Nat(x) ^' nat2Nat(y)"
apply (induct_tac y)
apply (auto)
apply (simp add: X1_def_Nat)
done

theorem Nat2nat_power : "Nat2nat(x ^' y) = Nat2nat(x) ^ Nat2nat(y)"
apply (rule nat2Nat_injectivity)
apply (auto)
done

theorem nat2Nat_fac [simp] : "nat2Nat(fact(x)) = nat2Nat(x)!'"
apply (induct_tac x)
apply (simp add: X1_def_Nat)
apply (subst fact.simps)
apply (simp only: nat2Nat_mul nat2Nat_Suc factorial_suc)
done

theorem Nat2nat_fac : "Nat2nat(x!') = fact(Nat2nat(x))"
apply (rule nat2Nat_injectivity)
apply auto
done

section "Predicates"


subsection "ordering"

lemma no_le_zero [simp] : "(x <=' 0') = (x = 0')"
apply (case_tac x)
by (auto)

lemma no_nat2Nat_zero [simp] : "!!x. nat2Nat x = 0' ==> x = 0"
apply (rule nat2Nat_injectivity)
apply simp
done

theorem nat2Nat_lt_equal [simp] : "x <= y <-> nat2Nat(x) <=' nat2Nat(y)"
apply (rule diff_induct)
apply (auto)
done

theorem Nat2nat_lt_equal : "x <=' y <-> Nat2nat(x) <= Nat2nat(y)"
apply (auto)
done

theorem nat2Nat_lt [simp] : "x < y <-> nat2Nat(x) <' nat2Nat(y)"
apply (rule diff_induct)
apply (auto)
done

theorem Nat2nat_lt : "x <' y <-> Nat2nat(x) < Nat2nat(y)"
apply (auto)
done

theorem nat2Nat_gt [simp] : "x > y <-> nat2Nat(x) >' nat2Nat(y)"
apply (rule diff_induct)
apply (auto)
done

theorem Nat2nat_gt : "x >' y <-> Nat2nat(x) > Nat2nat(y)"
apply (auto)
done

theorem nat2Nat_gt_equal [simp] : "x >= y <-> nat2Nat(x) >=' nat2Nat(y)"
apply (rule diff_induct)
apply (auto)
done

theorem Nat2nat_gt_equal : "x >=' y <-> Nat2nat(x) >= Nat2nat(y)"
apply(auto)
done

subsection "Even and Odd"

lemma suc_even_nat: "even(x) ==> even(Suc(Suc(x)))"
apply (auto)
done

theorem nat2Nat_even [simp] : "((even'(x) <-> even(Nat2nat(x))) & (odd'(x) <-> odd(Nat2nat(x))))"
apply (induct x)
apply (simp)
apply (rule conjI)
apply (simp only: even_suc_Nat Nat2nat_suc even_nat_Suc suc_even_nat)
apply (subst Nat2nat_suc)
apply (subst even_nat_Suc [rule_format, THEN sym])
apply (auto)
done

theorem Nat2nat_even : "((even(x) <-> even'(nat2Nat(x))) & (odd(x) <-> odd'(nat2Nat(x))))"
apply (auto)
done

theorem nat2Nat_dvd [simp] : "(x dvd y) <-> (nat2Nat(x) dvd' nat2Nat(y))"
apply (subst dvd_def_Nat)
apply (subst dvd_def)
apply (rule iffI)
apply (erule exE)
apply (drule_tac f="%x. nat2Nat(x)" in arg_cong)
apply (force)
apply (erule exE)
apply (drule_tac f="%x. Nat2nat(x)" in arg_cong)
apply (simp (no_asm_use) only: Nat2nat_mul iso2)
apply (auto)
done


theorem Nat2nat_dvd : "(x dvd' y) = (Nat2nat(x) dvd Nat2nat(y))"
apply (auto)
sorry

section "Simple Functions"

theorem nat2Nat_max [simp]: "nat2Nat(max x y) = max'(nat2Nat(x),nat2Nat(y))"
apply (simp add: max_def_Nat max_def)
done

theorem Nat2nat_max : "Nat2nat(max'(x,y)) = (max (Nat2nat(x)) (Nat2nat(y)))"
apply (simp add: max_def_Nat max_def)
done

theorem nat2Nat_min : "nat2Nat(min x y) = min' (nat2Nat(x), nat2Nat(y))"
apply (simp add: min_def_Nat min_def)
done

theorem Nat2nat_min : "Nat2nat(min'(x,y)) = (min (Nat2nat(x)) (Nat2nat(y)))"
apply (simp add: min_def_Nat min_def)
done


(* ============================================================================= *)
(* ============================== cut off minus ================================ *)
(* ============================================================================= *)


lemma anything_part_minus_zero [simp] : "x -? 0' = makePartial x"
apply (simp add: sub_def_Nat)
done

lemma add_partiality  : "x=y <-> makePartial x = makePartial y"
apply (simp add: makePartial_def)
done


lemma anything_minus_zero [simp] : "x -! 0' = x"
(* here the problem is that the defined rewrite rule is only applicable for makePartial x-!y *)
apply (subst add_partiality)
apply (subst subTotal_def2_Nat)
apply (simp)
apply (subst anything_part_minus_zero)
apply (simp)
done

lemma not_greater_zero : "~ x>'0' <-> x <=' 0'"
apply (simp)
apply (auto)
done



lemma zero_minus_anything [simp] : "0' -! x = 0'"
apply (case_tac "x>'0'")
apply (simp only: subTotal_def1_Nat)
apply (subst (asm) not_greater_zero)
apply (subst add_partiality)
apply (subst subTotal_def2_Nat)
apply (auto)
done

lemma not_iff : "(A<->B) <-> (~A <-> ~B)"
apply (auto)
done


lemma not_greater_suc : "~ (x>'y) <-> x <' suc'(y)"
apply (insert Nat2nat_gt)
apply (subst (asm) not_iff)
apply (subst (asm) not_less_eq)
apply (subst (asm) Nat2nat_suc [rule_format, THEN sym])
apply (subst (asm) Nat2nat_lt [rule_format, THEN sym])
apply (auto)
done

lemma not_greater_isa : "~((x::nat) > (y::nat)) <-> x<=y"
apply (arith)
done

lemma minus_Suc : "(Suc(x) - Suc(y))=(x-y)"
apply (auto)
done

lemma not_greater : " ~ (x>'y) <-> x<='y"
sorry

lemma minus_neutral : "(x <=' y) ==> y = (y -! x) +' x"
apply (drule subTotal_def2_Nat)
apply (drule sym)
apply (subst (asm) sub_def_Nat)
apply (auto)
done

(*forward reasoning anstatt makePartial einfügen ist hilfreich*)

lemma minus_suc : "(suc'(x) -! suc'(y))=(x-!y)"
apply (case_tac "y>'x")
apply (simp)
apply (subst (asm) not_greater)
apply (subst add_partiality)
apply (subst subTotal_def2_Nat)
apply (simp)
apply (subst sub_def_Nat)
apply (subst ga_comm___XPlus__)
apply (subst add_suc_Nat)
apply (subst ga_injective_suc)
apply (subst ga_comm___XPlus__)
apply (rule minus_neutral)
apply (simp)
done

theorem nat2Nat_minus: "nat2Nat (x - y) = (nat2Nat(x) -! nat2Nat (y))"
apply (rule diff_induct)
apply (simp)
apply (simp only: nat2Nat_0 nat2Nat_Suc diff_0_eq_0 zero_minus_anything)
apply (subst minus_Suc)
apply (simp)
apply (subst minus_suc)
apply (auto)
done

theorem Nat2nat_minus: "Nat2nat (x -! y) = (Nat2nat (x) - Nat2nat(y))"
apply (rule nat2Nat_injectivity)
apply (subst nat2Nat_minus)
apply (auto)
done


section "Partial Functions"

theorem iso2_negated: "~(nat2Nat(x)=nat2Nat(y)) ==> ~(x=y)"
apply (auto)
done

theorem iso1_negated1: "x~=y ==> ~(Nat2nat(x)=Nat2nat(y))"
apply (auto)
apply (drule Nat2nat_injectivity)
apply (auto)
done





section "Non-canonical Mappings"

theorem nat2Nat_at : "nat2Nat(x @@@ y) = nat2Nat(x) @@ nat2Nat(y)"
apply (auto simp add: decimal_def decimal_def_nat)
apply (rule Nat2nat_injectivity)
apply (simp only: Nat2nat_mul Nat2nat_add Nat2nat_9_def_Nat[rule_format, THEN sym])
by (auto)

theorem Nat2nat_at  : "Nat2nat( x @@ y) = Nat2nat(x) @@@ Nat2nat(y)"
apply (simp only: decimal_def decimal_def_nat)
apply (simp only: Nat2nat_mul Nat2nat_suc Nat2nat_add Nat2nat_9_def_Nat[rule_format, THEN sym])
done


theorem Nat2nat_pre : "!!x. x > 0 --> nat2Nat(snd (pre_nat(x))) = snd (pre (nat2Nat(x)))"
apply (case_tac x)
apply (simp)
apply (simp add: makePartial_def)
done

theorem nat2Nat_pre : "!!x. x >' 0' --> ( Nat2nat(snd (pre(x)))  = snd(pre_nat (Nat2nat x)))"
apply (case_tac x)
apply (simp)
apply (simp add: makePartial_def)
done

theorem nat2Nat_div [simp] : " y ~= 0 ==> nat2Nat(x div y) = snd(nat2Nat(x) div' nat2Nat(y))"
apply (rule sym)
apply (rule makepartial_intro_weak)
apply (subst div_Nat)
apply (rule_tac x="nat2Nat (x mod y)" in exI)
apply (rule conjI)
apply (rule Nat2nat_injectivity)
apply (simp only: iso2 Nat2nat_add Nat2nat_mul)
apply (arith)
apply (subst nat2Nat_lt[rule_format,THEN sym])
apply (rule mod_less_divisor)
apply (arith)
done

theorem Nat2nat_div [simp] : " y ~= 0' ==> Nat2nat(snd (x div' y)) = Nat2nat(x) div Nat2nat(y)"
apply (frule iso1_negated1)
apply (subst (asm) Nat2nat_0)
apply (rule nat2Nat_injectivity)
apply (drule nat2Nat_div)
apply (simp)
done


theorem nat2Nat_mod [simp] : "~(y = 0) ==> nat2Nat(x mod y) =snd (nat2Nat(x) mod' nat2Nat(y))"
apply (rule sym)
apply (rule makepartial_intro_weak)
(*apply (subst nat2Nat_mod_mp[rule_format,THEN sym])*)
apply (simp)
apply (subst mod_Nat)
apply (rule_tac x="nat2Nat (x div y)" in exI)
apply (rule conjI)
apply (subst nat2Nat_mul[rule_format,THEN sym])
apply (subst nat2Nat_add[rule_format,THEN sym])
apply (rule_tac f="nat2Nat" in arg_cong)
apply (simp)
apply (subst Nat2nat_lt)
apply (simp only: iso2)
apply (rule mod_less_divisor)
apply (auto)
done

theorem Nat2nat_mod : "~(y = 0') ==>  Nat2nat (snd (x mod' y)) = (Nat2nat(x) mod Nat2nat(y))"
apply (frule iso1_negated1)
apply (subst (asm) Nat2nat_0)
apply (rule nat2Nat_injectivity)
apply (drule nat2Nat_mod)
apply (simp)
done

theorem nat2Nat_pdiv : "[|~ y = 0 ; x mod y = 0|] ==> nat2Nat(snd(x /?? y)) =snd(nat2Nat(x) /? nat2Nat(y))"
apply (rule sym)
apply (rule makepartial_intro_weak)
apply (subst divide_Pos_Nat)
apply (simp)
apply (rule Nat2nat_injectivity)
apply (simp only: Nat2nat_mul iso2)
apply (subst part_div_def)
apply (simp add: makePartialproj)
apply (drule iso1_negated1)
apply (simp only: Nat2nat_0 iso2)
apply (auto)
done


theorem Nat2nat_pdiv : "[|~ y = 0' ; x mod' y = makePartial 0'|] ==> Nat2nat(snd(x /? y)) =snd(Nat2nat(x) /?? Nat2nat(y))"
apply (drule iso1_negated1)
apply (subst (asm) Nat2nat_0)
apply (drule_tac f="%x. snd(x)" in arg_cong)
apply (drule_tac f="%x. Nat2nat(x)" in arg_cong)
apply (subst (asm) Nat2nat_mod)
apply (simp)
apply (simp  only: makePartialproj Nat2nat_0 Nat2nat_mod)
apply (rule nat2Nat_injectivity)
apply (drule nat2Nat_pdiv)
apply (simp)
apply (simp)
done

theorem nat2Nat_pminus : "(x >= y) ==> nat2Nat(snd (x -?? y)) = snd(nat2Nat(x) -? nat2Nat(y))"
apply (rule sym)
apply (rule makepartial_intro_weak)
apply (subst sub_def_Nat)
apply (rule Nat2nat_injectivity)
apply (simp only: Nat2nat_add iso2)
apply (subst part_minus_def)
apply (simp add: makePartialproj)
done

theorem Nat2nat_pminus : "(x >=' y) ==> Nat2nat(snd(x -? y)) = snd(Nat2nat(x) -?? Nat2nat(y))"
apply (subst (asm) Nat2nat_gt_equal)
apply (rule nat2Nat_injectivity)
apply (subst nat2Nat_pminus)
apply (simp)
apply (simp)
done

end

