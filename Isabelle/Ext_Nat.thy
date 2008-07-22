theory Ext_Nat
imports "$HETS_LIB/Isabelle/MainHC"
begin

consts fac :: "nat => nat"("(_/ !)" [58] 58)
consts pre_nat :: "nat => nat option"
consts part_div :: "nat => nat => nat option" ("(_/ '/??/ _)" [54,54] 52)
consts ev_nat :: "nat => bool"
consts od_nat :: "nat => bool"
consts combine_nat :: "nat => nat => nat" ("(_/ @@@/ _)" [54,54] 52)

defs
ev_nat_def: "ev_nat x == (x mod 2 = 0)"
od_nat_def: "od_nat x == (x mod 2 = 1)"

axioms
divide_dom_nat [rule_format] :
"ALL m.
 ALL X_n. defOp (m /?? X_n) = (~ X_n = 0 & m mod X_n = 0)"

divide_0_nat [rule_format] : "ALL m. ~ defOp (m /?? 0)"

divide_Pos_nat [rule_format] :
"ALL m.
 ALL X_n. ALL r. X_n > 0 --> m /?? X_n = Some r = (m = r * X_n)"

decimal_def_nat [rule_format] :
"ALL m. ALL X_n. m @@@ X_n = (m * Suc(9)) + X_n"

primrec
"fac 0 = 1"
"fac (Suc n) = (Suc n) * (fac n)"

primrec
"pre_nat 0 = None"
"pre_nat (Suc n) = Some n"

end
