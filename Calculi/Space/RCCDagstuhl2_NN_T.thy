theory RCCDagstuhl2_NN_T
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin


ML "Header.initialize [\"P_def_1\",\"O_def_1\",\"NTP_def_1\",\"C_non_null\",\"C_sym\",\"C_id\",\"C_non_triv\",\"Ax1\",\"def_nonempty\",\"C_def\",\"P_def\",\"O_def\",\"NTP_def\",\"MS_pos\",\"MS_zero\",\"MS_pos_definite\",\"MS_symm\",\"MS_triangle\",\"one_greater_zero\",\"zero_leq_one\",\"half_gt_zero\",\"half_plus_minus\",\"add_monotone\",\"sub_leq\",\"half_leq\",\"half_leq_zero\",\"comm_add\",\"Real_abs_def\",\"Real_sqr_def\",\"Real_sqrt_dom\",\"Real_sqrt_def\",\"Real_2_def\",\"Real_minus_def\",\"Real_divide_dom\",\"Real_divide_def\",\"Real_half_def\",\"ga_Nat\",\"Real_ub_def\",\"Real_lb_def\",\"Real_inf_def\",\"Real_sup_def\",\"Real_isBounded_defCBrX\",\"Real_inj_0\",\"Real_inj_suc\",\"Real_archimedian\",\"FWO_plus\",\"FWO_times\",\"Field_unary_minus_def\",\"dichotomy_TotalOrder\",\"antisym\",\"trans\",\"refl\",\"min_inf_relation\",\"max_sup_relation\",\"ga_comm_min\",\"ga_comm_max\",\"ga_assoc_min\",\"ga_assoc_max\",\"min_def_ExtTotalOrder\",\"max_def_ExtTotalOrder\",\"ga_comm_inf\",\"ga_comm_sup\",\"inf_def_ExtPartialOrder\",\"sup_def_ExtPartialOrder\",\"geq_def_ExtPartialOrder\",\"less_def_ExtPartialOrder\",\"greater_def_ExtPartialOrder\",\"EMSCD_rep_pos\",\"EMSCD_rep_0\",\"EMSCD_rep_inj\",\"Ax4\",\"ga_Nat_1\"]"



typedecl ClosedBall
typedecl Real
typedecl S

datatype Nat = X0 | suc "Nat"

consts
MinusXXX :: "Real => Real"
VBarX__VBarX :: "Real => Real"
X0_2 :: "Real"
X1 :: "Real"
X2 :: "Real"
XXCXX :: "ClosedBall * ClosedBall => bool"
XXGtXEqXXX :: "Real * Real => bool"
XXGtXXX :: "Real * Real => bool"
XXLtXEqXXX_1 :: "(Real => bool) * Real => bool"
XXLtXEqXXX_2 :: "Real * (Real => bool) => bool"
XXLtXEqXXX_3 :: "Real * Real => bool"
XXLtXXX :: "Real * Real => bool"
XXMinusXXX :: "Real * Real => Real"
XXNTPXX :: "ClosedBall * ClosedBall => bool"
XXOXXX :: "ClosedBall * ClosedBall => bool"
XXPXX :: "ClosedBall * ClosedBall => bool"
XXPlusXXX :: "Real * Real => Real"
XXSlashXXX :: "Real * Real => Real option"
XXxXXX :: "Real * Real => Real"
closedBall :: "S * Real => ClosedBall"
d :: "S * S => Real"
half :: "Real => Real"
inf_1 :: "(Real => bool) => Real option"
inf_2 :: "Real * Real => Real option"
injX :: "Nat => Real"
isBounded :: "(Real => bool) => bool"
maxX :: "Real * Real => Real"
minX :: "Real * Real => Real"
nonempty :: "ClosedBall => bool"
rep :: "ClosedBall => S => bool"
sqrXX :: "Real => Real"
sqrtXX :: "Real => Real option"
sup_1 :: "(Real => bool) => Real option"
sup_2 :: "Real * Real => Real option"

lemma case_Nat_SomeProm [simp]:" (case caseVar of X0 => Some (x)
   | suc nat => Some (s nat)
) =
Some (case caseVar of X0 => x
   | suc nat => s nat
)"
apply (case_tac caseVar)
apply (auto)
done


instance ClosedBall::type
by intro_classes
instance Real::type
by intro_classes
instance S::type
by intro_classes

axioms
def_nonempty : "ALL x. op = (pApp (Some nonempty) (Some x)) (pApp (Some XXCXX) (pair (Some x) (Some x)))"

C_def : "pApp (Some XXCXX) (pair (Some x) (Some y)) = (EX s. pApp (apt (Some rep) (Some x)) (Some s) & pApp (apt (Some rep) (Some y)) (Some s))"

P_def : "pApp (Some XXPXX) (pair (Some x) (Some y)) = (ALL z. pApp (Some XXCXX) (pair (Some z) (Some x)) --> pApp (Some XXCXX) (pair (Some z) (Some y)))"

O_def : "pApp (Some XXOXXX) (pair (Some x) (Some y)) = (EX z. (pApp (Some XXCXX) (pair (Some z) (Some z)) & pApp (Some XXPXX) (pair (Some z) (Some x))) & pApp (Some XXPXX) (pair (Some z) (Some y)))"

NTP_def : "pApp (Some XXNTPXX) (pair (Some x) (Some y)) = (ALL z. pApp (Some XXCXX) (pair (Some z) (Some x)) --> pApp (Some XXOXXX) (pair (Some z) (Some y)))"

MS_pos [simp] : "pApp (Some XXLtXEqXXX_3) (pair (Some X0_2) (apt (Some d) (pair (Some x) (Some y))))"

MS_zero [simp] : "op = (apt (Some d) (pair (Some x) (Some x))) (Some X0_2)"

MS_pos_definite [simp] : "op = (apt (Some d) (pair (Some x) (Some y))) (Some X0_2) = op = (Some x) (Some y)"

MS_symm [simp] : "op = (apt (Some d) (pair (Some x) (Some y))) (apt (Some d) (pair (Some y) (Some x)))"

MS_triangle [simp] : "pApp (Some XXLtXEqXXX_3) (pair (apt (Some d) (pair (Some x) (Some z))) (apt (Some XXPlusXXX) (pair (apt (Some d) (pair (Some x) (Some y))) (apt (Some d) (pair (Some y) (Some z))))))"

one_greater_zero [simp] : "pApp (Some XXGtXXX) (pair (Some X1) (Some X0_2))"

zero_leq_one [simp] : "pApp (Some XXLtXEqXXX_3) (pair (Some X0_2) (Some X1))"

half_gt_zero [simp] : "pApp (Some XXGtXXX) (pair (Some r) (Some X0_2)) --> pApp (Some XXGtXXX) (pair (apt (Some half) (Some r)) (Some X0_2))"

half_plus_minus [simp] : "pApp (Some XXLtXEqXXX_3) (pair (Some r) (Some s)) --> pApp (Some XXLtXEqXXX_3) (pair (apt (Some XXPlusXXX) (pair (Some s) (apt (Some half) (apt (Some XXMinusXXX) (pair (Some r) (Some s)))))) (Some s))"

add_monotone [simp] : "pApp (Some XXLtXEqXXX_3) (pair (Some a) (Some b)) & pApp (Some XXLtXEqXXX_3) (pair (Some c) (Some e)) --> pApp (Some XXLtXEqXXX_3) (pair (apt (Some XXPlusXXX) (pair (Some a) (Some c))) (apt (Some XXPlusXXX) (pair (Some b) (Some e))))"

sub_leq [simp] : "~ pApp (Some XXLtXEqXXX_3) (pair (Some a) (Some b)) --> pApp (Some XXGtXXX) (pair (apt (Some XXMinusXXX) (pair (Some a) (Some b))) (Some X0_2))"

half_leq [simp] : "pApp (Some XXLtXEqXXX_3) (pair (Some a) (apt (Some XXPlusXXX) (pair (apt (Some half) (apt (Some XXMinusXXX) (pair (Some a) (Some b)))) (Some b)))) --> pApp (Some XXLtXEqXXX_3) (pair (Some a) (Some b))"

half_leq_zero [simp] : "pApp (Some XXLtXEqXXX_3) (pair (Some X0_2) (Some r)) --> pApp (Some XXLtXEqXXX_3) (pair (Some X0_2) (apt (Some half) (Some r)))"

comm_add [simp] : "op = (apt (Some XXPlusXXX) (pair (Some a) (Some b))) (apt (Some XXPlusXXX) (pair (Some b) (Some a)))"

Real_abs_def [simp] : "op = (apt (Some VBarX__VBarX) (Some r)) (apt (Some maxX) (pair (Some r) (apt (Some MinusXXX) (Some r))))"

Real_sqr_def [simp] : "op = (apt (Some sqrXX) (Some r)) (apt (Some XXxXXX) (pair (Some r) (Some r)))"

Real_sqrt_dom [simp] : "defOp (app (Some sqrtXX) (Some r)) = pApp (Some XXGtXEqXXX) (pair (Some r) (Some X0_2))"

Real_sqrt_def [simp] : "op = (app (Some sqrtXX) (apt (Some sqrXX) (Some r))) (apt (Some VBarX__VBarX) (Some r))"

Real_2_def [simp] : "op = (Some X2) (apt (Some XXPlusXXX) (pair (Some X1) (Some X1)))"

Real_minus_def [simp] : "op = (apt (Some XXMinusXXX) (pair (Some r) (Some r'))) (apt (Some XXPlusXXX) (pair (Some r) (apt (Some MinusXXX) (Some r'))))"

Real_divide_dom [simp] : "~ defOp (app (Some XXSlashXXX) (pair (Some r) (Some X0_2)))"

Real_divide_def [simp] : "op = (app (Some XXSlashXXX) (pair (Some r) (Some r'))) (Some r'') = op = (apt (Some XXxXXX) (pair (Some r'') (Some r'))) (Some r)"

Real_half_def [simp] : "op = (apt (Some XXxXXX) (pair (Some X2) (apt (Some half) (Some r)))) (Some r)"

ga_Nat [simp] : "True"

Real_ub_def : "pApp (Some XXLtXEqXXX_1) (pair (Some M) (Some r)) = (ALL s. pApp (Some M) (Some s) --> pApp (Some XXLtXEqXXX_3) (pair (Some s) (Some r)))"

Real_lb_def : "pApp (Some XXLtXEqXXX_2) (pair (Some r) (Some M)) = (ALL s. pApp (Some M) (Some s) --> pApp (Some XXLtXEqXXX_3) (pair (Some r) (Some s)))"

Real_inf_def : "op = (app (Some inf_1) (Some M)) (Some r) = (pApp (Some XXLtXEqXXX_2) (pair (Some r) (Some M)) & (ALL s. pApp (Some XXLtXEqXXX_2) (pair (Some s) (Some M)) --> pApp (Some XXLtXEqXXX_3) (pair (Some s) (Some r))))"

Real_sup_def : "op = (app (Some sup_1) (Some M)) (Some r) = (pApp (Some XXLtXEqXXX_1) (pair (Some M) (Some r)) & (ALL s. pApp (Some XXLtXEqXXX_1) (pair (Some M) (Some s)) --> pApp (Some XXLtXEqXXX_3) (pair (Some r) (Some s))))"

Real_isBounded_defCBrX : "pApp (Some isBounded) (Some M) = (EX ub. EX lb. pApp (Some XXLtXEqXXX_2) (pair (Some lb) (Some M)) & pApp (Some XXLtXEqXXX_1) (pair (Some M) (Some ub)))"

Real_inj_0 [simp] : "op = (apt (Some injX) (Some X0_1)) (Some X0_2)"

Real_inj_suc [simp] : "op = (apt (Some injX) (apt (Some suc) (Some nX))) (apt (Some XXPlusXXX) (pair (Some X1) (apt (Some injX) (Some nX))))"

Real_archimedian : "EX nX. pApp (Some XXLtXEqXXX_3) (pair (Some r) (apt (Some injX) (Some nX)))"

FWO_plus_right : "ALL a. ALL b. ALL c. pApp (Some XXLtXEqXXX_3) (pair (Some b) (Some c)) --> pApp (Some XXLtXEqXXX_3) (pair (apt (Some XXPlusXXX) (pair (Some a) (Some b))) (apt (Some XXPlusXXX) (pair (Some a) (Some c))))"

FWO_times_right : "ALL a. ALL b. ALL c. pApp (Some XXLtXEqXXX_3) (pair (Some b) (Some c)) & pApp (Some XXLtXEqXXX_3) (pair (Some X0_2) (Some a)) --> pApp (Some XXLtXEqXXX_3) (pair (apt (Some XXxXXX) (pair (Some a) (Some b))) (apt (Some XXxXXX) (pair (Some a) (Some c))))"

FWO_plus_left : "ALL a. ALL b. ALL c. pApp (Some XXLtXEqXXX_3) (pair (Some a) (Some b)) --> pApp (Some XXLtXEqXXX_3) (pair (apt (Some XXPlusXXX) (pair (Some a) (Some c))) (apt (Some XXPlusXXX) (pair (Some b) (Some c))))"


FWO_plus : "ALL a. ALL b. ALL c. ALL d. pApp (Some XXLtXEqXXX_3) (pair (Some a) (Some c)) & pApp (Some XXLtXEqXXX_3) (pair (Some b) (Some d)) --> pApp (Some XXLtXEqXXX_3) (pair (apt (Some XXPlusXXX) (pair (Some a) (Some b))) (apt (Some XXPlusXXX) (pair (Some c) (Some d))))"


FWO_times_left : "ALL a. ALL b. ALL c. pApp (Some XXLtXEqXXX_3) (pair (Some a) (Some b)) & pApp (Some XXLtXEqXXX_3) (pair (Some X0_2) (Some c)) --> pApp (Some XXLtXEqXXX_3) (pair (apt (Some XXxXXX) (pair (Some a) (Some c))) (apt (Some XXxXXX) (pair (Some b) (Some c))))"

Field_unary_minus_def : "ALL x. op = (apt (Some XXPlusXXX) (pair (apt (Some MinusXXX) (Some x)) (Some x))) (Some X0_2)"

dichotomy_TotalOrder : "ALL x. ALL y. pApp (Some XXLtXEqXXX_3) (pair (Some x) (Some y)) | pApp (Some XXLtXEqXXX_3) (pair (Some y) (Some x))"

antisym : "ALL x. ALL y. pApp (Some XXLtXEqXXX_3) (pair (Some x) (Some y)) & pApp (Some XXLtXEqXXX_3) (pair (Some y) (Some x)) --> op = (Some x) (Some y)"

trans : "ALL x. ALL y. ALL z. pApp (Some XXLtXEqXXX_3) (pair (Some x) (Some y)) & pApp (Some XXLtXEqXXX_3) (pair (Some y) (Some z)) --> pApp (Some XXLtXEqXXX_3) (pair (Some x) (Some z))"

refl : "ALL x. pApp (Some XXLtXEqXXX_3) (pair (Some x) (Some x))"

min_inf_relation : "ALL x. ALL y. op = (apt (Some minX) (pair (Some x) (Some y))) (app (Some inf_2) (pair (Some x) (Some y)))"

max_sup_relation : "ALL x. ALL y. op = (apt (Some maxX) (pair (Some x) (Some y))) (app (Some sup_2) (pair (Some x) (Some y)))"

ga_comm_min : "ALL x. ALL y. op = (apt (Some minX) (pair (Some x) (Some y))) (apt (Some minX) (pair (Some y) (Some x)))"

ga_comm_max : "ALL x. ALL y. op = (apt (Some maxX) (pair (Some x) (Some y))) (apt (Some maxX) (pair (Some y) (Some x)))"

ga_assoc_min : "ALL x. ALL y. ALL z. op = (apt (Some minX) (pair (Some x) (apt (Some minX) (pair (Some y) (Some z))))) (apt (Some minX) (pair (apt (Some minX) (pair (Some x) (Some y))) (Some z)))"

ga_assoc_max : "ALL x. ALL y. ALL z. op = (apt (Some maxX) (pair (Some x) (apt (Some maxX) (pair (Some y) (Some z))))) (apt (Some maxX) (pair (apt (Some maxX) (pair (Some x) (Some y))) (Some z)))"

min_def_ExtTotalOrder : "ALL x. ALL y. op = (apt (Some minX) (pair (Some x) (Some y))) (if pApp (Some XXLtXEqXXX_3) (pair (Some x) (Some y)) then Some x else Some y)"

max_def_ExtTotalOrder : "ALL x. ALL y. op = (apt (Some maxX) (pair (Some x) (Some y))) (if pApp (Some XXLtXEqXXX_3) (pair (Some x) (Some y)) then Some y else Some x)"

ga_comm_inf : "ALL x. ALL y. op = (app (Some inf_2) (pair (Some x) (Some y))) (app (Some inf_2) (pair (Some y) (Some x)))"

ga_comm_sup : "ALL x. ALL y. op = (app (Some sup_2) (pair (Some x) (Some y))) (app (Some sup_2) (pair (Some y) (Some x)))"

inf_def_ExtPartialOrder : "ALL x. ALL y. ALL z. op = (app (Some inf_2) (pair (Some x) (Some y))) (Some z) = (pApp (Some XXLtXEqXXX_3) (pair (Some z) (Some x)) & pApp (Some XXLtXEqXXX_3) (pair (Some z) (Some y)) & (ALL t. pApp (Some XXLtXEqXXX_3) (pair (Some t) (Some x)) & pApp (Some XXLtXEqXXX_3) (pair (Some t) (Some y)) --> pApp (Some XXLtXEqXXX_3) (pair (Some t) (Some z))))"

sup_def_ExtPartialOrder : "ALL x. ALL y. ALL z. op = (app (Some sup_2) (pair (Some x) (Some y))) (Some z) = (pApp (Some XXLtXEqXXX_3) (pair (Some x) (Some z)) & pApp (Some XXLtXEqXXX_3) (pair (Some y) (Some z)) & (ALL t. pApp (Some XXLtXEqXXX_3) (pair (Some x) (Some t)) & pApp (Some XXLtXEqXXX_3) (pair (Some y) (Some t)) --> pApp (Some XXLtXEqXXX_3) (pair (Some z) (Some t))))"

geq_def_ExtPartialOrder : "ALL x. ALL y. pApp (Some XXGtXEqXXX) (pair (Some x) (Some y)) = pApp (Some XXLtXEqXXX_3) (pair (Some y) (Some x))"

less_def_ExtPartialOrder : "ALL x. ALL y. pApp (Some XXLtXXX) (pair (Some x) (Some y)) = (pApp (Some XXLtXEqXXX_3) (pair (Some x) (Some y)) & ~ op = (Some x) (Some y))"

greater_def_ExtPartialOrder : "ALL x. ALL y. pApp (Some XXGtXXX) (pair (Some x) (Some y)) = pApp (Some XXLtXXX) (pair (Some y) (Some x))"

EMSCD_rep_pos [simp] : "pApp (Some XXGtXXX) (pair (Some r) (Some X0_2)) --> pApp (apt (Some rep) (apt (Some closedBall) (pair (Some x) (Some r)))) (Some y) = pApp (Some XXLtXEqXXX_3) (pair (apt (Some d) (pair (Some x) (Some y))) (Some r))"

EMSCD_rep_0 [simp] : "~ pApp (Some XXGtXXX) (pair (Some r) (Some X0_2)) --> ~ pApp (apt (Some rep) (apt (Some closedBall) (pair (Some x) (Some r)))) (Some y)"

EMSCD_rep_inj : "op = (apt (Some rep) (Some a)) (apt (Some rep) (Some b)) --> op = (Some a) (Some b)"

Ax4 : "EX z. EX t. op = (Some a) (apt (Some closedBall) (pair (Some z) (Some t)))"

ga_Nat_1 [simp] : "True"

lemmas P_def' = P_def [simplified]
lemmas C_def' = C_def [simplified]
lemmas O_def' = O_def [simplified]
lemmas NTP_def' = NTP_def [simplified]
lemmas Ax4' = Ax4 [simplified]
lemmas EMSCD_rep_pos' = EMSCD_rep_pos [simplified]
lemmas EMSCD_rep_0' = EMSCD_rep_0 [simplified, THEN mp]
(*lemmas Real_minus_pos' = Real_minus_pos [simplified, THEN mp]
lemmas Real_half_pos' = Real_half_pos [simplified, THEN mp]*)
lemmas MS_triangle' = MS_triangle [simplified]
lemmas FWO_plus_left' = FWO_plus_left [simplified]
lemmas EMSCD_rep_inj' = EMSCD_rep_inj [simplified]
(*lemmas MS_identity' = MS_identity [simplified] *)
lemmas MS_pos_definite' = MS_pos_definite [simplified]
lemmas less_def_ExtPartialOrder' = less_def_ExtPartialOrder [simplified]
lemmas greater_def_ExtPartialOrder' = greater_def_ExtPartialOrder [simplified]
lemmas FWO_plus_right' = FWO_plus_right [simplified]
lemmas MS_symm' = MS_symm [simplified]
lemmas trans' = trans[simplified, THEN spec, THEN spec, THEN spec, THEN mp]
lemmas sub_leq'= sub_leq [simplified, THEN mp]
lemmas half_plus_minus' = half_plus_minus[simplified, THEN mp]
lemmas half_leq' = half_leq[simplified, THEN mp]
lemmas half_gt_zero' = half_gt_zero[simplified, THEN mp]
lemmas half_leq_zero' = half_leq_zero[simplified, THEN mp]
lemmas comm_add' = comm_add[simplified]

declare P_def' [simp]
declare C_def' [simp]
declare O_def' [simp]
declare NTP_def' [simp]
declare EMSCD_rep_pos' [simp]
declare EMSCD_rep_0' [simp]



theorem P_def_1 : "ALL x. ALL y. pApp (Some XXPXX) (pair (Some x) (Some y)) = (ALL z. pApp (Some XXCXX) (pair (Some z) (Some x)) --> pApp (Some XXCXX) (pair (Some z) (Some y)))"
by auto

ML "Header.record \"P_def_1\""

theorem O_def_1 : "ALL x. ALL y. pApp (Some XXOXXX) (pair (Some x) (Some y)) = (EX z. pApp (Some XXCXX) (pair (Some z) (Some z)) & pApp (Some XXPXX) (pair (Some z) (Some x)) & pApp (Some XXPXX) (pair (Some z) (Some y)))"
by auto

ML "Header.record \"O_def_1\""

theorem NTP_def_1 : "ALL x. ALL y. pApp (Some XXNTPXX) (pair (Some x) (Some y)) = (ALL z. pApp (Some XXCXX) (pair (Some z) (Some x)) --> pApp (Some XXOXXX) (pair (Some z) (Some y)))"
by auto

ML "Header.record \"NTP_def_1\""

theorem C_non_null : "ALL x. ALL y. pApp (Some XXCXX) (pair (Some x) (Some y)) --> pApp (Some XXCXX) (pair (Some x) (Some x))"
by auto

ML "Header.record \"C_non_null\""

theorem C_sym : "ALL x. ALL y. pApp (Some XXCXX) (pair (Some x) (Some y)) --> pApp (Some XXCXX) (pair (Some y) (Some x))"
by auto

ML "Header.record \"C_sym\""


theorem C_id : "ALL x. ALL y. (ALL z. pApp (Some XXCXX) (pair (Some z) (Some x)) = pApp (Some XXCXX) (pair (Some z) (Some y))) --> op = (Some x) (Some y)" 

apply (simp)
proof 
  fix x
  show "ALL y.
            (ALL z.
                (EX s. rep z s & rep x s) = (EX s. rep z s & rep y s)) -->
            x = y"
    proof
      fix y
      pr
      show "(ALL z.
                (EX s. rep z s & rep x s) = (EX s. rep z s & rep y s)) -->
            x = y"
	proof 
	  assume "(ALL z.
                (EX s. rep z s & rep x s) = (EX s. rep z s & rep y s))"
	  then show "x=y"
	    proof (rule contrapos_pp)
	      assume "x~=y"
	      with EMSCD_rep_inj' have "rep x ~= rep y" by blast
	      with ext [of "rep x"]  obtain p where sep: "rep x p ~= rep y p" 
		by blast
	      moreover from Ax4' obtain qx rx 
		where coordx: "x = closedBall (qx, rx)" 
		by blast
	      moreover from Ax4' obtain qy ry 
		where coordy: "y = closedBall (qy, ry)" 
		by blast
	      have "EX z. (EX s. rep z s & rep x s) ~= 
		(EX s. rep z s & rep y s)"
	      proof (cases "rep x p")
		case True
		note outerTrue = True
		with sep have p_notin_y: "~ rep y p" by blast
		from True EMSCD_rep_0' coordx have rx_pos: "XXGtXXX (rx,X0_2)"
		  by blast
		show ?thesis
		  proof (cases "XXGtXXX (ry,X0_2)")
		    case True
		    with coordy p_notin_y EMSCD_rep_pos'
		    have p_outside_ry: "~XXLtXEqXXX_3 (d(qy,p),ry)"
		      by blast
		    with sub_leq'
		    have pos_dist: "XXGtXXX (XXMinusXXX(d(qy,p),ry),X0_2)"
		      by blast
		    with half_gt_zero'
		    have pos_half_dist: "XXGtXXX 
		      (half(XXMinusXXX(d(qy,p),ry)),X0_2)"
		      by blast
		    with EMSCD_rep_pos' MS_zero[simplified] less_def_ExtPartialOrder'
		       greater_def_ExtPartialOrder' 
		    have "rep (closedBall 
		      (p,half(XXMinusXXX(d(qy,p),ry)))) p"
		      by simp
		    with  outerTrue have meetx: "EX s. rep (closedBall 
		      (p,half(XXMinusXXX(d(qy,p),ry)))) s
		      & rep x s" by blast
		    have not_meet_y: "~ (EX s. rep (closedBall 
		      (p,half(XXMinusXXX(d(qy,p),ry)))) s
		      & rep y s)"
		      proof
			assume "EX s. rep (closedBall (p, 
			  half (XXMinusXXX (d (qy, p), ry)))) s &
			  rep y s"
			then obtain s where s_in_meet: 
			  "rep (closedBall (p, 
			  half (XXMinusXXX (d (qy, p), ry)))) s &
			  rep y s" by blast
			with coordy True have s_within_ry:
			  "XXLtXEqXXX_3 (d(qy,s),ry)" by simp
			from s_in_meet pos_half_dist MS_symm' 
			have s_within_dist:
			  "XXLtXEqXXX_3 (d(s,p),
			  half (XXMinusXXX (d (qy, p), ry)))" by simp
			with s_within_ry MS_triangle' [of "qy" "p" "s"] 
			  trans[simplified]
			  of "d(qy,p)" "XXPlusXXX(d(qy,s),d(s,p))"]
			FWO_plus[simplified] 
			have "XXLtXEqXXX_3 (d(qy,p),
			  XXPlusXXX(ry,half (XXMinusXXX (d (qy, p), ry))))"
			  by blast
			  
			  apply (auto)
			  apply (rule trans')
			  apply (rule conjI)
			  apply (assumption)
			  apply (rule FWO_plus[simplified,THEN spec, THEN spec, THEN spec, THEN spec, THEN mp]) 
			  apply (rule conjI)
			  
			  
			  
			  
			  			
		    
		      
		    




lemma swap : "A --> B=C ==> B ==> A-->C"
by auto

lemma impLemma : "[| A; A==>B; B-->C|] ==> C"
by auto

lemma reflLemma : "x=y ==> XXLtXEqXXX_3 (x,y)"
using refl[simplified] by auto

thm MS_triangle[simplified]

lemma MS_triangle_rev : "XXLtXEqXXX_3 (d (x, z), XXPlusXXX (d (x, y), d (z, y)))"
by (simp add: MS_triangle[simplified] MS_symm[simplified])

lemma C_id_lemma : "!!x y xa. \ 
       ALL z. (EX s. rep z s & rep x s) = (EX s. rep z s & rep y s) \
       ==> rep x xa ==> rep y xa"
apply (erule contrapos_pp)
apply (subst not_all)
apply (insert Ax4' [THEN allI, of "%x. x"])
apply (frule_tac x="x" in spec)
apply (drule_tac x="y" in spec)
apply (erule exE)
apply (erule exE)
apply (erule exE)
apply (erule exE)
apply (subst not_iff)
apply (case_tac "XXGtXXX (ta,X0_2)")
apply (rule_tac x="closedBall(xa,half (XXMinusXXX (d(za,xa),ta)))" in exI)
apply(auto)
apply((drule EMSCD_rep_pos [simplified, THEN swap])+)
apply(rule_tac P="XXLtXEqXXX_3 (d (za, xa), ta)" in notE)
apply(assumption)
apply(rule half_leq')
apply(rule trans')
apply(rule conjI)
defer
apply(rule add_monotone[simplified, THEN mp])
apply(rule conjI)
apply(erule mp)
back
apply(insert sub_leq')
apply(rule half_gt_zero')
apply(rule sub_leq')
apply(assumption+)

apply(rule_tac x="xa" in exI)
apply(simp)
apply(rule EMSCD_rep_pos [simplified, THEN mp, THEN iffD2])
apply(rule half_gt_zero')
apply(rule sub_leq')
apply(assumption)
apply(simp add: MS_zero[simplified])
apply(rule half_leq_zero')
apply(drule sub_leq')
apply(simp add: greater_def_ExtPartialOrder[simplified]
                less_def_ExtPartialOrder[simplified])
apply(rule trans')
apply(rule conjI)
defer
apply(rule MS_triangle_rev)
apply(rule reflLemma)
apply(rule MS_symm')
done

theorem C_id : "ALL x. ALL y. (ALL z. pApp (Some XXCXX) (pair (Some z) (Some x)) = pApp (Some XXCXX) (pair (Some z) (Some y))) --> op = (Some x) (Some y)"
apply (simp del: C_def C_def')
apply (auto)
apply (rule EMSCD_rep_inj [THEN mp, simplified])
apply (rule ext)
apply (auto)
apply (rule_tac x="x" in C_id_lemma)
apply(auto)
apply (rule_tac x="y" in C_id_lemma)
apply(auto)
done


ML "Header.record \"C_id\""

theorem C_non_triv : "EX x. pApp (Some XXCXX) (pair (Some x) (Some x))"
apply auto
apply (rule exI)
apply (rule exI)
apply (rule EMSCD_rep_pos [THEN mp, simplified, THEN iffD2])
apply(rule one_greater_zero [simplified])
apply(rule iffD2)
apply(rule arg_cong)
back
defer
apply(rule zero_leq_one [simplified]) 
using MS_pos_definite apply simp
done

ML "Header.record \"C_non_triv\""

theorem Ax1 : "ALL x. pApp (Some nonempty) (Some x) = pApp (Some XXCXX) (pair (Some x) (Some x))"
using def_nonempty by auto

ML "Header.record \"Ax1\""

end
