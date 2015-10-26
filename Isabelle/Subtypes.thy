theory Subtypes
imports MainHC
begin

consts

X_gn_inj :: "'a => 'b" ("gn'_inj/'(_')" [3] 999)
X_gn_proj :: "'a => 'b partial" ("gn'_proj/'(_')" [3] 999)
X_gn_subt :: "'a => 'b => bool" ("gn'_subt/'(_,/ _')" [3,3] 999)



axioms
ga_subt_reflexive [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). gn_subt(x, y)"

ga_subt_transitive [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'b).
 ALL (z :: 'c). gn_subt(x, y) & gn_subt(y, z) --> gn_subt(x, z)"

ga_subt_inj_proj [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'b).
 gn_subt(x, y) -->
 y = (X_gn_inj :: 'a => 'b) x =
 (makePartial x = (X_gn_proj :: 'b => 'a partial) y)"

ga_inj_transitive [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'b).
 ALL (z :: 'c).
 gn_subt(x, y) & gn_subt(y, z) & y = (X_gn_inj :: 'a => 'b) x -->
 z = (X_gn_inj :: 'a => 'c) x = (z = (X_gn_inj :: 'b => 'c) y)"


lemma subtype_reflexive:
"X_gn_subt (x:: 'a) (y:: 'a)" by (rule ga_subt_reflexive)

lemma subtype_transitive:
"[| X_gn_subt (x:: 'a) (y:: 'b); X_gn_subt (z:: 'b) (t:: 'c) |]  ==> X_gn_subt (u:: 'a) (v:: 'c)"
proof-
  assume hypAB: "X_gn_subt (x:: 'a) (y:: 'b)"
  assume hypBC: "X_gn_subt (z:: 'b) (t:: 'c)"
  have A: "X_gn_subt u y" by (rule ga_subt_transitive [of u x y], simp add: ga_subt_reflexive hypAB)
  have B: "X_gn_subt y t" by (rule ga_subt_transitive [of y z t], simp add: ga_subt_reflexive hypBC)
  have C: "X_gn_subt u t" by (rule ga_subt_transitive [of u y t], simp add: A B)
  show "X_gn_subt u v" by (rule ga_subt_transitive [of u t v], simp add: ga_subt_reflexive C)
qed

-- "necessary when omitting the quantifiers in the axioms below"
lemma subtype_constant:
"X_gn_subt (x:: 'a) (y:: 'b) ==> (!!(u:: 'a) v:: 'b. X_gn_subt u v)"
proof-
  assume hyp: "X_gn_subt x y"
  fix u:: 'a
  fix v:: 'b
  show "X_gn_subt u v"


 by (rule subtype_transitive [of x x x y u v], (simp only: ga_subt_reflexive hyp)+)
qed


-- "INJECTION PROJECTION RULES"

lemma gn_proj_inj:
"X_gn_subt (x:: 'a) (y:: 'b) ==> (!!(z:: 'a). makePartial(z) = gn_proj(gn_inj(z):: 'b))"
proof-
  assume hyp: "X_gn_subt x y"
  fix z :: 'a

  have "(gn_inj(z) :: 'b) = gn_inj(z) = (makePartial z = gn_proj(gn_inj(z) :: 'b))"
    by (rule ga_subt_inj_proj, rule subtype_constant [of x y], simp only: hyp)
  thus "makePartial z = gn_proj(gn_inj(z) :: 'b)" by simp
qed

lemma gn_makeTotal_proj_inj:
"X_gn_subt (x:: 'a) (y:: 'b) ==> (!!(z:: 'a). makeTotal(gn_proj(gn_inj(z):: 'b)) = z)"
 by (simp only: partial_identity gn_proj_inj [symmetric])


-- "is used to derive defining predicate P for a subtype A, P(gn_inj(x::A))"
lemma gn_proj_def:
"X_gn_subt (x:: 'a) (y:: 'b) ==> defOp(gn_proj(gn_inj(x):: 'b):: 'a partial)"
proof-
  assume hyp: "gn_subt(x, y)"
  hence A: "makePartial(x) = gn_proj(gn_inj(x):: 'b)" by (rule gn_proj_inj [of x y x])
  show "defOp(gn_proj(gn_inj(x):: 'b):: 'a partial)"
    by (simp add: A [symmetric] makePartial_def)
qed

(*
lemma gn_inj_proj:
"X_gn_subt (x:: 'a) (y:: 'b) ==> (!!(z:: 'b). defOp(gn_proj(z):: 'a partial) ==>
  gn_inj(makeTotal(gn_proj(z):: 'a partial)) = z)"
proof-
  assume hyp: "gn_subt(x, y)"
  fix z :: 'b
  assume hyp': "defOp(gn_proj(z):: 'a partial)"
  have "EX (t :: 'a). gn_proj(z) = makePartial t"
    by (rule defOp_implies_makePartial [of "gn_proj(z)"], simp only: hyp')
  then obtain t :: 'a where eq1: "makePartial t = gn_proj(z)" by auto
  from hyp have A: "gn_subt(t, z)" by (simp only: subtype_constant)
  have B: "t=makeTotal(gn_proj(gn_inj(t):: 'b)) "
    by (rule gn_makeTotal_proj_inj [symmetric,of x y], simp only: hyp)
  have C: "z = gn_inj(t)"
    by (simp only: ga_subt_inj_proj subtype_reflexive A eq1)
  also have "\<dots> = gn_inj(makeTotal(gn_proj(gn_inj(t):: 'b)):: 'a)"
    by (subst B, simp)
  also have "\<dots> = gn_inj(makeTotal(gn_proj(z)):: 'a)" by (simp only: C)
  finally show "gn_inj(makeTotal(gn_proj(z)):: 'a) = z" ..
qed
*)

lemma gn_inj_diagram:
"[| X_gn_subt (x:: 'a) (y:: 'b); X_gn_subt (z:: 'b) (t:: 'c) |]
  ==> (!!(x':: 'a). (gn_inj(x'):: 'c) = gn_inj(gn_inj(x'):: 'b))"
proof-
  assume hypAB: "X_gn_subt (x:: 'a) (y:: 'b)"
  assume hypBC: "X_gn_subt (z:: 'b) (t:: 'c)"
  fix x' :: 'a

  def y_def: y' == "gn_inj(x'):: 'b"
  def z_def: z' == "gn_inj(x'):: 'c"

  from hypAB hypBC have A: "gn_subt(x',y') \<and> gn_subt(y',z')"
    by (simp add: subtype_constant)

  have B: "(z' = gn_inj(x')) = (z' = gn_inj(y'))"
    by (rule ga_inj_transitive [of x' y' z'], simp only: A, simp add: y_def)

  show "(gn_inj(x'):: 'c) = gn_inj(gn_inj(x'):: 'b)"
    by (simp only:  y_def [symmetric] z_def [symmetric], subst B [symmetric]
      , simp only: z_def)
qed

lemma gn_inj_injective :
  "X_gn_subt (u :: 'a) (v:: 'b) ==> inj (X_gn_inj :: 'a => 'b)"
  proof (rule injI)
    fix x:: 'a
    fix y:: 'a
    assume hyp1: "X_gn_subt (u:: 'a) (v:: 'b)"
      and hyp2: "(X_gn_inj x :: 'b) = X_gn_inj y"

    from hyp1 subtype_constant 
    have fact: "!!(z:: 'a). makeTotal(gn_proj(gn_inj(z):: 'b)) = z"
      by (rule_tac gn_makeTotal_proj_inj, blast)

    hence "x = makeTotal(gn_proj(gn_inj(x):: 'b))" ..
    also from hyp2 have "... = makeTotal(gn_proj(gn_inj(y):: 'b))" by simp
    also from fact have "... = y" by simp
    finally show "x = y" by simp
  qed

lemma gn_inj_identity :
"!!x:: 'a. (gn_inj(x):: 'a) = x"
proof-
  fix x:: 'a
  have fact: "(gn_inj(x):: 'a) = gn_inj(gn_inj(x):: 'a)"
    by (simp_all add: gn_inj_diagram subtype_reflexive)
  thus "(gn_inj(x):: 'a) = x"
    by (subst injD [of "(X_gn_inj:: 'a=>'a)" "(gn_inj(x):: 'a)" x],
      simp_all only: gn_inj_injective subtype_reflexive fact [symmetric])
qed


end
