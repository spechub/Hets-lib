theory dsefSyntax = gdjSyntax + Lemmabase:

text{* Seqences fulfilling all three (sef, cp, com) properties are called deterministic 
  sideeffect free*}
constdefs
  "dsef" :: "'a T \<Rightarrow> bool"
  "dsef p == (sef p) \<and> (cp p) \<and> (\<forall>q. (p comwith q))"

text {*
  Introducing the subtype @{text "('a D)"} of @{text "('a T)"} comprising the dsef programs;
  since Isabelle lacks true subtyping, it is simply declared as a new type
  with coercion functions 
@{text "    Rep_Dsef :: 'a D \<Rightarrow> 'a T"}
  and 
@{text "    Abs_Dsef :: 'a T \<Rightarrow> 'a D"}
  where (Abs\_Dsef p) is of course only sensibly defined if (dsef p) holds.
*}

(*the proof is the same as dsef_ret. Just to make it easier
  to avoid cycles in theories I proved it here again*)
typedef (Dsef) ('a) D = "{p::'a T. dsef p}"
(* {{{ Proof }}} *)
  apply(rule_tac x = "ret x" in exI)
  apply (unfold dsef_def)
  apply (simp add: cp_def)
  apply (simp add: sef_def com_def del:delBind)
  apply (rule allI)
  apply (simp add: com_def)
  by (simp add: weak_cp2retSeq)(* }}} *)


(* {{{ Don't want to write Rep\_Dsef and Abs\_Dsef while building HoareCalc-Theory.
  . and # are just syntactic sugar for these both}}} *)
syntax
  Rep :: "'a D \<Rightarrow> 'a T"  ("\<down>_")
  Abs :: "'a T \<Rightarrow> 'a D" ("\<up>_")
  Ret :: "'a \<Rightarrow> 'a D" ("\<Up>_")

translations
  "\<down>p" == "Rep_Dsef p"
  "\<up>p" == "Abs_Dsef p"
  "\<Up>p" == "\<up>(ret p)"
  
lemma avoidAbsRep [simp]: "Abs_Dsef (Rep_Dsef p) = p"
  by (rule Rep_Dsef_inverse)

lemma avoidRepAbs [simp]:"p \<in> Dsef \<Longrightarrow> Rep_Dsef (Abs_Dsef p) = p"
  by (rule Abs_Dsef_inverse)

lemma avoidAbsRep' [simp]:"\<up>\<down>(p::'a D) == p"
  by (simp add: Rep_Dsef_inverse)

lemma avoidRepAbs' [simp]:"p \<in> Dsef \<Longrightarrow> (\<down>\<up>(p::'a T)) == p"
  by (simp add: Abs_Dsef_inverse)
(* }}} *)

constdefs 
  if\<^isub>D :: "bool D \<Rightarrow> 'a T \<Rightarrow> 'a T \<Rightarrow> 'a T"   ("if\<^isub>D (_) then (_) else (_)")
  "if\<^isub>D b then p else q == do{x\<leftarrow>\<down>b;if x then p else q}" 

consts  
  iter\<^isub>D:: "('a \<Rightarrow> bool D) \<Rightarrow> ('a \<Rightarrow> 'a T) \<Rightarrow> 'a \<Rightarrow> 'a T"
  while\<^isub>D :: "bool D \<Rightarrow> unit T \<Rightarrow> unit T" ("while\<^isub>D (_) (_)")

axioms
  iter\<^isub>D_def: "iter\<^isub>D test f x = 
       do{if\<^isub>D (test x) then (do{y\<leftarrow>(f x);iter\<^isub>D test f y}) else (ret x)}"

  while\<^isub>D_def: "while\<^isub>D b p == iter\<^isub>D (\<lambda>x. b) (\<lambda>x. p) ()"
(* }}} *)

(* {{{ all kinds of Hoare-Pre/Post-Conditions }}} *)
constdefs
  condConj :: "bool D \<Rightarrow> bool D \<Rightarrow> bool D"   ("(_\<and>\<^isub>D _)")
  "condConj \<Phi> \<xi> \<equiv> \<up>do{x\<leftarrow>\<down>\<Phi>;y\<leftarrow>\<down>\<xi>;ret(x\<and>y)}"  
  condDisj :: "bool D \<Rightarrow> bool D \<Rightarrow> bool D"   ("(_\<or>\<^isub>D _)")
  "condDisj \<Phi> \<xi> \<equiv> \<up>do{x\<leftarrow>\<down>\<Phi>;y\<leftarrow>\<down>\<xi>;ret(x\<or>y)}"
  condNot :: "bool D \<Rightarrow> bool D"             ("\<not>\<^isub>D_") 
  "condNot \<Phi> \<equiv> \<up>do{x\<leftarrow>\<down>\<Phi>;ret(\<not>x)}"
(* }}} *)

end