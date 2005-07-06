header {* A Deterministic Parser Monad with Fall Back Alternatives *}

theory Parsec = PDL + MonEq:


text {*
  In a typical implementation of this parser monad, @{term "T"} would have the 
  form @{text "T A = (S \<Rightarrow> (E + A) \<times> S)"}, i.e. it would be a state monad (over states
  $S$) with exceptions of type $E$. The fall back alternative @{term "q"} in
  @{text "p\<parallel>q"} would then only be used if @{term "p"} failed to terminate.
*}


consts
  item       :: "nat T"      -- {* Parses exactly one character (natural number) *}
  fail       :: "'a T"       -- {* Always fails *}
  alt        :: "'a T \<Rightarrow> 'a T \<Rightarrow> 'a T" (infixl "\<parallel>" 140) -- {* Prefer first parser, but fall back on second if necessary *}
  getInput   :: "nat list T" -- {* read the current state *}
  setInput   :: "nat list \<Rightarrow> unit T" 


constdefs 
  eot :: "bool T"
  "eot == (do {i \<leftarrow> getInput; ret (null i)})"
  Eot :: "bool D"
  "Eot == \<Up> eot"
  GetInput :: "nat list D"
  "GetInput == \<Up> getInput"
text {* 
@{term "GetInput"} and @{term "Eot"} are the abstractions in @{typ "'a D"} of the
resp. lower case terms in @{typ "'a T"}
*}



axioms
  dsef_getInput: "dsef getInput"
  fail_bot: "\<turnstile> [# fail](\<lambda>x. Ret False)"
  eot_item: "\<turnstile> Eot \<longrightarrow>\<^sub>D [# x\<leftarrow>item](Ret False)"
  set_get:  "\<turnstile> [# setInput x](\<lambda>u. GetInput =\<^sub>D Ret x)"
  get_item: "\<turnstile> GetInput =\<^sub>D Ret xs \<longrightarrow>\<^sub>D [# x\<leftarrow>item](Ret (x = hd xs) \<and>\<^sub>D GetInput =\<^sub>D Ret (tl xs))"
  altB_iff: "\<turnstile> [# x\<leftarrow>p\<parallel>q](P x) \<longleftrightarrow>\<^sub>D [# x\<leftarrow>p](P x) \<and>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Ret True) \<or>\<^sub>D [# x\<leftarrow>q](P x) \<and>\<^sub>D [# x\<leftarrow>p](Ret False)"
  altD_iff: "\<turnstile> \<langle>x\<leftarrow>p\<parallel>q\<rangle>(P x) \<longleftrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(P x) \<or>\<^sub>D (\<langle>x\<leftarrow>q\<rangle>(P x) \<and>\<^sub>D [# x\<leftarrow>p](Ret False))"
  determ:   "\<turnstile> \<langle>x\<leftarrow>p\<rangle>(P x) \<longleftrightarrow>\<^sub>D [# x\<leftarrow>p](P x) \<and>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Ret True)"

text {*
  Axiom @{thm [source] "determ"} is the typical relationship between @{term "\<langle>x\<leftarrow>p\<rangle>(P x)"} and @{term "[# x\<leftarrow>p](P x)"} 
  when no non-determinism is involved. Axioms @{thm [source] "altB_iff" "altD_iff"} describe the 
  fall back behaviour of the alternative operation.
*}


text {* @{term "dsef getInput"} implies @{term "dsef eot"} *}
lemma dsef_eot: "dsef eot"
  by (simp add: eot_def dsef_seq dsef_ret dsef_getInput)


text {* Another way to state the properties of alternation (for the diamond operator) *}
axioms
altD_left: "\<turnstile> \<langle>p\<rangle>P \<longrightarrow>\<^sub>D \<langle>p\<parallel>q\<rangle>P"
altD_right: "\<turnstile> \<langle>q\<rangle>P \<longrightarrow>\<^sub>D \<langle>p\<rangle>(\<lambda>x. Ret True) \<or>\<^sub>D \<langle>p\<parallel>q\<rangle>P"


text {* Proof that @{term "Eot"} actually is just an abbreviation *}
lemma Eot_GetInput: "Eot = (GetInput =\<^sub>D Ret [])"
proof -
  have null_eq_nil: " \<forall>x. null x = (x = [])"
  proof
    fix x show "null x = (x = [])"
    proof (cases x) 
      assume "x = []" thus "null x = (x = [])" by simp
    next
      fix a list assume "x = (a#list)" thus "null x = (x = [])" by simp
    qed
  qed
  show ?thesis
  by(simp add: Eot_def eot_def GetInput_def MonEq_def liftM2_def 
                  dsef_getInput Abs_Dsef_inverse Dsef_def Ret_def null_eq_nil)
qed

lemma GetInput_item_fail: "\<turnstile> GetInput =\<^sub>D Ret [] \<longrightarrow>\<^sub>D [# item](\<lambda>x. Ret False)"
  apply(rule subst[OF Eot_GetInput])
  by (rule eot_item)

text {* A formulation of part of @{thm [source] get_item} using patterns and
  asserting only what @{term "item"} will read *}

lemma get_item1: "\<turnstile> GetInput =\<^sub>D Ret (y#ys) \<longrightarrow>\<^sub>D [# x\<leftarrow>item](Ret (x = y))" (is "\<turnstile> ?A \<longrightarrow>\<^sub>D [# x\<leftarrow>item](?B x)")
proof -
  -- {* Common proof idiom: take a tautology, prove all its premisses, draw the conclusion by MP *}
  let ?C = "GetInput =\<^sub>D Ret ys"
  have "\<turnstile> ([# x\<leftarrow>item](?B x \<and>\<^sub>D ?C) \<longleftrightarrow>\<^sub>D [# x\<leftarrow>item](?B x) \<and>\<^sub>D [# x\<leftarrow>item]?C) \<longrightarrow>\<^sub>D
           (?A \<longrightarrow>\<^sub>D [# x\<leftarrow>item](?B x \<and>\<^sub>D ?C)) \<longrightarrow>\<^sub>D (?A \<longrightarrow>\<^sub>D [# x\<leftarrow>item](?B x))"
    by (simp add: pdl_taut)
  moreover 
  note box_conj_distrib
  moreover
  note get_item[of "y#ys", simplified]
  ultimately
  show ?thesis by(rule pdl_mp_2x)
qed

text {* This asserts the second half of @{thm [source] "get_item"}, i.e. what
  @{term "item"} consumes *}
lemma get_item2: "\<turnstile> GetInput =\<^sub>D Ret (y#ys) \<longrightarrow>\<^sub>D [# x\<leftarrow>item](GetInput =\<^sub>D Ret ys)" (is "\<turnstile> ?A \<longrightarrow>\<^sub>D [# x\<leftarrow>item](?C)")
proof -
  -- {* Common proof idiom: take a tautology, prove all its premisses, draw the conclusion by MP *}
  let "?B x" = "Ret (x = y)"
  have aff: "\<turnstile> ([# x\<leftarrow>item](?B x \<and>\<^sub>D ?C) \<longleftrightarrow>\<^sub>D [# x\<leftarrow>item](?B x) \<and>\<^sub>D [# x\<leftarrow>item]?C) \<longrightarrow>\<^sub>D
           (?A \<longrightarrow>\<^sub>D [# x\<leftarrow>item](?B x \<and>\<^sub>D ?C)) \<longrightarrow>\<^sub>D (?A \<longrightarrow>\<^sub>D [# x\<leftarrow>item](?C))"
    by (simp add: pdl_taut)
  moreover 
  note box_conj_distrib
  moreover
  note get_item[of "y#ys", simplified]
  ultimately
  show ?thesis by(rule pdl_mp_2x)
qed


text {* We can show that an alternative parser terminates iff one of its constituent
  parsers does *}
lemma par_term: "\<turnstile> \<langle>x \<leftarrow> p\<parallel>q\<rangle>(Ret True) \<longleftrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Ret True) \<or>\<^sub>D \<langle>x\<leftarrow>q\<rangle>(Ret True)"
proof (rule pdl_iffI)
  have "\<turnstile> ( \<langle>x\<leftarrow>p\<parallel>q\<rangle>(Ret True) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Ret True) \<or>\<^sub>D \<langle>x\<leftarrow>q\<rangle>(Ret True) \<and>\<^sub>D [# x\<leftarrow>p](Ret False) ) \<longrightarrow>\<^sub>D 
          \<langle>x\<leftarrow>p\<parallel>q\<rangle>(Ret True) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Ret True) \<or>\<^sub>D \<langle>x\<leftarrow>q\<rangle>(Ret True)"
    by (simp add: pdl_taut)
  moreover note pdl_iffD1[OF altD_iff]
  ultimately show  "\<turnstile> \<langle>p \<parallel> q\<rangle>(\<lambda>x. Ret True) \<longrightarrow>\<^sub>D \<langle>p\<rangle>(\<lambda>x. Ret True) \<or>\<^sub>D \<langle>q\<rangle>(\<lambda>x. Ret True)" 
    by (rule pdl_mp)
next
  have "\<turnstile> ( \<langle>x\<leftarrow>p\<rangle>(Ret True) \<or>\<^sub>D \<langle>x\<leftarrow>q\<rangle>(Ret True) \<and>\<^sub>D [# x\<leftarrow>p](Ret False) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow> p \<parallel> q\<rangle>(Ret True) ) \<longrightarrow>\<^sub>D 
          ( [# x\<leftarrow>p](Ret False) \<longleftrightarrow>\<^sub>D  \<not>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(\<not>\<^sub>D Ret False) ) \<longrightarrow>\<^sub>D 
           \<langle>x\<leftarrow>p\<rangle>(Ret True) \<or>\<^sub>D \<langle>x\<leftarrow>q\<rangle>(Ret True) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow> p \<parallel> q\<rangle>(Ret True)"
    by (simp add: pdl_taut)
  moreover 
  note pdl_iffD2[OF altD_iff]
  moreover 
  note box_dmd_rel
  ultimately
  show "\<turnstile> \<langle>x\<leftarrow>p\<rangle>(Ret True) \<or>\<^sub>D \<langle>x\<leftarrow>q\<rangle>(Ret True) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow> p \<parallel> q\<rangle>(Ret True)"
    by (rule pdl_mp_2x)
qed


text {* The following two lemmas are immediate from the axioms *}
lemma parI1: "\<turnstile>  [# x\<leftarrow>p](P x) \<and>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Ret True) \<longrightarrow>\<^sub>D [# x\<leftarrow>p\<parallel>q](P x)"
(*<*)
proof -
  have "\<turnstile> ([# x\<leftarrow>p](P x) \<and>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Ret True)) \<longrightarrow>\<^sub>D 
          ([# x\<leftarrow>p](P x) \<and>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Ret True) \<or>\<^sub>D [# x\<leftarrow>q](P x) \<and>\<^sub>D [# x\<leftarrow>p](Ret False))"
    by (simp add: pdl_taut)
  moreover 
  have "\<turnstile> ([# x\<leftarrow>p](P x) \<and>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Ret True) \<or>\<^sub>D [# x\<leftarrow>q](P x) \<and>\<^sub>D [# x\<leftarrow>p](Ret False)) \<longrightarrow>\<^sub>D
          [# x\<leftarrow>p\<parallel>q](P x)"
    by (rule pdl_iffD2[OF altB_iff])
  ultimately
  show ?thesis by (rule pdl_imp_trans)
qed
(*>*)


lemma parI2: "\<turnstile> [# x\<leftarrow>p](Ret False) \<and>\<^sub>D [# x\<leftarrow>q](P x) \<longrightarrow>\<^sub>D [# x\<leftarrow> p\<parallel>q](P x)"
(*<*)
proof -
   have "\<turnstile> [# x\<leftarrow>p](Ret False) \<and>\<^sub>D [# x\<leftarrow>q](P x) \<longrightarrow>\<^sub>D 
          ([# x\<leftarrow>p](P x) \<and>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Ret True) \<or>\<^sub>D [# x\<leftarrow>q](P x) \<and>\<^sub>D [# x\<leftarrow>p](Ret False))"
    by (simp only: pdl_taut Valid_Ret)
  moreover 
  have "\<turnstile> ([# x\<leftarrow>p](P x) \<and>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Ret True) \<or>\<^sub>D [# x\<leftarrow>q](P x) \<and>\<^sub>D [# x\<leftarrow>p](Ret False)) \<longrightarrow>\<^sub>D
          [# x\<leftarrow>p\<parallel>q](P x)"
    by (rule pdl_iffD2[OF altB_iff])
  ultimately
  show ?thesis by (rule pdl_imp_trans)
qed
(*>*)



subsection {* Specifying Simple Parsers in Terms of the Basic Ones *}


constdefs
  sat        :: "(nat \<Rightarrow> bool) \<Rightarrow> nat T"
  "sat p == do {x\<leftarrow>item; if p x then ret x else fail}"
  digitp       :: "nat T"
  "digitp == sat (\<lambda>x. x < 10)"

text {*
  The intended semantics of @{text "many"} is that maps a parser $p$ into one
  that applies $p$ as often as possible and collects the results (which may be 
  none).
*}
consts
many :: "'a T \<Rightarrow> 'a list T"

text {* We cannot define @{term "many"}, since it is not primitive recursive 
  and there is no termination measure. *}
axioms
many_unfold: "many p = ((do {x \<leftarrow> p; xs \<leftarrow> many p; ret (x#xs)}) \<parallel> ret [])"


constdefs
many1 :: "'a T \<Rightarrow> 'a list T"
"many1 p \<equiv> (do {x \<leftarrow> p; xs \<leftarrow> many p; ret (x#xs)})"
natp :: "nat T"
"natp \<equiv> do {ns \<leftarrow> many1 digitp; ret (foldl (\<lambda>r n. 10 * r + n) 0 ns)}"

text {*
  The parser for natural numbers @{term "natp"} works on an input stream
  that conists of natural numbers and reads numbers between 0 and 9 (inclusive) until 
  no such number can be read. Then it transforms its result list into a number
  by folding an appropriate function into the list. Of course, one might just as
  well consider an input stream of bounded numbers (e.g. ASCII characters in their
  numeric representation) and then read `0' to `9', but this would not 
  provide any interesting further insight.
*}


subsection {* Auxiliary Lemmas *}

(*<*)
(* NOTE:
 \<turnstile> [# do {x\<leftarrow>?p; y\<leftarrow>?q x; ret (x, y)}](\<lambda>(x, y). ?P x y) \<longleftrightarrow>\<^sub>D [# ?p](\<lambda>x. [# ?q x]?P x)
 *
 * Diese bisherige seq-Regel macht nicht viel Sinn, da sie zwar notationell schoen aussieht,
 * aber zusammenbricht, wenn man eine Mehrfachsequenz _einmal_ auseinander nehmen will.
 * Weil: in [x\<leftarrow>p][y\<leftarrow>q; z\<leftarrow>r]P wird dann ploetzlich ein neues ret(y,z) eingefuehrt.
 * Ausserdem matcht (y\<leftarrow>q; z\<leftarrow>r) nicht so einfach auf q... Daher verwenden wir ab sofort
 * die vereinfachte Regel pdl_seqB_simp.
 *)
lemma "\<turnstile> [# x\<leftarrow>p; z'\<leftarrow>do {y\<leftarrow>q; z\<leftarrow>ret (f x y); ret(y,z)}](P x z') \<longleftrightarrow>\<^sub>D [# x\<leftarrow>p][# z'\<leftarrow>do {y\<leftarrow>q; z\<leftarrow>ret (f x y); ret(y,z)}](P x z')"
by (rule pdl_seqB)

lemma "\<turnstile> [# do {x\<leftarrow>p; y\<leftarrow>q; ret (f x y)}]P \<longleftrightarrow>\<^sub>D [# p](\<lambda>x. [# do {y\<leftarrow>q; ret (f x y)}]P)"
  by (rule pdl_iff_sym[OF pdl_seqB_simp])
(*>*)



lemma aux_1: "\<turnstile> (A \<longrightarrow>\<^sub>D [# p](\<lambda>x. B x \<and>\<^sub>D C x)) \<longrightarrow>\<^sub>D ([# p](\<lambda>x. B x \<and>\<^sub>D C x) \<longleftrightarrow>\<^sub>D ([# p]B \<and>\<^sub>D [# p]C)) \<longrightarrow>\<^sub>D (A \<longrightarrow>\<^sub>D [# p]C)"
  by (simp add: pdl_taut)


lemma altB_iff_lifted2: "\<turnstile>(A \<longrightarrow>\<^sub>D [# p](\<lambda>x. Ret False) \<and>\<^sub>D[# q]P) \<longrightarrow>\<^sub>D (A \<longrightarrow>\<^sub>D [# p \<parallel> q]P)"
(*<*)
proof -
  have "\<turnstile> ([# p \<parallel> q]P \<longleftrightarrow>\<^sub>D [# p]P \<and>\<^sub>D \<langle>p\<rangle>(\<lambda>x. Ret True) \<or>\<^sub>D [# q]P \<and>\<^sub>D [# p](\<lambda>x. Ret False)) \<longrightarrow>\<^sub>D
            (A \<longrightarrow>\<^sub>D [# p](\<lambda>x. Ret False) \<and>\<^sub>D[# q]P) \<longrightarrow>\<^sub>D (A \<longrightarrow>\<^sub>D [# p \<parallel> q]P)" 
    by (simp add: pdl_taut)
  from this altB_iff show ?thesis by (rule pdl_mp)
qed
(*>*)

text {* The correctness of @{term "natp"} obviously relies on the correctness of @{term "digitp"}, 
  which is proved first. *}
theorem digitp_nat: "\<turnstile> GetInput =\<^sub>D Ret (y#ys) \<longrightarrow>\<^sub>D [# digitp](\<lambda>x. GetInput =\<^sub>D Ret ys \<and>\<^sub>D Ret (x = y))"
  (is "\<turnstile> ?A \<longrightarrow>\<^sub>D [# digitp](\<lambda>x. ?C \<and>\<^sub>D ?D x)")
proof -
  have "\<turnstile> (?A \<longrightarrow>\<^sub>D [# digitp](\<lambda>x. ?C)) \<longrightarrow>\<^sub>D (?A \<longrightarrow>\<^sub>D [# digitp](\<lambda>x. ?D x)) \<longrightarrow>\<^sub>D
          ([# digitp](\<lambda>x. ?C \<and>\<^sub>D ?D x) \<longleftrightarrow>\<^sub>D [# digitp](\<lambda>x. ?C) \<and>\<^sub>D [# digitp](\<lambda>x. ?D x)) \<longrightarrow>\<^sub>D
          (?A \<longrightarrow>\<^sub>D [# digitp](\<lambda>x. ?C \<and>\<^sub>D ?D x))"
    by (simp add: pdl_taut)
  moreover
  have "\<turnstile> GetInput =\<^sub>D Ret (y#ys) \<longrightarrow>\<^sub>D [# digitp](\<lambda>x. GetInput =\<^sub>D Ret ys)"
  proof -
    have "\<turnstile> GetInput =\<^sub>D Ret (y#ys) \<longrightarrow>\<^sub>D [# do {x\<leftarrow>item; if x < 10 then ret x else fail}](\<lambda>x. GetInput =\<^sub>D Ret ys)"
    proof (rule pdl_plugB_lifted1)
      from aux_1 get_item[of "y#ys", simplified] box_conj_distrib
      show "\<turnstile> GetInput =\<^sub>D Ret(y#ys) \<longrightarrow>\<^sub>D [# item](\<lambda>x. GetInput =\<^sub>D Ret ys)"
	by (rule pdl_mp_2x)
    next
      show "\<forall>x. \<turnstile> GetInput =\<^sub>D Ret ys \<longrightarrow>\<^sub>D [# do {if x<(10::nat) then ret x else fail}](\<lambda>y. GetInput =\<^sub>D Ret ys)"
      proof (rule allI)
	fix x
	show "\<turnstile> GetInput =\<^sub>D Ret ys \<longrightarrow>\<^sub>D [# if x < 10 then ret x else fail](\<lambda>y. GetInput =\<^sub>D Ret ys)"
	  (*<*)
	  apply(simp add: split_if)
	  apply(rule conjI)
	  apply(rule impI)
	  apply(rule pdl_iffD2[OF pdl_retB]) (* First subgoal done; now for fail *)
	  apply(rule impI)
	  apply(rule pdl_imp_wk)
	  apply(rule pdl_mpB)
	  apply(rule fail_bot)
	  apply(rule allI) 
	  apply(rule pdl_False_imp)
	  (*>*) -- {* \dots some rather obvious proof steps later *}
	  done
      qed
    qed
    thus ?thesis by (simp only: digitp_def sat_def)
  qed
  moreover
  have "\<turnstile> GetInput =\<^sub>D Ret (y#ys) \<longrightarrow>\<^sub>D [# digitp](\<lambda>x. Ret (x = y))"
  proof -
    have "\<turnstile> GetInput =\<^sub>D Ret (y#ys) \<longrightarrow>\<^sub>D [# do {x\<leftarrow>item; if x<10 then ret x else fail}](\<lambda>x. Ret(x=y))"
    proof (rule pdl_plugB_lifted1)
      show "\<turnstile> GetInput =\<^sub>D Ret (y#ys) \<longrightarrow>\<^sub>D [# item](\<lambda>x. Ret (x=y))"
	by (rule get_item1)
    next
      show " \<forall>x. \<turnstile> Ret (x = y) \<longrightarrow>\<^sub>D [# if x < 10 then ret x else fail](\<lambda>x. Ret (x = y))"
      proof (rule allI)
	fix x
	show "\<turnstile> Ret (x = y) \<longrightarrow>\<^sub>D [# if x < 10 then ret x else fail](\<lambda>x. Ret (x = y))"
	  (*<*)
	  apply(simp add: split_if)
	  apply(rule conjI)
	  apply(rule impI)
	  apply(rule pdl_iffD2[OF pdl_retB])
	  apply(rule impI)
	  apply(rule pdl_imp_wk)
	  apply(rule pdl_mpB)
	  apply(rule fail_bot)
	  apply(rule allI)
	  apply(rule pdl_False_imp)
	  (*>*) -- {* Again, the easy proof steps are omitted *}
	  done
      qed
    qed
    thus ?thesis by (simp add: digitp_def sat_def)
  qed
  moreover
  note box_conj_distrib
  ultimately
  show ?thesis by (rule pdl_mp_3x)
qed


theorem digitp_fail: "\<turnstile> GetInput =\<^sub>D Ret [] \<longrightarrow>\<^sub>D [# digitp](\<lambda>x. Ret False)"
  apply(simp add: digitp_def sat_def)
  apply(rule pdl_plugB_lifted1)
  apply(rule GetInput_item_fail)
  apply(rule allI)
  apply(rule pdl_False_imp)
done



(* auxiliary theorem, an "instance" of pdl_eqB_ext, with some extra premisses *)
lemma aux_2: "\<turnstile> (B \<and>\<^sub>D C \<longrightarrow>\<^sub>D [# p b]P) \<longrightarrow>\<^sub>D Ret (a = b) \<and>\<^sub>D B \<and>\<^sub>D C \<longrightarrow>\<^sub>D [# p a]P"
(*<*)
proof -
  have "\<turnstile> Ret (a = b) \<and>\<^sub>D B \<and>\<^sub>D C \<longrightarrow>\<^sub>D (B \<and>\<^sub>D C \<longrightarrow>\<^sub>D [# p b]P) \<longrightarrow>\<^sub>D [# p a]P" 
  proof -
    have "\<turnstile> (Ret (a = b) \<longrightarrow>\<^sub>D [# p b]P \<longrightarrow>\<^sub>D [# p a]P) \<longrightarrow>\<^sub>D 
            Ret (a = b) \<and>\<^sub>D B \<and>\<^sub>D C \<longrightarrow>\<^sub>D (B \<and>\<^sub>D C \<longrightarrow>\<^sub>D [# p b]P) \<longrightarrow>\<^sub>D [# p a]P"
      by (simp add: pdl_taut)
    moreover
    have "\<turnstile> Ret (a = b) \<longrightarrow>\<^sub>D [# p b]P \<longrightarrow>\<^sub>D [# p a]P"
      by (subst eq_commute, rule pdl_eqB_ext)
    ultimately
    show ?thesis by (rule pdl_mp)
  qed
  thus ?thesis by (simp add: pdl_taut)
qed
(*>*)

lemma aux_3: "\<turnstile> (A \<longrightarrow>\<^sub>D [# p b]P) \<longrightarrow>\<^sub>D A \<and>\<^sub>D Ret (a = b) \<longrightarrow>\<^sub>D [# p a]P"
(*<*)
proof -
  have "\<turnstile> A \<and>\<^sub>D Ret (a = b) \<longrightarrow>\<^sub>D (A \<longrightarrow>\<^sub>D [# p b]P) \<longrightarrow>\<^sub>D [# p a]P"
  proof -
    have "\<turnstile> (Ret (a = b) \<longrightarrow>\<^sub>D [# p b]P \<longrightarrow>\<^sub>D [# p a]P) \<longrightarrow>\<^sub>D
             A \<and>\<^sub>D Ret (a = b) \<longrightarrow>\<^sub>D (A \<longrightarrow>\<^sub>D [# p b]P) \<longrightarrow>\<^sub>D [# p a]P"
      by (simp add: pdl_taut)
    moreover
    have "\<turnstile> Ret (a = b) \<longrightarrow>\<^sub>D [# p b]P \<longrightarrow>\<^sub>D [# p a]P"
      by (subst eq_commute, rule pdl_eqB_ext)
    ultimately
    show ?thesis by (rule pdl_mp)
  qed
  thus ?thesis by (simp add: pdl_taut)
qed
(*>*)


lemma pdl_imp_strg1: "\<turnstile> A \<longrightarrow>\<^sub>D C \<Longrightarrow> \<turnstile> A \<and>\<^sub>D B \<longrightarrow>\<^sub>D C"
(*<*)
proof -
  assume "\<turnstile> A \<longrightarrow>\<^sub>D C"
  have "\<turnstile> (A \<longrightarrow>\<^sub>D C) \<longrightarrow>\<^sub>D A \<and>\<^sub>D B \<longrightarrow>\<^sub>D C"
    by (simp add: pdl_taut)
  thus ?thesis by (rule pdl_mp)
qed
(*>*)

lemma pdl_imp_strg2: "\<turnstile> B \<longrightarrow>\<^sub>D C \<Longrightarrow> \<turnstile> A \<and>\<^sub>D B \<longrightarrow>\<^sub>D C"
(*<*)
proof -
  assume "\<turnstile> B \<longrightarrow>\<^sub>D C"
  have "\<turnstile> (B \<longrightarrow>\<^sub>D C) \<longrightarrow>\<^sub>D A \<and>\<^sub>D B \<longrightarrow>\<^sub>D C"
    by (simp add: pdl_taut)
  thus ?thesis by (rule pdl_mp)
qed
(*>*)

subsection {* Correctness of the Monadic Parser *}
text {* 
  The following is a major theorem, more because of its complexity and since it 
  involves most of the axioms given for the monad, than because of its
  theoretical insight. Essentially, it states that @{term "natp"} behaves
  correctly for a given input.
*}
theorem "\<turnstile> [# uu\<leftarrow>setInput [1::nat]; n \<leftarrow> natp](Ret (n = 1) \<and>\<^sub>D Eot)"
proof -
  have f1: "\<turnstile> [# uu\<leftarrow>setInput [1::nat]](GetInput =\<^sub>D Ret [1])"
    by (rule set_get)
  have f2: "\<forall>uu. \<turnstile> GetInput =\<^sub>D Ret [1::nat] \<longrightarrow>\<^sub>D [# n\<leftarrow>natp](Ret (n = 1) \<and>\<^sub>D Eot)"
  proof
    fix uu
    -- {* The actual proof starts here: from a given input, show that @{term "natp"} is correct *}
    show "\<turnstile> GetInput =\<^sub>D Ret [1::nat] \<longrightarrow>\<^sub>D [# natp](\<lambda>n. Ret (n = 1) \<and>\<^sub>D Eot)"
    proof -
      -- {* Prove simplified version *}
      have "\<turnstile> GetInput =\<^sub>D Ret [1::nat] \<longrightarrow>\<^sub>D [# do {x\<leftarrow>digitp; xs\<leftarrow>many digitp; ret (foldl (\<lambda>r. op + (10 * r)) x xs)}](\<lambda>n. Ret (n = 1) \<and>\<^sub>D Eot)" (is "\<turnstile> ?a \<longrightarrow>\<^sub>D ?b")
      proof -
	have "\<turnstile> GetInput =\<^sub>D Ret [1] \<longrightarrow>\<^sub>D [# digitp](\<lambda>x. [# do {xs\<leftarrow>many digitp; ret (foldl (\<lambda>r. op + (10 * r)) x xs)}](\<lambda>n. Ret (n = 1) \<and>\<^sub>D Eot))"
	proof -
	  -- {* Split into two parts and connect per mpB *}
	  have g1: "\<turnstile> GetInput =\<^sub>D Ret [1] \<longrightarrow>\<^sub>D [# digitp](\<lambda>n. Ret (n=1) \<and>\<^sub>D GetInput =\<^sub>D Ret [])"
	  proof (rule pdl_iffD2[OF box_conj_distrib_lifted1, THEN pdl_mp])
	    have "\<turnstile> (GetInput =\<^sub>D Ret [1] \<longrightarrow>\<^sub>D [# digitp](\<lambda>x. Ret (x = 1)))" (is "\<turnstile> ?A")
	      by (rule imp_box_conj2[OF digitp_nat])
	    moreover
	    have "\<turnstile> (GetInput =\<^sub>D Ret [1] \<longrightarrow>\<^sub>D [# digitp](\<lambda>x. GetInput =\<^sub>D Ret []))" (is "\<turnstile> ?B")
	      by (rule imp_box_conj1[OF digitp_nat])
	    ultimately show "\<turnstile> ?A \<and>\<^sub>D ?B" by (rule pdl_conjI)
	  qed
	  have g2: "\<forall>n. \<turnstile> (Ret (n=1) \<and>\<^sub>D GetInput =\<^sub>D Ret []) \<longrightarrow>\<^sub>D 
	    ([# do {xs\<leftarrow>many digitp; ret (foldl (\<lambda>r. op + (10 * r)) n xs)}](\<lambda>n. Ret (n=1) \<and>\<^sub>D Eot))"
	    -- {* Proceed with one command @{term "digitp"} removed *}
	  proof
	    fix n 
	    show "\<turnstile> Ret (n = 1) \<and>\<^sub>D GetInput =\<^sub>D Ret [] \<longrightarrow>\<^sub>D
              [# do {xs\<leftarrow>many digitp; ret (foldl (\<lambda>r. op + (10 * r)) n xs)}](\<lambda>n. Ret (n = 1) \<and>\<^sub>D Eot)"
	    proof -
	      -- {* Again, prove a simplified version *}
	      have "\<turnstile> Ret (n = Suc 0) \<and>\<^sub>D GetInput =\<^sub>D Ret [] \<longrightarrow>\<^sub>D
		[# do {xs\<leftarrow>(do {x\<leftarrow>digitp; xs\<leftarrow>many digitp; ret (x # xs)}) \<parallel> ret []; 
		       ret (foldl (\<lambda>r. op + (10 * r)) n xs)}](\<lambda>n. Ret (n = Suc 0) \<and>\<^sub>D Eot)"
	      proof (rule pdl_plugB_lifted1[where B = "\<lambda>xs. Ret (n = 1) \<and>\<^sub>D GetInput =\<^sub>D Ret [] \<and>\<^sub>D Ret (xs = [])"])
		-- {* Part one shows that the alternative @{term "p\<parallel>q"} yields a sufficient result *}
		show "\<turnstile> Ret (n = Suc 0) \<and>\<^sub>D GetInput =\<^sub>D Ret [] \<longrightarrow>\<^sub>D 
		        [# (do {x\<leftarrow>digitp; xs\<leftarrow>many digitp; ret (x # xs)}) \<parallel> ret []](\<lambda>xs. 
                           Ret (n = 1) \<and>\<^sub>D GetInput =\<^sub>D Ret [] \<and>\<^sub>D Ret (xs = []))"
		  (*<*)
		  apply(rule altB_iff_lifted2[THEN pdl_mp])
		  apply(rule pdl_conjI_lifted)
		  apply(rule pdl_plugB_lifted1)
		  apply(rule pdl_imp_strg2)
		  apply(rule digitp_fail)
		  apply(rule allI)
		  apply(rule pdl_False_imp)
		  apply(rule pdl_iffD2[OF box_conj_distrib_lifted1, THEN pdl_mp])
		  apply(rule pdl_conjI)
		  apply(rule pdl_imp_strg1)
		  apply(simp)
		  apply(rule pdl_iffD2[OF pdl_retB])
		  apply(rule pdl_imp_strg2)
		  apply(rule pdl_iffD2[OF box_conj_distrib_lifted1, THEN pdl_mp])
		  apply(rule pdl_conjI)
		  apply(rule pdl_iffD2[OF pdl_retB])
		  apply(rule pdl_imp_wk)
		  apply(rule pdl_iffD2[OF pdl_retB, THEN pdl_mp])
		  (*>*)
		by simp -- {* And some proof steps omitted in the text *}
	      next
		-- {* Part two shows that the result obtained from part one is just what we wanted *}
		show "\<forall>xs. \<turnstile> Ret (n = 1) \<and>\<^sub>D GetInput =\<^sub>D Ret [] \<and>\<^sub>D Ret (xs = []) \<longrightarrow>\<^sub>D 
		      [# ret (foldl (\<lambda>r. op + (10 * r)) n xs)](\<lambda>n. Ret (n = Suc 0) \<and>\<^sub>D Eot)"
		proof
		  fix xs show "\<turnstile> Ret (n = 1) \<and>\<^sub>D GetInput =\<^sub>D Ret [] \<and>\<^sub>D Ret (xs = []) \<longrightarrow>\<^sub>D 
                                 [# ret (foldl (\<lambda>r. op + (10 * r)) n xs)](\<lambda>n. Ret (n = Suc 0) \<and>\<^sub>D Eot)"
		  proof (rule aux_2[THEN pdl_mp])
		    show "\<turnstile> GetInput =\<^sub>D Ret [] \<and>\<^sub>D Ret (xs = []) \<longrightarrow>\<^sub>D 
                            [# ret (foldl (\<lambda>r. op + (10 * r)) 1 xs)](\<lambda>n. Ret (n = Suc 0) \<and>\<^sub>D Eot)"
		      proof (rule aux_3[THEN pdl_mp])
			have "\<turnstile> GetInput =\<^sub>D Ret [] \<longrightarrow>\<^sub>D [# ret (1::nat)](\<lambda>n. Ret (n = 1) \<and>\<^sub>D Eot)"
			  (*<*)
			  apply(rule pdl_iffD2[OF box_conj_distrib_lifted1, THEN pdl_mp])
			  apply(rule pdl_conjI)
			  apply(rule pdl_imp_wk)
			  apply(rule pdl_iffD2[OF pdl_retB, THEN pdl_mp])
			  apply(subst Valid_Ret, simp)
			  apply(subst Eot_GetInput)
			  apply(rule pdl_iffD2[OF pdl_retB])
			  (*>*) -- {* Obvious *}
			  done
			thus "\<turnstile> GetInput =\<^sub>D Ret [] \<longrightarrow>\<^sub>D [# ret (foldl (\<lambda>r\<Colon>nat. op + ((10\<Colon>nat) * r)) (1\<Colon>nat) [])](\<lambda>n\<Colon>nat. Ret (n = Suc 0) \<and>\<^sub>D Eot)"
			  by (simp)
		      qed
		    qed
		  qed
		qed
	      thus ?thesis by (subst many_unfold, simp add: mon_ctr del: bind_assoc)
	    qed
	  qed
	  -- {* this essentially establishes the goal *}
	  from g1 g2 show ?thesis  by (rule pdl_mpB_lifted1)
	qed
	-- {* Sequencing *}
	thus ?thesis by (rule pdl_iffD1[OF pdl_seqB_lifted1, THEN pdl_mp])
      qed
      -- {* Retranslation to @{term "natp"} *}
      thus ?thesis by (simp add: natp_def many1_def mon_ctr del: bind_assoc)
    qed
  qed
  show ?thesis
  proof (rule pdl_seqB_join)
    from f1 f2 show "\<turnstile> [# setInput [1]](\<lambda>uu. [# natp](\<lambda>y. Ret (y = 1) \<and>\<^sub>D Eot))"
      by (rule pdl_mpB)
  qed
qed





(* Testing ground for if and while rules *)
(*<*)



constdefs
  MonIf     :: "bool D \<Rightarrow> 'a T \<Rightarrow> 'a T \<Rightarrow> 'a T" ("IF _ THEN _ ELSE _ FI" [0, 0, 0] 100)
  "IF b THEN p ELSE q FI == do {x\<leftarrow>\<Down> b; if x then p else q}"



text {* 
  The premisses of the lemmas below are actually too strong to be useful
  in all but the simplest cases. Because the notion of  \emph{global}
  validity is involved, one cannot expect @{term "\<turnstile> b"} or
  @{term "\<turnstile> (\<not>\<^sub>D b)"} to hold; only the weaker tautologous
  @{term "\<turnstile> b \<or>\<^sub>D (\<not>\<^sub>D b)"} will be applicable in most proofs.
*}

lemma "\<turnstile> b \<Longrightarrow> (IF b THEN p ELSE q FI) = p"
proof -
  assume "\<turnstile> b"
  hence "\<Down> b = ret True" by (rule iffD1[OF Valid_simp])
  thus ?thesis by (simp add: MonIf_def)
qed

lemma "\<turnstile> \<not>\<^sub>D b \<Longrightarrow> (IF b THEN p ELSE q FI) = q"
proof -
  assume "\<turnstile> \<not>\<^sub>D b"
  hence "\<Down> b = ret False" by (rule iffD1[OF Valid_not_eq_ret_False])
  thus ?thesis by (simp add: MonIf_def)
qed


text {* Next try, now \dots still improperly stated. *}
lemma MonIf_eq_left: "\<turnstile> b \<longrightarrow>\<^sub>D Ret (p = (IF b THEN p ELSE q FI))"
  oops

lemma MonIf_eq_right: "\<turnstile> \<not>\<^sub>D b \<longrightarrow>\<^sub>D Ret (q = (IF b THEN p ELSE q FI))"
  oops


(*
lemma MonIfI: "\<lbrakk>\<turnstile> b \<longrightarrow>\<^sub>D [# x\<leftarrow>p](P x);
                \<turnstile> (\<not>\<^sub>D b) \<longrightarrow>\<^sub>D [# x\<leftarrow>q](P x) \<rbrakk> \<Longrightarrow>
               \<turnstile> [# x\<leftarrow>(IF b THEN p ELSE q FI)](P x)"
proof -
  assume a1: "\<turnstile> b \<longrightarrow>\<^sub>D [# x \<leftarrow>p](P x)"
  assume a2: "\<turnstile> \<not>\<^sub>D b \<longrightarrow>\<^sub>D [# x\<leftarrow>q](P x)"
  let ?s = "IF b THEN p ELSE q FI"
  from MonIf_eq_left pdl_eqB 
  have "\<turnstile> b \<longrightarrow>\<^sub>D [# p]P \<longrightarrow>\<^sub>D [# ?s]P" by (rule pdl_imp_trans)
  (* \<dots> *)
  have p1: "\<turnstile> b \<longrightarrow>\<^sub>D [# ?s]P"
    sorry
  (* \<dots> *)
  have p2: "\<turnstile> \<not>\<^sub>D b \<longrightarrow>\<^sub>D [# ?s]P"
    sorry
  from pdl_excluded_middle p1 p2
  show "\<turnstile> [# ?s]P" by (rule pdl_disjE)
qed
*)

(*
lemma MonIfI_total: "\<lbrakk>\<turnstile> b \<longrightarrow>\<^sub>D ([# x\<leftarrow>p](P x) \<and>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Ret True));
                \<turnstile> (\<not>\<^sub>D b) \<longrightarrow>\<^sub>D ([# x\<leftarrow>q](P x) \<and>\<^sub>D \<langle>x\<leftarrow>q\<rangle>(Ret True))\<rbrakk> \<Longrightarrow>
               \<turnstile> [# x\<leftarrow>(IF b THEN p ELSE q FI)](P x) \<and>\<^sub>D 
                  \<langle>x\<leftarrow>(IF b THEN p ELSE q FI)\<rangle>(Ret True)"
proof -
  assume "\<turnstile> b \<longrightarrow>\<^sub>D [# p]P \<and>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Ret True)"
  assume "\<turnstile> \<not>\<^sub>D b \<longrightarrow>\<^sub>D [# p]P 
  hence "" (* OPEN *)
*)    




consts
  while :: "bool D \<Rightarrow> unit T \<Rightarrow> unit T"


axioms 
  pdl_while: "\<lbrakk>wf R; \<turnstile> (P \<and>\<^sub>D b \<and>\<^sub>D (t =\<^sub>D Ret z)) \<longrightarrow>\<^sub>D 
                       [# p](\<lambda>x. P \<and>\<^sub>D \<Up> (do {a\<leftarrow>\<Down> t; ret ((a,z) \<in> R)})) \<rbrakk> \<Longrightarrow>
               \<turnstile> [# while b p](\<lambda>x. P \<and>\<^sub>D \<not>\<^sub>D b)"


lemma pdl_while_nat: "\<lbrakk> \<turnstile> (P \<and>\<^sub>D b \<and>\<^sub>D (t =\<^sub>D Ret (z::nat))) \<longrightarrow>\<^sub>D 
                        [# p](\<lambda>x. P \<and>\<^sub>D \<Up> (do {a\<leftarrow>\<Down> t; ret (a < z)})) \<rbrakk> \<Longrightarrow>
                      \<turnstile> [# while b p](\<lambda>x. P \<and>\<^sub>D \<not>\<^sub>D b)"
by (rule pdl_while, rule wf_less, simp)
  
  
(*>*)
end
