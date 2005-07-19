header {* A Deterministic Parser Monad with Fall Back Alternatives *}

theory Parsec = PDL + MonEq:
text_raw {* \label{sec:parsec-thy} *}

text {*
  In a typical implementation of this parser monad, @{term "T"} would have the 
  form @{text "T A = (S \<Rightarrow> (E + A) \<times> S)"}, i.e. it would be a state monad (over states
  $S$) with exceptions of type $E$. The fall back alternative @{term "q"} in
  @{text "p\<parallel>q"} would then only be used if @{term "p"} failed to terminate.
  \label{isa:parsec-spec}
*}


consts
  item       :: "nat T"      -- {* Parses exactly one character (natural number) *}
  fail       :: "'a T"       -- {* Always fails *}
  alt        :: "'a T \<Rightarrow> 'a T \<Rightarrow> 'a T" (infixl "\<parallel>" 140) -- {* Prefer first parser, but fall back on second if necessary *}
  getInput   :: "nat list T" -- {* read the current state *}
  setInput   :: "nat list \<Rightarrow> unit T" 


constdefs 
  eot :: "bool T"
  "eot \<equiv> (do {i \<leftarrow> getInput; ret (null i)})"
  Eot :: "bool D"
  "Eot \<equiv> \<Up> eot"
  GetInput :: "nat list D"
  "GetInput \<equiv> \<Up> getInput"
text {* 
@{term "GetInput"} and @{term "Eot"} are the abstractions in @{typ "'a D"} of the
resp. lower case terms in @{typ "'a T"}.
*}


axioms
  dsef_getInput: "dsef getInput"
  fail_bot: "\<turnstile> [# fail](\<lambda>x. Ret False)"
  eot_item: "\<turnstile> Eot \<longrightarrow>\<^sub>D [# x\<leftarrow>item](Ret False)"
  set_get:  "\<turnstile> \<langle>setInput x\<rangle>(\<lambda>u. GetInput =\<^sub>D Ret x)"
  get_item: "\<turnstile> GetInput =\<^sub>D Ret (y#ys) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>item\<rangle>(Ret (x = y) \<and>\<^sub>D GetInput =\<^sub>D Ret ys)"
  altB_iff: "\<turnstile> [# x\<leftarrow>p\<parallel>q](P x) \<longleftrightarrow>\<^sub>D ( [# x\<leftarrow>p](P x) \<and>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Ret True) ) \<or>\<^sub>D 
                                     ( [# x\<leftarrow>q](P x) \<and>\<^sub>D [# x\<leftarrow>p](Ret False) )"
  altD_iff: "\<turnstile> \<langle>x\<leftarrow>p\<parallel>q\<rangle>(P x) \<longleftrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(P x) \<or>\<^sub>D (\<langle>x\<leftarrow>q\<rangle>(P x) \<and>\<^sub>D [# x\<leftarrow>p](Ret False))"
  determ:   "\<turnstile> \<langle>x\<leftarrow>p\<rangle>(P x) \<longleftrightarrow>\<^sub>D [# x\<leftarrow>p](P x) \<and>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(Ret True)"

text {*
  Axiom @{thm [source] "determ"} is the typical relationship between @{term "\<langle>x\<leftarrow>p\<rangle>(P x)"} and @{term "[# x\<leftarrow>p](P x)"} 
  when no non-determinism is involved. Axioms @{thm [source] "altB_iff" "altD_iff"} describe the 
  fall back behaviour of the alternative operation.
*}


text {* @{term "dsef getInput"} implies @{term "dsef eot"}. *}
lemma dsef_eot: "dsef eot"
  by (simp add: eot_def dsef_seq dsef_ret dsef_getInput)


text {* Another way to state the properties of alternation (for the diamond operator). *}
axioms
altD_left: "\<turnstile> \<langle>p\<rangle>P \<longrightarrow>\<^sub>D \<langle>p\<parallel>q\<rangle>P"
altD_right: "\<turnstile> \<langle>q\<rangle>P \<longrightarrow>\<^sub>D \<langle>p\<rangle>(\<lambda>x. Ret True) \<or>\<^sub>D \<langle>p\<parallel>q\<rangle>P"


text {* Proof that @{term "Eot"} actually is just an abbreviation. *}
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



text {* We can show that an alternative parser terminates iff one of its constituent
  parsers does. *}
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


text {* The following two lemmas are immediate from the axioms. *}
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

text_raw {* \label{isa:defined-parsers} *}
constdefs
  sat        :: "(nat \<Rightarrow> bool) \<Rightarrow> nat T"
  "sat p \<equiv> do {x\<leftarrow>item; if p x then ret x else fail}"
  digitp       :: "nat T"
  "digitp \<equiv> sat (\<lambda>x. x < 10)"

text {*
  The intended semantics of @{text "many"} is that it maps a parser $p$ into one
  that applies $p$ as often as possible and collects the results (which may be 
  none). @{text "many1"} requires at least one successful run of $p$.
*}
consts
many  :: "'a T \<Rightarrow> 'a list T"
many1 :: "'a T \<Rightarrow> 'a list T"


text {* We cannot define @{term "many"}, since it is not primitive recursive 
  and there is no termination measure. 
  \label{isa:many-unfold}
*}
axioms
many_unfold: "many p = ((do {x \<leftarrow> p; xs \<leftarrow> many p; ret (x#xs)}) \<parallel> ret [])"

defs
many1_def: "many1 p \<equiv> (do {x \<leftarrow> p; xs \<leftarrow> many p; ret (x#xs)})"


text {* This is the most convenient and expressive rule we can hope for at the
   moment. *}
lemma many_step: "\<lbrakk> \<turnstile> \<langle>(do {x \<leftarrow> p; xs \<leftarrow> many p; ret (x#xs)})\<rangle>P \<or>\<^sub>D 
                      \<langle>ret []\<rangle>P \<and>\<^sub>D [# x\<leftarrow>p](Ret False) \<rbrakk> \<Longrightarrow> \<turnstile> \<langle>many p\<rangle>P"
(*<*)
proof (subst many_unfold)
  let ?seq = "do {x\<leftarrow>p; xs\<leftarrow>many p; ret (x # xs)}"
  assume a1: "\<turnstile> \<langle>?seq\<rangle>P \<or>\<^sub>D \<langle>ret []\<rangle>P \<and>\<^sub>D [# p](\<lambda>x. Ret False)"
  show "\<turnstile> \<langle>?seq \<parallel> ret []\<rangle>P"
  proof (rule pdl_iffD2[OF altD_iff, THEN pdl_mp])
    from a1 
    show "\<turnstile> \<langle>?seq\<rangle>P \<or>\<^sub>D \<langle>ret []\<rangle>P \<and>\<^sub>D [# x\<leftarrow>?seq](Ret False)"
    proof (rule pdl_disjE)
      show "\<turnstile> \<langle>?seq\<rangle>P \<longrightarrow>\<^sub>D \<langle>?seq\<rangle>P \<or>\<^sub>D \<langle>ret []\<rangle>P \<and>\<^sub>D [# x\<leftarrow>?seq](Ret False)"
	by (simp add: pdl_taut)
    next
      show "\<turnstile>  \<langle>ret []\<rangle>P \<and>\<^sub>D [# p](\<lambda>x. Ret False) \<longrightarrow>\<^sub>D
               \<langle>?seq\<rangle>P \<or>\<^sub>D \<langle>ret []\<rangle>P \<and>\<^sub>D [# x\<leftarrow>?seq](Ret False)"
	(is "\<turnstile> ?r1 \<and>\<^sub>D ?s1 \<longrightarrow>\<^sub>D ?uu \<or>\<^sub>D ?r1 \<and>\<^sub>D ?s2")
      proof -
	have "\<turnstile> (?s1 \<longrightarrow>\<^sub>D ?s2) \<longrightarrow>\<^sub>D
	         ?r1 \<and>\<^sub>D ?s1 \<longrightarrow>\<^sub>D ?uu \<or>\<^sub>D ?r1 \<and>\<^sub>D ?s2"
	  by (simp add: pdl_taut)
	moreover
	have "\<turnstile> ?s1 \<longrightarrow>\<^sub>D ?s2"
	proof (rule pdl_plugB_lifted1)
	  show "\<turnstile> [# p](\<lambda>x. Ret False) \<longrightarrow>\<^sub>D [# p](\<lambda>x. Ret False)" 
	    by (simp add: pdl_taut)
	next
	  show "\<forall>x. \<turnstile> Ret False \<longrightarrow>\<^sub>D [# do {xs\<leftarrow>many p; ret (x # xs)}](\<lambda>x. Ret False)"
	    by (simp add: pdl_taut)
	qed
	ultimately
	show ?thesis by (rule pdl_mp)
      qed
    qed
  qed
qed
(*>*)

constdefs
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

text {* A convenient rendition of axiom @{thm [source] altD_iff} as a rule. *}
lemma altD_iff_lifted1: "\<lbrakk>\<turnstile> A \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>q\<rangle>(P x); \<turnstile> A \<longrightarrow>\<^sub>D [# x\<leftarrow>p](Ret False)\<rbrakk> \<Longrightarrow> \<turnstile> A \<longrightarrow>\<^sub>D \<langle>x\<leftarrow> p\<parallel>q\<rangle>(P x)"
proof - 
  have "\<turnstile> (\<langle>x\<leftarrow>p\<parallel>q\<rangle>(P x) \<longleftrightarrow>\<^sub>D \<langle>x\<leftarrow>p\<rangle>(P x) \<or>\<^sub>D \<langle>x\<leftarrow>q\<rangle>(P x) \<and>\<^sub>D [# x\<leftarrow>p](Ret False)) \<longrightarrow>\<^sub>D
          (A \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>q\<rangle>(P x)) \<longrightarrow>\<^sub>D (A \<longrightarrow>\<^sub>D [# x\<leftarrow>p](Ret False)) \<longrightarrow>\<^sub>D
           A \<longrightarrow>\<^sub>D \<langle>x\<leftarrow> p\<parallel>q\<rangle>(P x)"
    by (simp add: pdl_taut)
  moreover 
  note altD_iff
  moreover
  assume "\<turnstile> A \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>q\<rangle>(P x)"
  moreover
  assume "\<turnstile> A \<longrightarrow>\<^sub>D [# x\<leftarrow>p](Ret False)"
  ultimately
  show ?thesis by (rule pdl_mp_3x)
qed


text {* The correctness of @{term "natp"} obviously relies on the correctness of @{term "digitp"}, 
  which is proved first. *}
theorem digitp_nat: "\<turnstile> GetInput =\<^sub>D Ret (1#ys) \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>digitp\<rangle>(Ret (x = 1) \<and>\<^sub>D GetInput =\<^sub>D Ret ys)"
  (is "\<turnstile> ?A \<longrightarrow>\<^sub>D \<langle>digitp\<rangle>(\<lambda>x. ?C x \<and>\<^sub>D ?D)")
  apply(unfold digitp_def sat_def)
  apply(rule pdl_plugD_lifted1)
  apply(rule get_item)
  apply(rule allI)
  apply(simp add: split_if)
  apply(safe) 
  apply(rule pdl_iffD2[OF pdl_retD])
  by (simp add: pdl_taut) -- {* For the else-branch we obtain a contradiction, since the input was 1 *}


text {* On empty input, @{term "digitp"} will fail. *}
theorem digitp_fail: "\<turnstile> GetInput =\<^sub>D Ret [] \<longrightarrow>\<^sub>D [# digitp](\<lambda>x. Ret False)"
  apply(simp add: digitp_def sat_def)
  apply(rule pdl_plugB_lifted1)
  apply(rule GetInput_item_fail)
  apply(rule allI)
  apply(rule pdl_False_imp)
done


lemma ret_nil_aux: " \<turnstile> A \<and>\<^sub>D B \<longrightarrow>\<^sub>D
  \<langle>ret []\<rangle>(\<lambda>xs. A \<and>\<^sub>D B \<and>\<^sub>D Ret (xs = []))"
(*<*)
  apply(rule pdl_imp_trans[of _ "A \<and>\<^sub>D B \<and>\<^sub>D Ret ([] = [])"])
  apply(simp add: pdl_taut)
  by (rule pdl_iffD2[OF pdl_retD])
(*>*)


lemma ret_one_aux: "\<turnstile> A \<longrightarrow>\<^sub>D 
                      \<langle>ret (Suc 0)\<rangle>(\<lambda>n. Ret (n = Suc 0) \<and>\<^sub>D A)"
(*<*)
  apply(rule pdl_imp_trans[of _ "Ret (Suc 0 = Suc 0) \<and>\<^sub>D A"])
  apply(simp add: pdl_taut)
  by (rule pdl_iffD2[OF pdl_retD])
(*>*)


(* auxiliary theorem, an "instance" of pdl_eqB_ext, with some extra premisses. *)
lemma pdl_eqD_aux1: "\<turnstile> (B \<and>\<^sub>D C \<longrightarrow>\<^sub>D \<langle>p b\<rangle>P) \<longrightarrow>\<^sub>D Ret (a = b) \<and>\<^sub>D B \<and>\<^sub>D C \<longrightarrow>\<^sub>D \<langle>p a\<rangle>P"
(*<*)
proof -
  have "\<turnstile> Ret (a = b) \<and>\<^sub>D B \<and>\<^sub>D C \<longrightarrow>\<^sub>D (B \<and>\<^sub>D C \<longrightarrow>\<^sub>D \<langle>p b\<rangle>P) \<longrightarrow>\<^sub>D \<langle>p a\<rangle>P" 
  proof -
    have "\<turnstile> (Ret (a = b) \<longrightarrow>\<^sub>D \<langle>p b\<rangle>P \<longrightarrow>\<^sub>D \<langle>p a\<rangle>P) \<longrightarrow>\<^sub>D 
            Ret (a = b) \<and>\<^sub>D B \<and>\<^sub>D C \<longrightarrow>\<^sub>D (B \<and>\<^sub>D C \<longrightarrow>\<^sub>D \<langle>p b\<rangle>P) \<longrightarrow>\<^sub>D \<langle>p a\<rangle>P"
      by (simp add: pdl_taut)
    moreover
    have "\<turnstile> Ret (a = b) \<longrightarrow>\<^sub>D \<langle>p b\<rangle>P \<longrightarrow>\<^sub>D \<langle>p a\<rangle>P"
      by (subst eq_commute, rule pdl_eqD_ext)
    ultimately
    show ?thesis by (rule pdl_mp)
  qed
  thus ?thesis by (simp add: pdl_taut)
qed
(*>*)

lemma pdl_eqD_aux2: "\<turnstile> (A \<longrightarrow>\<^sub>D \<langle> p b\<rangle>P) \<longrightarrow>\<^sub>D A \<and>\<^sub>D Ret (a = b) \<longrightarrow>\<^sub>D \<langle> p a\<rangle>P"
(*<*)
proof -
  have "\<turnstile> A \<and>\<^sub>D Ret (a = b) \<longrightarrow>\<^sub>D (A \<longrightarrow>\<^sub>D \<langle> p b\<rangle>P) \<longrightarrow>\<^sub>D \<langle> p a\<rangle>P"
  proof -
    have "\<turnstile> (Ret (a = b) \<longrightarrow>\<^sub>D \<langle> p b\<rangle>P \<longrightarrow>\<^sub>D \<langle> p a\<rangle>P) \<longrightarrow>\<^sub>D
             A \<and>\<^sub>D Ret (a = b) \<longrightarrow>\<^sub>D (A \<longrightarrow>\<^sub>D \<langle> p b\<rangle>P) \<longrightarrow>\<^sub>D \<langle> p a\<rangle>P"
      by (simp add: pdl_taut)
    moreover
    have "\<turnstile> Ret (a = b) \<longrightarrow>\<^sub>D \<langle> p b\<rangle>P \<longrightarrow>\<^sub>D \<langle> p a\<rangle>P"
      by (subst eq_commute, rule pdl_eqD_ext)
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
  totally correct for a given input.
  \label{isa:natp-proof}
*}

theorem natp_corr: "\<turnstile> \<langle>do {uu\<leftarrow>setInput [1]; natp}\<rangle>(\<lambda>n. Ret (n = 1) \<and>\<^sub>D Eot)"
proof -
  have "\<turnstile> \<langle>uu\<leftarrow>setInput [1]\<rangle>(GetInput =\<^sub>D Ret [1])"
    by (rule set_get)
  moreover
  have "\<forall>uu::unit. \<turnstile> GetInput =\<^sub>D Ret [1] \<longrightarrow>\<^sub>D \<langle>n\<leftarrow>natp\<rangle>(Ret (n = 1) \<and>\<^sub>D Eot)"
  proof
    fix uu
    -- {* The actual proof starts here: from a given input, show that @{term "natp"} is correct *}
    show "\<turnstile> GetInput =\<^sub>D Ret [1] \<longrightarrow>\<^sub>D \<langle>natp\<rangle>(\<lambda>n. Ret (n = 1) \<and>\<^sub>D Eot)"
    proof -
      -- {* Prove the formula with defn. of @{term "natp"} unfolded *}
      have "\<turnstile> GetInput =\<^sub>D Ret [1] \<longrightarrow>\<^sub>D \<langle>do {x\<leftarrow>digitp; xs\<leftarrow>many digitp; ret (foldl (\<lambda>r. op + (10 * r)) x xs)}\<rangle>(\<lambda>n. Ret (n = 1) \<and>\<^sub>D Eot)" (is "\<turnstile> ?a \<longrightarrow>\<^sub>D ?b")
      proof - -- {* Work out each atomic program separately *}
	have "\<turnstile> GetInput =\<^sub>D Ret [1] \<longrightarrow>\<^sub>D \<langle>x\<leftarrow>digitp\<rangle>(Ret (x=1) \<and>\<^sub>D GetInput =\<^sub>D Ret [])"
	  by (rule digitp_nat)
	moreover
	have "\<forall>x. \<turnstile> (Ret (x=(1::nat)) \<and>\<^sub>D GetInput =\<^sub>D Ret []) \<longrightarrow>\<^sub>D
	    (\<langle>do {xs\<leftarrow>many digitp; ret (foldl (\<lambda>r. op + (10 * r)) x xs)}\<rangle>(\<lambda>n. Ret(n=1) \<and>\<^sub>D Eot))"
	proof -- {* Here, @{term "digitp"} will fail, ie. @{term "many"} will return @{term "[]"} *}
	  fix x
	  show "\<turnstile> Ret (x = 1) \<and>\<^sub>D GetInput =\<^sub>D Ret [] \<longrightarrow>\<^sub>D
             \<langle>do {xs\<leftarrow>many digitp; ret (foldl (\<lambda>r. op + (10 * r)) x xs)}\<rangle>(\<lambda>n. Ret (n = 1) \<and>\<^sub>D Eot)"
	  proof (rule pdl_plugD_lifted1[where B = "\<lambda>xs. Ret (x = 1) \<and>\<^sub>D GetInput =\<^sub>D Ret [] \<and>\<^sub>D
	                                                Ret (xs = [])"])
	    show "\<turnstile> Ret (x = 1) \<and>\<^sub>D GetInput =\<^sub>D Ret [] \<longrightarrow>\<^sub>D
	      \<langle>many digitp\<rangle>(\<lambda>xs. Ret (x = 1) \<and>\<^sub>D GetInput =\<^sub>D Ret [] \<and>\<^sub>D Ret (xs = []))"
	      apply(subst many_unfold)
	      apply(rule altD_iff_lifted1)
	      apply(rule ret_nil_aux)
	      apply(rule pdl_plugB_lifted1)
	      apply(rule pdl_imp_strg2)
	      apply(rule digitp_fail)
	      apply(rule allI) 
	      by (simp add: pdl_taut)
	  next
	    show "\<forall>xs. \<turnstile> Ret (x = 1) \<and>\<^sub>D GetInput =\<^sub>D Ret [] \<and>\<^sub>D Ret (xs = []) \<longrightarrow>\<^sub>D
                         \<langle>ret (foldl (\<lambda>r. op + (10 * r)) x xs)\<rangle>(\<lambda>n. Ret (n = 1) \<and>\<^sub>D Eot)"
	      apply(rule allI)
	      apply(rule pdl_eqD_aux1[THEN pdl_mp])
	      apply(rule pdl_eqD_aux2[THEN pdl_mp])
	      apply(simp)
	      apply(subst Eot_GetInput)
	      by (rule ret_one_aux)
	  qed
	qed
	ultimately
	show ?thesis by (rule pdl_plugD_lifted1)
      qed
      thus ?thesis by (simp add: natp_def many1_def mon_ctr del: bind_assoc)
    qed
  qed
  ultimately show ?thesis by (rule pdl_plugD)
qed

(*<*)
(* Testing ground for if and while rules *)



constdefs
  MonIf     :: "bool D \<Rightarrow> 'a T \<Rightarrow> 'a T \<Rightarrow> 'a T" ("IF _ THEN _ ELSE _ FI" [0, 0, 0] 100)
  "IF b THEN p ELSE q FI \<equiv> do {x\<leftarrow>\<Down> b; if x then p else q}"



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
