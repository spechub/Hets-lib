theory Test = Main:

(* shows how to prove implications without implicit use of impI in a proof
statement *)
lemma "A \<longrightarrow> A" proof -
  { assume "A"
    have "A" .
  }
  thus ?thesis by (rule impI)
qed



lemma "A \<longrightarrow> A"
proof -
  have "A \<Longrightarrow> A"
  proof -
    assume "A"
    show "A" .
  qed
  thus ?thesis by (rule impI) 
qed


lemma "(A \<longrightarrow> B) \<longrightarrow> (C \<or> A \<longrightarrow> B \<or> C)"
  by blast

(* Contraposition is intuitionistic in two cases: *)

lemma "\<lbrakk> ~Q; P \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> ~P"
  apply(rule notI)
  apply(rule notE)
  apply(assumption)
  apply(rules)
done

lemma "\<lbrakk> Q; P \<Longrightarrow> ~Q\<rbrakk> \<Longrightarrow> ~P"
  apply(rule notI)
  apply(rule notE)
  
  apply(rules)+
done

lemma "\<lbrakk> ~Q; ~P \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> P"
  oops


lemma "\<not>(P \<or> Q) \<Longrightarrow> \<not>P \<and> \<not>Q"
  apply(rule conjI)
  oops



constdefs
  xor :: "[bool, bool] \<Rightarrow> bool"        (infixr "\<oplus>" 20)
  "P \<oplus> Q \<equiv>  (P \<and> \<not> Q) \<or> (\<not> P \<and> Q)"



lemma "(P \<oplus> True) = (\<not> P)" 
  apply (unfold xor_def)
  by blast



lemma and_comm: "(A \<and> B) = (B \<and> A)" by blast
lemma and_assoc: "((A \<and> B) \<and> C) = (A \<and> (B \<and> C))" by blast
lemma and_LC:   "(A \<and> (B \<and> C)) = (B \<and> (A \<and> C))" by blast


lemma xor_comm: "(A \<oplus> B) = (B \<oplus> A)" by (unfold xor_def, blast)
lemma xor_assoc: "((A \<oplus> B) \<oplus> C) = (A \<oplus> (B \<oplus> C))" by (unfold xor_def, blast)
lemma xor_LC:    "(A \<oplus> (B \<oplus> C)) = (B \<oplus> (A \<oplus> C))" by (unfold xor_def, blast)

lemma and_True: "(A \<and> True) = A"  by blast
lemma and_False: "(A \<and> False) = False" by blast
lemma and_absorb: "(A \<and> A) = A" by blast
lemma xor_False: "(A \<oplus> False) = A" by (unfold xor_def, blast)
lemma xor_contr: "(A \<oplus> A) = False" by (unfold xor_def, blast)
lemma and_xor_rdistrib: "((A \<oplus> B) \<and> C) = ((A \<and> C) \<oplus> (B \<and> C))" by (unfold xor_def, blast)
lemma and_xor_ldistrib: "(C \<and> (A \<oplus> B)) = ((C \<and> A) \<oplus> (C \<and> B))" by (unfold xor_def, blast)

lemma imp_as_xor: "(A \<longrightarrow> B) = (A \<and> B \<oplus> A \<oplus> True)"
  by (unfold xor_def, blast)
lemma or_as_xor: "(A \<or> B) = (A \<oplus> B \<oplus> A \<and> B)"
  by (unfold xor_def, blast)
lemma not_as_xor: "(\<not> A) = (A \<oplus> True)" by (unfold xor_def, blast)
lemma iff_as_xor: "(A = B) = (A \<oplus> B \<oplus> True)"  by (unfold xor_def, blast)


lemma aux1: "(A \<and> (A \<and> B)) = (A \<and> B)" by blast
lemma aux2: "(True \<and> A) = A" by blast
lemma aux3: "(False \<and> A) = False" by blast
lemma aux4: "(False \<oplus> A) = A" by (unfold xor_def, blast)
lemma aux5: "(A \<oplus> (A \<oplus> B)) = B" by (unfold xor_def, blast)

lemmas prop_taut = and_comm and_assoc and_LC xor_comm xor_assoc xor_LC and_True
                   and_False and_absorb xor_False xor_contr 
                   and_xor_ldistrib and_xor_rdistrib
                   imp_as_xor or_as_xor not_as_xor iff_as_xor
                   aux1 aux2 aux3 aux4 aux5


lemma "(p \<and> q \<longrightarrow> r) = (p \<longrightarrow> q \<longrightarrow> r)"
  apply (simp only: prop_taut)
done

lemma "A --> B --> A"
  apply (simp only: prop_taut)
done

lemma "(C \<and> D \<or> E \<and> \<not>C) \<longrightarrow> A \<longrightarrow> (C \<and> D \<or> E \<and> \<not>C)"
  apply (simp only: prop_taut)
done

lemma "A \<and> B \<longrightarrow> A" 
  apply (simp only: prop_taut)
done

lemma "A \<or> B \<longrightarrow> B \<or> A \<or> C" by (simp only: prop_taut)


lemma "A \<or> B \<longrightarrow> (A \<longrightarrow> C) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> C" by (simp only: prop_taut)


lemma "p = p" by (simp only: prop_taut)

lemma "(p \<and> q) = (p \<and> (q \<or> \<not> p))" by (simp only: prop_taut)


lemma "((p \<longrightarrow> q) \<and> (\<not> p \<longrightarrow> r)) = ((p \<and> q) \<or> (\<not>p \<and> r))" 
by (simp only: prop_taut)


lemma "(p = q) = ((p \<and> q) \<or> (\<not>p \<and> \<not>q))" by (simp only: prop_taut)
