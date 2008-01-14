theory KleeneSyntax imports MultimonadSyntax begin

text{*Definition of monad type and the two monadic funtions 
  \quak{@{text "\<guillemotright>="}} and ret *}

consts   
  star1 :: "('a \<Rightarrow> 'a T) \<Rightarrow> ('a \<Rightarrow> 'a T)" ("_\<^sup>\<star>" [100] 10)

axioms
 unf_left:   "(p\<^sup>\<star>) = (\<lambda>x. p x \<oplus> ((p\<^sup>\<star>) x \<guillemotright>= p))"
 unf_right:  "(p\<^sup>\<star>) = (\<lambda>x. p x \<oplus> (p x \<guillemotright>= (p\<^sup>\<star>)))"
 ind_left:   "\<forall>x. ((p x \<guillemotright>= q) \<preceq> (q x)) \<Longrightarrow> \<forall>x. (((p\<^sup>\<star>) x \<guillemotright>= q) \<preceq> (q x))"
 ind_right:  "\<forall>x. ((p x \<guillemotright>= q) \<preceq> (p x)) \<Longrightarrow> \<forall>x. ((p x \<guillemotright>= (q\<^sup>\<star>)) \<preceq> (p x))"

constdefs
  test :: "bool \<Rightarrow> unit T"
  "(test b) == if b then ret () else \<delta>" 

syntax
  (* "_monseq"  :: "monseq \<Rightarrow> 'a T"                  ("(do {(_)})"    [5] 100) *)
  "_monstar"  :: "[pttrn, 'a T, monseq]\<Rightarrow> monseq"  ("((_\<leftarrow>\<^sup>\<star>(_));/ _)" [110,6,5]5)
  (* "_monexp"  :: "['a T, monseq]\<Rightarrow> monseq"         ("((_);/ _)"     [6,5] 5)
  "_monexp0" :: "['a T] \<Rightarrow> monseq"                ("(_)"           5) *)

translations
  (* input macros; replace do-notation by bind/seq *)
  "_monseq(_monstar x p q)"    => "(_monseq q) \<oplus> ((((%x. p)\<^sup>\<star>) x) \<guillemotright>= (%x. (_monseq q)))"
  (* Retranslation of bind/seq into do-notation *)
  (*"_monseq(_monstar x p q)"    <= "p \<guillemotright>= (%x. q)"*)
  (* Normalization macros *)
  "_monseq(_monstar x p q)"    <= "_monseq (_monstar x p (_monseq q))"

lemma unfLeft [simp]: "(do {x \<leftarrow>\<^sup>\<star> p x; q x}) = (q x \<oplus> do{x \<leftarrow>\<^sup>\<star> p x; x \<leftarrow> p x; q x})" 
  

end
