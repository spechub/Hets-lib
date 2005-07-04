(*
 
 Implementing (propositional) dynamic logic in Isabelle
 
 Theory Monads provides monadic operations and properties
 as well as a Haskell-style do-notation. 
 2005-02-13 Initial version by Dennis Walter
*)


header {* Basic monad definitions and laws. *}

theory Monads = Main:

text {*
 For the lack of constructor classes in Isabelle, we initially
 use functor @{text "T"} as a parameter standing for the monad in question.
*}

typedecl 'a T

arities T :: (type)type


text {* Monadic operations, decorated with Haskell-style syntax. *}

consts
 bind :: "'a T \<Rightarrow> ('a \<Rightarrow> 'b T) \<Rightarrow> 'b T"     (infixl "\<ggreater>=" 20)
 ret  :: "'a \<Rightarrow> 'a T"

constdefs
 seq :: "'a T \<Rightarrow> 'b T \<Rightarrow> 'b T"            (infixl "\<ggreater>" 20)
 "p \<ggreater> q \<equiv> (p \<ggreater>= (\<lambda>x. q))"

text {*
  The usual monad laws for bind and ret (not the Kleisli triple ones)
  including injectivity of @{term "ret"} for convenience.
*}

axioms
 bind_assoc [simp]: "(p \<ggreater>= (\<lambda>x. f x \<ggreater>= g)) = (p \<ggreater>= f \<ggreater>= g)"
 ret_lunit [simp]: "(ret x \<ggreater>= f) = f x"
 ret_runit [simp]: "(p \<ggreater>= ret) = p"
 ret_inject: "ret x = ret z \<Longrightarrow> x = z"

lemma seq_assoc [simp]: "(p \<ggreater> (q \<ggreater> r)) = (p \<ggreater> q \<ggreater> r)"
 by (simp add: seq_def)


text {*
  This sets up a Haskell-style `@{text "do {x\<leftarrow>p; q}"}' syntax 
  with multiple bindings inside one @{text "do"} term.
*}

nonterminals
 monseq

syntax (xsymbols)
 "_monseq"  :: "monseq \<Rightarrow> 'a T"                  ("(do {(_)})"    [5] 100)
 "_mongen"  :: "[pttrn, 'a T, monseq]\<Rightarrow> monseq"   ("(_\<leftarrow>(_);/ _)"  [10, 6, 5] 5)
 "_monexp"  :: "['a T, monseq]\<Rightarrow> monseq"         ("(_;/ _)"       [6, 5] 5)
 "_monexp0" :: "['a T] \<Rightarrow> monseq"                ("(_)"         5)

translations
 -- {* input macros; replace do-notation by @{term "bind"}/@{term "seq"} *}
 "_monseq(_mongen x p q)"    => "p \<ggreater>= (%x. (_monseq q))"
 "_monseq(_monexp p q)"      => "p \<ggreater> (_monseq q)"
 "_monseq(_monexp0 q)"       => "q"
 -- {* Retranslation of into the do-notation *}
 "_monseq(_mongen x p q)"    <= "p \<ggreater>= (%x. q)"
 "_monseq(_monexp p q)"      <= "p \<ggreater> q"
 -- {* Normalization macros `flattening' do-terms *}
 "_monseq(_mongen x p q)"    <= "_monseq (_mongen x p (_monseq q))"
 "_monseq(_monexp p q)"      <= "_monseq (_monexp p (_monseq q))"


text {* Actually, this rule does not contract, but rather expand monadic 
  sequences, but for historical reasons\dots
*}
lemma mon_ctr: "(do {x \<leftarrow> (do {y \<leftarrow> p; q y}); f x}) = (do {y \<leftarrow> p; x \<leftarrow> q y; f x})"
  by(rule bind_assoc[symmetric])

  

end
