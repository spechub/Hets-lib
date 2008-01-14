theory MonadSyntax imports Main begin (*min. Product_Type*)

text{*Definition of monad type and the two monadic funtions 
  \quak{@{text "\<guillemotright>="}} and ret *}

typedecl 'a T

consts   
  bind  :: "'a T \<Rightarrow> ('a \<Rightarrow> 'b T) \<Rightarrow> 'b T"  ("_ \<guillemotright>=\ _" [5, 6] 5)
  ret   :: "'a \<Rightarrow> 'a T" 

constdefs 
  bind' :: "'a T \<Rightarrow> 'b T \<Rightarrow> 'b T"             ("_ \<guillemotright>\ _" [5, 6] 5)
  "bind' p q == bind p (\<lambda>x. q)"

text{*
  This sets up a Haskell-style \quak{@{text "do{x\<leftarrow>p;y\<leftarrow>q x;...}"}} 
  syntax. Initial taken from Christop Lueth and extended by Dennis Walter.
*}
nonterminals
  monseq

syntax
  "_monseq"  :: "monseq \<Rightarrow> 'a T"                  ("(do {(_)})"    [5] 100) 
  "_mongen"  :: "[pttrn, 'a T, monseq]\<Rightarrow> monseq"  ("((_\<leftarrow>(_));/ _)" [110,6,5]5)
  "_monexp"  :: "['a T, monseq]\<Rightarrow> monseq"         ("((_);/ _)"     [6,5] 5)
  "_monexp0" :: "['a T] \<Rightarrow> monseq"                ("(_)"           5)

translations
  (* input macros; replace do-notation by bind/seq *)
  "_monseq(_mongen x p q)"    => "p \<guillemotright>= (%x. (_monseq q))"
  "_monseq(_monexp p q)"      => "p \<guillemotright> (_monseq q)"
  "_monseq(_monexp0 q)"       => "q"
  (* Retranslation of bind/seq into do-notation *)
  "_monseq(_mongen x p q)"    <= "p \<guillemotright>= (%x. q)"
  "_monseq(_monexp p q)"      <= "p \<guillemotright> q"
  (* Normalization macros *)
  "_monseq(_monexp p q)"      <= "_monseq (_monexp p (_monseq q))"
  "_monseq(_mongen x p q)"    <= "_monseq (_mongen x p (_monseq q))"

text {*
  fstUnitLaw: left unity of ret\\ 
  sndUnitLaw: right unity of ret\\
  assocLaw: assiciativity*}

axioms
 lunit: "(ret x \<guillemotright>= p) = p x"
 runit: "(p \<guillemotright>= ret) = p"
 assoc: "(p \<guillemotright>= q \<guillemotright>= r) = (p \<guillemotright>= (\<lambda>x. q x \<guillemotright>= r))"
 injective: "ret x = ret z \<Longrightarrow> x = z"

lemma fstUnitLaw [simp]:  "(do {y\<leftarrow>ret x; p y}) = p x"
 by (rule lunit)

lemma sndUnitLaw [simp]:  "(do {x\<leftarrow>p; ret x}) = p"
 by (rule runit)

lemma assocLaw [simp]:  
  "do {y\<leftarrow>do {x\<leftarrow>p; q x}; r y} = do {x\<leftarrow>p; y\<leftarrow>q x;r y}"
  by (rule assoc)

text{* 
We also want associtivity for q and r coming along with no parameter. For 
this purpose we need three more variants of the assocLaw.
*}

lemma do_assoc1[simp]: 
  "(do{do{x\<leftarrow>p;q x}; r}) = (do {x\<leftarrow>p; q x; r})" 
  apply (unfold "bind'_def")
  by (rule assocLaw)

lemma do_assoc2[simp]: 
  "(do {x\<leftarrow>(do {p; q}); r x}) = (do {p; x\<leftarrow>q; r x})"
  apply (unfold "bind'_def")
  by (rule assocLaw)

lemma do_assoc3[simp]: 
  "(do {(do {p; q}); r})= (do {p; q; r})"
  apply (unfold "bind'_def")
  by (rule assocLaw)

lemma delBind[simp]: "do {x\<leftarrow>p; q} = do {p; q}"
  apply (unfold bind'_def)
  by simp

text{*Syntactic sugar for True and False*}
syntax
  "_b1"      :: "bool"                 ("\<top>")
  "_b2"      :: "bool"                 ("\<bottom>") 

translations
  "_b1" == "True"
  "_b2" == "False"

text{* @{text "\<alpha> res \<Phi> = \<alpha> iff \<alpha>"} is defined and @{text \<Phi>} holds*}
constdefs
  "res" :: "'a \<Rightarrow> bool \<Rightarrow> 'a" (infixl "res" 100)
  "\<alpha> res \<Phi> == if \<Phi> then \<alpha> else arbitrary"
 
text{* if\_then\_else lifted to monadic values *}
constdefs 
  if\<^isub>T :: "bool T \<Rightarrow> 'a T \<Rightarrow> 'a T \<Rightarrow> 'a T"   ("if\<^isub>T(_)then(_)else(_)")
  "if\<^isub>T b then p else q == do{x\<leftarrow>b;if x then p else q}" 

consts 
  iter\<^isub>T:: "('a \<Rightarrow> bool T) \<Rightarrow> ('a \<Rightarrow> 'a T) \<Rightarrow> 'a \<Rightarrow> 'a T"
  while\<^isub>T :: "bool T \<Rightarrow> unit T \<Rightarrow> unit T" ("while\<^isub>T (_) (_)")

axioms
  iter\<^isub>T_def: "iter\<^isub>T test f x = 
       do{if\<^isub>T (test x) then (do{y\<leftarrow>(f x);iter\<^isub>T test f y}) else (ret x)}"
  while\<^isub>T_def: "while\<^isub>T b p == iter\<^isub>T (\<lambda>x. b) (\<lambda>x. p) ()"

text{* some definitions for monadic-sequenzes*}
constdefs
  (* we can discard a sequence if it has no sideeffects *)
  "sef" :: "'a T \<Rightarrow> bool"  ("sef _")
  "sef p == (do{y\<leftarrow>p; ret ()} = ret ())" 

  (* if we have two copies of the same seqence, we can substitude the
    variable which was bound to the second seqenze-call by the first one 
    and remove the second call completely*)
  "cp" :: "'a T \<Rightarrow> bool"
  "cp p == (do{x\<leftarrow>p;y\<leftarrow>p;ret(x,y)} = do{x\<leftarrow>p;ret(x,x)})"

  (* We can expand the copabily sequence by every sequence which is of
    the type @{text "bool T"} and is copybal and dicardable. *)
  "com" :: "'a T \<Rightarrow> bool T \<Rightarrow> bool" ("_ comwith _")
  "(com p q) == (((cp q) \<and> (sef q)) \<longrightarrow> 
                  (cp(do {x\<leftarrow>p; y\<leftarrow>q; ret(x,y)})))"

text{* we can not quantify over types in com\_def. so we need a rule which
  lift the definition from bool T up to 'a T*}
(*axioms commute_tcoerc: 
  "\<forall>q::bool T.
       (cp q) \<and> (sef q) \<longrightarrow> (cp (do{x\<leftarrow>p; y\<leftarrow>q; ret(x,y)})) \<Longrightarrow>
   \<forall>q. (cp q) \<and> (sef q) \<longrightarrow> (cp (do{x\<leftarrow>p; y\<leftarrow>q; ret(x,y)}))"*)

axioms commute_tcoerc:
  "\<forall>q::bool T.(cp q) \<and> (sef q) \<longrightarrow> (cp (do{x\<leftarrow>p; y\<leftarrow>q; ret(x,y)})) \<Longrightarrow>
   \<forall>q. (cp q) \<and> (sef q) \<longrightarrow> (cp (do{x\<leftarrow>p; y\<leftarrow>q; ret(x,y)}))"

axioms tst: 
  "\<forall>x. \<forall>q::'b T. 
       (cp q) \<and> (sef q) \<longrightarrow> (cp (do{z\<leftarrow>p x; y\<leftarrow>q; ret(z,y)}))\<Longrightarrow>
   \<forall>x. (\<forall>q. (cp q) \<and> (sef q) \<longrightarrow> (cp (do{z\<leftarrow>p x; y\<leftarrow>q; ret(z,y)})))"

end