theory HoareSyntax = dsefSyntax:

(* {{{ Definition of Hoare-Triples 
  e.g. @{text "{\<Phi>} do{x\<leftarrow>p;b\<leftarrow>\<Psi>;ret(x,b)} {ret(x,b)}"}. 
  The pre- and postconditions have to be converted 
  expicitly to @{type "bool T"} via ret if needed. }}} *)

constdefs 
  "hoare":: "bool D \<Rightarrow> 'a T \<Rightarrow> ('a \<Rightarrow> bool D) \<Rightarrow> bool"
  "hoare \<Phi> p \<Psi> == [a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>(\<Psi> x)] (a \<longrightarrow> b)"

nonterminals
  "hseq" "hstep" "cond"

syntax
  "_hoare"  :: "bool D \<Rightarrow> hseq \<Rightarrow> bool D \<Rightarrow> bool" ("\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>")

  "_hbind"  :: "[pttrn, 'a T] \<Rightarrow> hstep" ("_\<leftarrow>_")
  "_hseq"   :: "[hstep, hseq] \<Rightarrow> hseq"  ("_;_")
  "_hsingle":: "idt \<Rightarrow> hstep"  ("_")
  "_hstep"  :: "hstep \<Rightarrow> hseq"  ("_")

  "_hIn"   :: "hseq \<Rightarrow> hseq"
  "_hIn'"  :: "[pttrn, hseq] \<Rightarrow> hseq"
  "_hOut"  :: "[pttrn, hseq] \<Rightarrow> hseq"
  "_hOut'" :: "[pttrn, hseq] \<Rightarrow> hseq"

  "_tpl" :: "[pttrn, pttrn] \<Rightarrow> pttrn"

translations
  "_hoare \<Phi> (_hstep (_hsingle p)) \<Psi>"  => "hoare \<Phi> p (_K \<Psi>)"
  "_hoare \<Phi> (_hstep (_hsingle p)) \<Psi>"  <= "hoare \<Phi> p (\<lambda>x. \<Psi>)"
  "_hoare \<Phi> (_hstep (_hbind x p)) \<Psi>"  == "hoare \<Phi> p (\<lambda>x. \<Psi>)"
  "_hoare \<Phi> (_hseq p q) \<Psi>" ==  "_hoare \<Phi> (_hIn (_hseq p q)) \<Psi>"

  "_hoare \<Phi> (_hOut r) \<Psi>" =>  "hoare \<Phi> r (_K \<Psi>)"
  "_hoare \<Phi> (_hOut r) \<Psi>" <=  "hoare \<Phi> r (\<lambda>x. \<Psi>)"
  "_hoare \<Phi> (_hOut' tpl r) \<Psi>" ==  "hoare \<Phi> r (\<lambda>tpl. \<Psi>)"

  "_hIn (_hstep (_hsingle p))" => "_hOut p"
  "_hIn (_hstep (_hbind x p))" => "_hOut' x p"
  "_hIn (_hseq (_hsingle p) q)" => "_hseq (_hsingle p) (_hIn' q)"
  "_hIn (_hseq (_hbind x p) q)" => "_hseq (_hbind x p) (_hIn' x q)"

  "_hIn' tpl (_hstep (_hsingle p))" => 
             "_hOut' (_tpl tpl) (do{p;ret (_tpl tpl)})"
  "_hIn' tpl (_hstep (_hbind x p))" =>
             "_hOut' (_tpl (tpl,x)) (do{x\<leftarrow>p;ret (_tpl (tpl,x))})"
  "_hIn' tpl (_hseq (_hsingle p) q)" => 
             "_hseq (_hsingle p) (_hIn' tpl q)"
  "_hIn' tpl (_hseq (_hbind x p) q)" => 
             "_hseq (_hbind x p) (_hIn' (tpl,x) q)"

  "_hseq (_hsingle p) (_hOut q)" => 
             "_hOut (p \<guillemotright> q)"

  "_hseq (_hsingle p) (_hOut' tpl q)" => 
             "_hOut' tpl (p \<guillemotright> q)"
  "_hseq (_hbind x p) (_hOut' tpl q)" => 
             "_hOut' tpl (p \<guillemotright>= (\<lambda>x. q))"

  "_tpl (Pair (Pair x y) z)" => "_tpl (Pair x (Pair y z))"
  "_tpl (Pair x y)" => "(Pair x y)"

(* }}} *)

(* {{{ Hoare-Tuples }}} *)

text{*
  Somtimes we need Hoare-triples without a programm-sequence.
  For this purpose we have three posible versions
  1.    @{text "{\<Phi>}{a:\<Psi>}"}  - equvivalent to normal Hoare-Triples
  2./3. @{text "{\<Phi>}{\<Psi>}"} and @{text "\<Phi> \<Rightarrow>\<^isub>T \<Psi>"} - as syntactic sugar for 
  version 1*}

constdefs
  "hoare_Tupel" :: "bool D \<Rightarrow> bool D \<Rightarrow> bool"  ("\<lbrace>_\<rbrace> \<lbrace>_\<rbrace>")
  "hoare_Tupel \<Phi> \<Psi> == [(a,b)\<leftarrow>do{a\<leftarrow>\<down>\<Phi>;b\<leftarrow>\<down>\<Psi>;ret(a,b)}] (a\<longrightarrow>b)"

syntax
  "hoare\<^isub>2" :: "bool D \<Rightarrow> bool D \<Rightarrow> bool"  ("(_) \<Rightarrow>\<^isub>h (_)")
translations 
  "hoare\<^isub>2 \<Phi> \<Psi>" == "hoare_Tupel \<Phi> \<Psi>"
(* }}} *)

end