theory gdjSyntax = MonadSyntax:

text{*
  Definition of gdj-syntax for a calculus on which the
  Hoare-calculs can be proven easily.
*}
constdefs
  gdj :: "'a T \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"     ("[_]_" [0, 100] 100)
  "gdj p \<Phi> == 
    ((do {x\<^isub>g\<leftarrow>p; ret (\<Phi> x\<^isub>g, x\<^isub>g)}) = (do {x\<^isub>g\<leftarrow>p; ret (True, x\<^isub>g)}))"

  empty_gdj :: "bool \<Rightarrow> bool"
  "empty_gdj \<Phi> == (\<Phi> = True)"

text {*
  Syntax translations that let you write e.g.
@{text    "[x\<leftarrow>p; y\<leftarrow>q](ret (x=y))"}
  for 
@{text    "gdj (do {x\<leftarrow>p; y\<leftarrow>q; ret (x,y)}) (\<lambda>(x,y). (x=y))"}
  Essentially, these translations collect all bound variables inside the 
  boxes and return them as a tuple. The lambda term that constitutes the 
  second argument of gdj will then also take a tuple pattern as its sole
  argument. Moreover the tuple is sorted so that nested tupeling is 
  solved.
*}
nonterminals
  bndseq bndstep
 
syntax
  "_empty_gdj"  :: "[bool] \<Rightarrow> bool"                ("[ ]_" 100)
  "_gdj"       :: "[bndseq, bool] \<Rightarrow> bool"        ("[_]_" [0,100]100)

  "_gdjBnd"    :: "[pttrn, 'a T] \<Rightarrow> bndstep"      ("_\<leftarrow>_")
  "_gdjSeq"    :: "[bndstep, bndseq] \<Rightarrow> bndseq"   ("_;/ _")
  ""           :: "[bndstep] \<Rightarrow> bndseq"           ("_")

  "_gdjIn"     :: "[pttrn, bndseq] \<Rightarrow> bndseq"       
  "_gdjOut"    :: "[pttrn, bndseq] \<Rightarrow> bndseq"

  "_reTpl"     :: "[pttrn, pttrn] \<Rightarrow> pttrn"

translations 
  "_empty_gdj \<Phi>" == "empty_gdj \<Phi>"

  "_gdj (_gdjBnd x p) phi"  == "gdj p (\<lambda>x. phi)"
  "_gdj (_gdjSeq (_gdjBnd x p) r) phi"  
              =>  "gdj (_gdjSeq (_gdjBnd x p) (_gdjIn x x r)) phi"

  "_gdjIn tpl tpl' (_gdjSeq (_gdjBnd x p) r)"
              =>  "_gdjSeq (_gdjBnd x p) (_gdjIn (tpl, x) (tpl', x) r)"
  "_gdjIn tpl tpl' (_gdjBnd x p)"
              =>  "_gdjOut (_reTpl tpl' x) (do {x\<leftarrow>p; ret(_reTpl tpl x)})"

  "_gdjSeq (_gdjBnd x p) (_gdjOut tpl r)" ==  "_gdjOut tpl (do {x\<leftarrow>p; r})"

  "_reTpl (_tuple tpl (_tuple_arg x)) y" 
          => "_reTpl tpl (_tuple x (_tuple_arg y))"
  "_reTpl x y" => "(x,y)"

  "Pair x (_pattern y z)" => "Pair x (Pair y z)"
  "Pair (_pattern x y) z" => "Pair x (Pair y z)"
  "Pair x (_patterns y z)" => "Pair x (Pair y z)"
  "Pair (_patterns x y) z" => "Pair x (Pair y z)"
  "(_pattern x (_patterns y z))" => "Pair x (Pair y z)"

  "gdj (_gdjOut tpl r) phi" == "gdj r (\<lambda>tpl. phi)"

text{*syntax for encapsulation of sequences*}
consts
 gdj' :: "pttrn \<Rightarrow> 'a T \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
                                         ("[_\<prec>-_]_" [0, 100] 100)

syntax
  "_gdjPBnd"   :: "[idt, pttrn, 'a T] \<Rightarrow> bndstep" ("_\<prec>-_\<leftarrow>_")

translations
  "_gdj (_gdjSeq (_gdjPBnd u x p) r) phi"  
          =>  "gdj (_gdjSeq (_gdjBnd u p) (_gdjIn u x r)) phi"
  "_gdj (_gdjPBnd u x p) phi"  => "gdj p (\<lambda>x. phi)"

  "_gdjIn tpl tpl' (_gdjSeq (_gdjPBnd u x p) r)"
       =>  "_gdjSeq (_gdjBnd u p) (_gdjIn (tpl, u) (tpl', x) r)"
  "_gdjIn tpl tpl' (_gdjPBnd x u p)"
       =>  "_gdjOut (_reTpl tpl' u) (do {x\<leftarrow>p; ret(_reTpl tpl x)})"

end