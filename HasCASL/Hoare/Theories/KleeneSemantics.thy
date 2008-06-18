theory KleeneSyntax imports MultimonadSyntax begin

text{*Definition of monad type and the two monadic funtions 
  \quak{@{text "\<guillemotright>="}} and ret *}


axioms
  ile_cpo: "\<forall>s :: nat \<Rightarrow> 'a T. (\<forall> i. s(i) \<preceq> s(i+1)) ==> (\<exists> ss. (\<forall> i. s(i) \<preceq> ss))"

consts   
  uplus :: "('a \<Rightarrow> 'a T) \<Rightarrow> ('a \<Rightarrow> 'a T)" ("_^[+]" [1000] 999)


end
