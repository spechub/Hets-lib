theory HoareCalc =  HoareSyntax + dsefCalc:

lemma "dsef" : 
  assumes dsef_p: "dsef p"
  shows "\<lbrace>\<up>(ret True)\<rbrace> x\<leftarrow>p \<lbrace>\<up>(do{y\<leftarrow>p;ret(x=y)})\<rbrace>"
(* {{{ Proof }}} *)
  proof -
  from dsef_p have "sef p"
    by (simp add: dsef_def)
  moreover
  from dsef_p have "cp p"
    by (simp add: dsef_def)
  ultimately
  have "[x\<leftarrow>p;y\<leftarrow>p](x=y)"
    by (simp add: sef2cp)
  from this 
  have "[u\<leftarrow>do {x\<leftarrow>p; y\<leftarrow>p; ret (x, y)}](fst u = snd u)"
    by (simp add: gdj_def)
  from this 
  have "do{u\<leftarrow>do {x\<leftarrow>p; y\<leftarrow>p; ret (x, y)};
           ret (fst u = snd u, True, fst u, fst u = snd u)} =
    do{u\<leftarrow>do {x\<leftarrow>p; y\<leftarrow>p; ret (x, y)};
           ret (True, True, fst u, fst u = snd u)}"
    by (rule gdj2doSeq)
  moreover have "\<forall>x. (do {y\<leftarrow>p; ret (x = y)}) \<in> Dsef"
    proof -
      from dsef_p have Dsef_p: "p \<in> Dsef"
	by (simp add: Dsef_def)
      have "\<forall>(x::'a) y. dsef (ret(x=y))"
	by (simp add: dsef_ret)
      from this have Dsef_ret: "\<forall>(x::'a) y. ret(x=y) \<in> Dsef"
	by (simp add: Dsef_def)
      from Dsef_p have 
	"\<forall>x. ((\<forall>y. (ret(x=y)) \<in> Dsef) \<longrightarrow> 
	     (do {y\<leftarrow>p; ret (x=y)}) \<in> Dsef)"
	by (simp add: weak_Dsef2seq)
      from Dsef_ret this have "\<forall>x. (do {y\<leftarrow>p; ret (x=y)}) \<in> Dsef"
	by simp
      from this show ?thesis
	by simp
    qed
  moreover have "(ret True) \<in> Dsef"    
    proof -
      have "dsef (ret (True::bool))"
	by (simp add: dsef_ret)
      from this show ?thesis
	by (simp add: Dsef_def)
    qed
  ultimately show ?thesis
    apply (simp add: hoare_def)
    by (simp add: gdj_def)
qed (* }}} *)

lemma "dsef'":
  assumes dsef_q: "dsef q"
  shows "\<lbrace>\<Phi>\<rbrace>q\<lbrace>\<Phi>\<rbrace>" 
(* {{{ Proof }}} *)
proof -
  (*<*)  
  have Dsef_\<Phi>: "(\<down>\<Phi>) \<in> Dsef"
    by (simp add: Rep_Dsef)    
  from this have dsef_\<Phi>: "dsef \<down>\<Phi>"
    by (simp add: Dsef_def)    
  from dsef_\<Phi> have cp_\<Phi>: "cp \<down>\<Phi>"
    by (simp add: dsef_def)
  from dsef_\<Phi> have sef_\<Phi>: "sef \<down>\<Phi>"
    by (simp add: dsef_def)

  from dsef_q have cp_q: "cp q"
    by (simp add: dsef_def)
  from dsef_q have sef_q: "sef q"
    by (simp add: dsef_def)
  (*>*)  

  have "\<forall>u. ((fst u=snd(snd u)) \<longrightarrow> (fst u\<longrightarrow>snd(snd u)))"
    by simp
  moreover
  have "[a\<leftarrow>\<down>\<Phi>; x\<leftarrow>q; b\<leftarrow>\<down>\<Phi>](a=b)"
    proof -
      from dsef_\<Phi> have 
	"(\<forall>(q:: bool T). ((cp q) \<and> (sef q)) \<longrightarrow> 
	                 (cp (do {x\<leftarrow>\<down>\<Phi>; y\<leftarrow>q; ret (x, y)})))"
	by (simp add: dsef_def com_def)
      from this have 
	"(\<forall>(q:: 'a T). ((cp q) \<and> (sef q)) \<longrightarrow> 
	               cp (do {x\<leftarrow>\<down>\<Phi>; y\<leftarrow>q; ret (x, y)}))"
	by (rule commute_tcoerc)
      from dsef_\<Phi> sef_q cp_q this have cp_do: 
	"cp(do {x\<leftarrow>\<down>\<Phi>; y\<leftarrow>q; ret(x,y)})"
	by (simp add: dsef_def com_def)
      from sef_\<Phi> sef_q cp_do have 
	"do {x\<leftarrow>\<down>\<Phi>; y\<leftarrow>q; ret (x, y)} = do {y\<leftarrow>q; x\<leftarrow>\<down>\<Phi>; ret (x, y)}"
	by (rule "cpsefProps(i\<rightarrow>ii)") 
      from cp_\<Phi> sef_\<Phi> this show ?thesis
	by (simp add: "cpsefProps(ii\<rightarrow>iv)") 
    qed
  from this have 
    "[u\<leftarrow>do{a\<leftarrow>\<down>\<Phi>; x\<leftarrow>q; b\<leftarrow>\<down>\<Phi>;ret(a,x,b)}](fst u=snd(snd u))"
    by (simp add: gdj_def)
  ultimately
  have "[u\<leftarrow>do{a\<leftarrow>\<down>\<Phi>; x\<leftarrow>q; b\<leftarrow>\<down>\<Phi>;ret(a,x,b)}](fst u \<longrightarrow> snd(snd u))"
    by (rule wk)
  from this have "[a\<leftarrow>\<down>\<Phi>; x\<leftarrow>q; b\<leftarrow>\<down>\<Phi>] (a\<longrightarrow>b)"
    by (simp add: gdj_def)
  from this show ?thesis
    by (simp add: hoare_def)
qed (* }}} *)

lemma "stateless": "\<lbrace>\<Up>\<Phi>\<rbrace>p\<lbrace>\<Up>\<Phi>\<rbrace>"
(* {{{ Proof }}} *)
proof -
  have 
    "[(a,x,b)\<leftarrow>do {a\<leftarrow>ret \<Phi>; x\<leftarrow>p; b\<leftarrow>ret \<Phi>; ret (a,x,b)}](a\<longrightarrow>b)"
    apply (unfold gdj_def)
    by simp
  moreover have "\<down>\<Up>\<Phi> = ret \<Phi>"
    by (simp add: dsef_ret Dsef_def)
  ultimately show ?thesis
    by (simp only: hoare_def)
qed (* }}} *)

lemma "emptySeq": "\<forall>x. \<lbrace>\<Phi> x\<rbrace>\<lbrace>\<Phi> x\<rbrace>"
  proof -
    have "sef (ret ())"
      by (simp add: sef_def)
    moreover
    have "\<forall>x. \<lbrace>\<Phi> x\<rbrace>y\<leftarrow>ret()\<lbrace>\<Phi> x\<rbrace>"
      by (simp add: dsef_ret dsef')
    ultimately show ?thesis
      apply (simp add: hoare_def hoare_Tupel_def dsef_def)
      by (simp add: sef_rm2of3)
  qed

text{*You can concat two sequences, one ending up in state @{text \<Psi>} and 
  the other one starting in this state.\abs
Proof:\\
@{text "[a\<leftarrow>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<Psi> x;y\<leftarrow>q x;c\<leftarrow>\<xi> x y](a\<longrightarrow>b)"}\\
@{text "  [a\<leftarrow>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<Psi> x;y\<leftarrow>q x;c\<leftarrow>\<xi> x y](b\<longrightarrow>c)"}\\
  --------------------------------------------------- (andI)\\
@{text "  [a\<leftarrow>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<Psi> x;y\<leftarrow>q x;c\<leftarrow>\<xi> x y]((a\<longrightarrow>b) \<and>(b\<longrightarrow>c))"}\\
  --------------------------------------------------- (wk)\\
@{text "  [a\<leftarrow>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<Psi> x;y\<leftarrow>q x;c\<leftarrow>\<xi> x y](a\<longrightarrow>c)"}\\
  --------------------------------------------------- (dsef-remove @{text \<Psi>})\\
@{text "  [a\<leftarrow>\<Phi>;x\<leftarrow>p;       y\<leftarrow>q x;c\<leftarrow>\<xi> x y](a\<longrightarrow>c)"}
*}
lemma "seq":
  assumes a: "\<lbrace>\<Phi>\<rbrace>x\<leftarrow>p\<lbrace>\<Psi> x\<rbrace>" and b: "\<forall>x. \<lbrace>\<Psi> x\<rbrace>y\<leftarrow>q x\<lbrace>\<Upsilon> x y\<rbrace>"
  shows "\<lbrace>\<Phi>\<rbrace>x\<leftarrow>p;y\<leftarrow>q x\<lbrace>\<Upsilon> x y\<rbrace>"
(* {{{ Proof }}}*)
proof -  
  (*<*)  
  have Dsef_\<Psi>: "\<forall>x. (\<down>(\<Psi> x)) \<in> Dsef"
    by (simp add: Rep_Dsef)
  from this have dsef_\<Psi>: "\<forall>x. dsef (\<down>(\<Psi> x))"
    by (simp add: Dsef_def)
  (*>*)  

  have a': "[a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>(\<Psi> x);y\<leftarrow>q x;c\<leftarrow>\<down>(\<Upsilon> x y)](a\<longrightarrow>b)"
    (* {{{ Proof }}}*)
    proof -
      from a have "[a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>(\<Psi> x)](a\<longrightarrow>b)"
	by (simp add: hoare_def)
      from this have 
	"[a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>(\<Psi> x);u\<leftarrow>do{y\<leftarrow>q x;c\<leftarrow>\<down>(\<Upsilon> x y);ret (y,c)}]
	                                                    (a\<longrightarrow>b)"
	by (rule app_exp')
      from this show ?thesis
	by (simp add: gdj_def)
    qed
    (* }}} *)
  moreover
  have b': "[a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>(\<Psi> x);y\<leftarrow>q x;c\<leftarrow>\<down>(\<Upsilon> x y)](b\<longrightarrow>c)"    
    (* {{{ Proof }}}*)
    proof -
      from b have 
	"\<forall>a x. [u\<prec>-(b,y,c)\<leftarrow>do{b\<leftarrow>\<down>(\<Psi> x);y\<leftarrow>q x;c\<leftarrow>\<down>(\<Upsilon> x y);
	                                        ret(b,y,c)}](b\<longrightarrow>c)"
	by (simp add: hoare_def gdj_def)
      from this have 
	"[a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;u\<prec>-(b,y,c)\<leftarrow>do{b\<leftarrow>\<down>(\<Psi> x);y\<leftarrow>q x;c\<leftarrow>\<down>(\<Upsilon> x y);
	                                        ret(b,y,c)}](b\<longrightarrow>c)"
	by (rule pre_exp)
      from this show ?thesis
	by simp
    qed
    (* }}} *)
  ultimately have conj: 
    "[a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>(\<Psi> x);y\<leftarrow>q x;c\<leftarrow>\<down>(\<Upsilon> x y)]((a\<longrightarrow>b)\<and>(b\<longrightarrow>c))"
    (* {{{ Proof }}}*)
    proof -
      from a' have 
	"[u\<prec>-(a,x,b,y,c)\<leftarrow>do{a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>(\<Psi> x);y\<leftarrow>q x;c\<leftarrow>\<down>(\<Upsilon> x y);
	                 ret(a,x,b,y,c)}](a\<longrightarrow>b)"
	by simp
      from this have 
	"[u\<leftarrow>do{a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>(\<Psi> x);y\<leftarrow>q x;c\<leftarrow>\<down>(\<Upsilon> x y);
	                 ret(a,x,b,y,c)}](fst u\<longrightarrow>fst(snd(snd u)))"
	by (simp add: gdj_def)
      moreover
      from b' have 
	"[u\<prec>-(a,x,b,y,c)\<leftarrow>do{a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>(\<Psi> x);y\<leftarrow>q x;c\<leftarrow>\<down>(\<Upsilon> x y);
	                 ret(a,x,b,y,c)}](b\<longrightarrow>c)"
	by simp
      from this have 
	"[u\<leftarrow>do{a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>(\<Psi> x);y\<leftarrow>q x;c\<leftarrow>\<down>(\<Upsilon> x y);
	                 ret(a,x,b,y,c)}]
	                 (fst(snd(snd u))\<longrightarrow>snd(snd(snd(snd u))))"
	by (simp add: gdj_def)
      ultimately
      have 
	"[u\<leftarrow>do{a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>(\<Psi> x);y\<leftarrow>q x;c\<leftarrow>\<down>(\<Upsilon> x y);
	                 ret(a,x,b,y,c)}]
                         ((fst u\<longrightarrow>fst(snd(snd u))) \<and> 
	                  (fst(snd(snd u))\<longrightarrow>snd(snd(snd(snd u)))))"
	by (rule andI)
      from this have
	"[u\<prec>-(a,x,b,y,c)\<leftarrow>do{a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>(\<Psi> x);y\<leftarrow>q x;c\<leftarrow>\<down>(\<Upsilon> x y);
	                         ret(a,x,b,y,c)}]((a\<longrightarrow>b) \<and> (b\<longrightarrow>c))"
	by (simp add: gdj_def)
      from this show ?thesis
	by simp
    qed
    (* }}} *)
  from this have "[a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>(\<Psi> x);y\<leftarrow>q x;c\<leftarrow>\<down>(\<Upsilon> x y)](a\<longrightarrow>c)"
    (* {{{ Proof }}}*)
    proof -
      have "\<forall>u. (((fst u)\<longrightarrow>(fst(snd(snd u)))) \<and> 
	        (fst(snd(snd u))\<longrightarrow>snd(snd(snd (snd u))))) \<longrightarrow>
	         (fst u \<longrightarrow> snd(snd(snd (snd u))))"
	by simp
      moreover
      from conj have 
	"[u\<leftarrow>do {a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>\<Psi> x;y\<leftarrow>q x;c\<leftarrow>\<down>\<Upsilon> x y;ret (a,x,b,y,c)}]
	                           (((fst u)\<longrightarrow>(fst(snd(snd u)))) \<and>
	                 (fst(snd(snd u))\<longrightarrow>snd(snd(snd (snd u)))))"
	by (simp add: gdj_def)
      ultimately have 
	"[u\<leftarrow>do {a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>\<Psi> x;y\<leftarrow>q x;c\<leftarrow>\<down>\<Upsilon> x y;ret (a,x,b,y,c)}]
	                        (((fst u)\<longrightarrow>snd(snd(snd (snd u)))))"
	by (rule wk)
      from this show ?thesis
	by (simp add: gdj_def)
    qed
    (* }}} *)
  moreover
  from dsef_\<Psi>
  have "\<forall>x. sef \<down>(\<Psi> x)"
    by (simp add: dsef_def)
  from this have 
    "[a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>(\<Psi> x);y\<leftarrow>q x;c\<leftarrow>\<down>(\<Upsilon> x y)](a\<longrightarrow>c) \<Longrightarrow> 
     [a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;y\<leftarrow>q x;c\<leftarrow>\<down>(\<Upsilon> x y)](a\<longrightarrow>c)"
    by (simp add: sef_rm3of5)
  ultimately
  have box: "[a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;y\<leftarrow>q x;c\<leftarrow>\<down>(\<Upsilon> x y)](a\<longrightarrow>c)"
    by simp
  from this show ?thesis
    (* {{{ Proof }}}*)
    proof -
      from box have 
	"[u\<leftarrow>do{a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;y\<leftarrow>q x;c\<leftarrow>\<down>(\<Upsilon> x y);ret(a,x,y,c)}]
	                      (fst u\<longrightarrow>(snd(snd(snd u))))"
	by (simp add: gdj_def)
      from this have
	"do{u\<leftarrow>do{a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;y\<leftarrow>q x;c\<leftarrow>\<down>(\<Upsilon> x y);ret(a,x,y,c)};
            ret(fst u\<longrightarrow>snd(snd(snd u)),fst u,
	        (fst(snd u),fst(snd(snd u))),snd(snd(snd u)))} =
	do{u\<leftarrow>do{a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;y\<leftarrow>q x;c\<leftarrow>\<down>(\<Upsilon> x y);ret(a,x,y,c)};
            ret(True,fst u,
	        (fst(snd u),fst(snd(snd u))),snd(snd(snd u)))}"
	by (rule gdj2doSeq)
      from this show ?thesis
	by (simp add: hoare_def gdj_def)
    qed
    (* }}} *)
qed
(* }}} *)

text{*sequencing works also for longer sequences*}
lemma "seq_exp":
  assumes a: "\<lbrace>\<Phi>\<rbrace>x\<leftarrow>p;y\<leftarrow>q x\<lbrace>\<Psi> x y\<rbrace>" and 
          b: "\<forall>x y. \<lbrace>\<Psi> x y\<rbrace>z\<leftarrow>r x y\<lbrace>\<Upsilon> x y z\<rbrace>"
  shows "\<lbrace>\<Phi>\<rbrace>x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y\<lbrace>\<Upsilon> x y z\<rbrace>"
proof -
  from a have "\<lbrace>\<Phi>\<rbrace>u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;ret(x,y)}\<lbrace>\<Psi> (fst u) (snd u)\<rbrace>"
    by (simp add: hoare_def)
  moreover from b have 
    "\<forall>u. \<lbrace>\<Psi> (fst u) (snd u)\<rbrace>
             z\<leftarrow>r (fst u)(snd u)
         \<lbrace>\<Upsilon> (fst u) (snd u) z\<rbrace>"
    by (simp add: hoare_def)
  ultimately have 
    "\<lbrace>\<Phi>\<rbrace>
        u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;ret(x,y)};z\<leftarrow>r (fst u) (snd u)
     \<lbrace>\<Upsilon> (fst u) (snd u) z\<rbrace>"
    by (rule seq)
  from this have 
    "[u\<leftarrow>do {a\<leftarrow>\<down>\<Phi>; x\<leftarrow>p; y\<leftarrow>q x; z\<leftarrow>r x y; b\<leftarrow>\<down>\<Upsilon> x y z;
                        ret (a,((x,y),z),b)}](fst u \<longrightarrow> snd(snd u))"
    by (simp add: hoare_def gdj_def)
  from this have 
    "do {u\<leftarrow>do{a\<leftarrow>\<down>\<Phi>; x\<leftarrow>p; y\<leftarrow>q x; z\<leftarrow>r x y; b\<leftarrow>\<down>\<Upsilon> x y z; 
                 ret(a,((x,y),z),b)};
                 ret (fst u \<longrightarrow> snd(snd u),
                      fst u,(fst(fst(fst(snd u))),
                      snd(fst(fst(snd u))),snd(fst(snd u))), 
                      snd(snd u))} =
     do {u\<leftarrow>do{a\<leftarrow>\<down>\<Phi>; x\<leftarrow>p; y\<leftarrow>q x; z\<leftarrow>r x y; b\<leftarrow>\<down>\<Upsilon> x y z; 
                 ret(a,((x,y),z),b)};
                 ret (True,
                      fst u,(fst(fst(fst(snd u))),
                      snd(fst(fst(snd u))),snd(fst(snd u))), 
                      snd(snd u))}"
    by (rule gdj2doSeq)
  from this show ?thesis
    by (simp add: hoare_def gdj_def)
qed

lemma "hoare_ctr":
  assumes "\<lbrace>\<Phi>\<rbrace>x\<leftarrow>p;y\<leftarrow>r x\<lbrace>\<Psi> y\<rbrace>"
  shows "\<lbrace>\<Phi>\<rbrace>y\<leftarrow>(do{x\<leftarrow>p;r x})\<lbrace>\<Psi> y\<rbrace>"
proof -
  from prems have 
    "[u\<leftarrow>do {a\<leftarrow>\<down>\<Phi>; x\<leftarrow>p; y\<leftarrow>r x; b\<leftarrow>\<down>\<Psi> y; ret (a, (x, y), b)}]
                                               (fst u\<longrightarrow>snd(snd u))"
    by (simp add: hoare_def gdj_def)
  from this have 
    "do {u\<leftarrow>do {a\<leftarrow>\<down>\<Phi>; x\<leftarrow>p; y\<leftarrow>r x; b\<leftarrow>\<down>\<Psi> y; ret (a, (x, y), b)};
         ret (fst u\<longrightarrow>snd(snd u), fst u, fst(fst(snd u)), 
         snd (fst(snd u)), snd(snd u))} =
    do {u\<leftarrow>do {a\<leftarrow>\<down>\<Phi>; x\<leftarrow>p; y\<leftarrow>r x; b\<leftarrow>\<down>\<Psi> y; ret (a, (x, y), b)};
         ret (True, fst u, fst(fst(snd u)), 
         snd (fst(snd u)), snd(snd u))}"
    by (rule gdj2doSeq)
  from this have 
    "[(a,x,y,b)\<leftarrow>do {a\<leftarrow>\<down>\<Phi>; x\<leftarrow>p; y\<leftarrow>r x; b\<leftarrow>\<down>\<Psi> y; 
                                        ret (a, x, y, b)}](a \<longrightarrow> b)"
    by (simp add: gdj_def)
  moreover from this show ?thesis
    apply (simp only: hoare_def)
    apply (rule ctr)
    by simp
qed  

text{*
  You can weaken pre- and postconditions @{text \<Phi>} and @{text \<Psi>} with @{text \<Phi>}' and @{text \<Psi>}'
  if from @{text \<Phi>} follows @{text \<Phi>}' and from @{text \<Psi>}' follows @{text \<Psi>}.\abs
Proof:\\
@{text   "[a\<leftarrow>\<Phi>';b\<leftarrow>\<Phi>](a\<longrightarrow>b)"}\\
  --------------------------------- (app)\\
(1)@{text   "[a\<leftarrow>\<Phi>';b\<leftarrow>\<Phi>;x\<leftarrow>p;c\<leftarrow>\<Psi> x](a\<longrightarrow>b)"}\\
---\\
@{text   "[        b\<leftarrow>\<Phi>;x\<leftarrow>p;c\<leftarrow>\<Psi> x](b\<longrightarrow>c)"}\\
  --------------------------------- (pre)\\
(2)@{text "[a\<leftarrow>\<Phi>';b\<leftarrow>\<Phi>;x\<leftarrow>p;c\<leftarrow>\<Psi> x](b\<longrightarrow>c)"}\\
---\\
                    (1) (2)\\
  ------------------------------------------ (andI)\\
@{text   "[a\<leftarrow>\<Phi>';b\<leftarrow>\<Phi>;x\<leftarrow>p;c\<leftarrow>\<Psi> x]((a\<longrightarrow>b) \<and>(b\<longrightarrow>c))"}\\
  ------------------------------------------ (wk) (dsef-remove @{text \<Phi>})\\
(3)   @{text "[a\<leftarrow>\<Phi>';x\<leftarrow>p;c\<leftarrow>\<Psi> x] (a\<longrightarrow>c)"}\\
---\\
with @{text "\<forall>a x. [c\<leftarrow>\<Psi> x;d\<leftarrow>\<Psi>' x](c\<longrightarrow>d)"} and (3) follow the same
tactic as the proof of (3) gets:\\
@{text      "[a\<leftarrow>\<Phi>';x\<leftarrow>p;d\<leftarrow>\<Psi>' x] (a\<longrightarrow>d)"}
*}
lemma "wk":
  assumes a: "\<lbrace>\<Phi>\<rbrace>x\<leftarrow>p\<lbrace>\<Psi> x\<rbrace>" and b: "\<Phi>'\<Rightarrow>\<^isub>h \<Phi>" and 
  c: "\<forall>x. (\<Psi> x) \<Rightarrow>\<^isub>h (\<Psi>' x)"   
  shows "\<lbrace>\<Phi>'\<rbrace>x\<leftarrow>p\<lbrace>\<Psi>' x\<rbrace>"
(* {{{ Proof }}} *)
proof -
  (*<*)  
  have Dsef_\<Phi>: "\<down>\<Phi> \<in> Dsef"
    by (simp add: Rep_Dsef)    
  from this have dsef_\<Phi>: "dsef (\<down>\<Phi>)"
    by (simp add: Dsef_def)
  from this have sef_\<Phi>: "sef (\<down>\<Phi>)"
    by (simp add: dsef_def)
  have Dsef_\<Psi>: "\<forall>x. (\<down>\<Psi> x) \<in> Dsef"
    by (simp add: Rep_Dsef)    
  from this have dsef_\<Psi>: "\<forall>x. dsef (\<down>\<Psi> x)"
    by (simp add: Dsef_def)
  from this have sef_\<Psi>: "\<forall>x. sef (\<down>\<Psi> x)"
    by (simp add: dsef_def)
  (*>*)  

  have d: "[a\<leftarrow>\<down>\<Phi>';b\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;c\<leftarrow>\<down>(\<Psi> x)] ((a\<longrightarrow>b) \<and> (b\<longrightarrow>c))"
  (* {{{ Proof }}} *)
  proof -
    from b have "[a\<leftarrow>\<down>\<Phi>';b\<leftarrow>\<down>\<Phi>](a\<longrightarrow>b)"
      by (simp add: hoare_Tupel_def)
    from this have 
      "[a\<leftarrow>\<down>\<Phi>';b\<leftarrow>\<down>\<Phi>;u\<leftarrow>do{x\<leftarrow>p;c\<leftarrow>\<down>(\<Psi> x);ret(x,c)}](a\<longrightarrow>b)"
      by (rule app_exp)
    from this have d: "[a\<leftarrow>\<down>\<Phi>';b\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;c\<leftarrow>\<down>(\<Psi> x)](a\<longrightarrow>b)"
      by (simp add: gdj_def)
    from a have 
      "\<forall>a. [u\<leftarrow>do{b\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;c\<leftarrow>\<down>(\<Psi> x);ret(b,x,c)}]
                                               (fst u\<longrightarrow>snd(snd u))"
      by (simp add: hoare_def gdj_def)
    from this have 
      "[a\<leftarrow>\<down>\<Phi>';u\<leftarrow>do{b\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;c\<leftarrow>\<down>(\<Psi> x);ret(b,x,c)}]
                                               (fst u\<longrightarrow>snd(snd u))"
      by (rule pre)
    from this have "[a\<leftarrow>\<down>\<Phi>';b\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;c\<leftarrow>\<down>(\<Psi> x)](b\<longrightarrow>c)"
      by (simp add: gdj_def)
    from d this show ?thesis
      by (rule andI_exp)
  qed
  (* }}} *)
  from d have "[a\<leftarrow>\<down>\<Phi>';b\<leftarrow>(\<down>\<Phi>);x\<leftarrow>p;c\<leftarrow>\<down>\<Psi> x] (a\<longrightarrow>c)"
  (* {{{ Proof }}} *)
  proof -
    have "\<forall>a b x c. ((a\<longrightarrow>b) \<and> (b\<longrightarrow>c)) \<longrightarrow> (a\<longrightarrow>c)"
      by simp
    moreover
    assume "[a\<leftarrow>\<down>\<Phi>';b\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;c\<leftarrow>\<down>\<Psi> x] ((a\<longrightarrow>b) \<and> (b\<longrightarrow>c))"    
    ultimately show ?thesis
      by (rule wk_exp)
  qed
  (* }}} *)
  from sef_\<Phi> this have "[a\<leftarrow>\<down>\<Phi>';x\<leftarrow>p;c\<leftarrow>\<down>\<Psi> x] (a\<longrightarrow>c)"
    by (rule sef_rm2of4)
  from this have e: "[a\<leftarrow>\<down>\<Phi>';x\<leftarrow>p;c\<leftarrow>\<down>\<Psi> x;d\<leftarrow>\<down>\<Psi>' x] ((a\<longrightarrow>c) \<and> (c\<longrightarrow>d))"
  (* {{{ Proof }}} *)
  proof -
    assume "[a\<leftarrow>\<down>\<Phi>';x\<leftarrow>p;c\<leftarrow>\<down>\<Psi> x] (a\<longrightarrow>c)"
    from this have "[a\<leftarrow>\<down>\<Phi>';x\<leftarrow>p;c\<leftarrow>\<down>\<Psi> x;d\<leftarrow>\<down>\<Psi>' x] (a\<longrightarrow>c)"
      by (rule app_exp')
    moreover
    from c have 
      "\<forall>a x. [u\<leftarrow>do{c\<leftarrow>\<down>\<Psi> x;d\<leftarrow>\<down>\<Psi>' x;ret(c,d)}](fst u\<longrightarrow>snd u)"
      by (simp add: gdj_def hoare_Tupel_def)
    from this have 
      "[a\<leftarrow>\<down>\<Phi>';x\<leftarrow>p;u\<leftarrow>do{c\<leftarrow>\<down>\<Psi> x;d\<leftarrow>\<down>\<Psi>' x;ret(c,d)}](fst u\<longrightarrow>snd u)"
      by (rule pre_exp)
    from this have "[a\<leftarrow>\<down>\<Phi>';x\<leftarrow>p;c\<leftarrow>\<down>\<Psi> x;d\<leftarrow>\<down>\<Psi>' x](c\<longrightarrow>d)"
      by (simp add: gdj_def)
    ultimately
    show ?thesis
      by (rule andI_exp)
  qed
  (* }}} *)
  from e have "[a\<leftarrow>\<down>\<Phi>';x\<leftarrow>p;c\<leftarrow>\<down>\<Psi> x;d\<leftarrow>\<down>\<Psi>' x] (a\<longrightarrow>d)"
  (* {{{ Proof }}} *)
  proof -
    have "\<forall>a x c d. ((a\<longrightarrow>c) \<and> (c\<longrightarrow>d)) \<longrightarrow> (a\<longrightarrow>d)"
      by simp
    moreover
    assume "[a\<leftarrow>\<down>\<Phi>';x\<leftarrow>p;c\<leftarrow>\<down>\<Psi> x;d\<leftarrow>\<down>\<Psi>' x] ((a\<longrightarrow>c) \<and> (c\<longrightarrow>d))"
    ultimately
    show ?thesis
      by (rule wk_exp)  
  qed
  (* }}} *)
  from sef_\<Psi> this have "[a\<leftarrow>\<down>\<Phi>'; x\<leftarrow>p; d\<leftarrow>\<down>\<Psi>' x](a \<longrightarrow> d)"
    by (rule sef_rm3of4)
  from this show ?thesis
    by (simp add: hoare_def)
qed
(* }}} *)

text{* Most of the time you only want to weaken pre- or postcondition 
instead of both. For this purpose wk\_pre and wk\_post take care of the
unchanged condition.*}
lemma "wk_pre":
  assumes a: "\<lbrace>\<Phi>\<rbrace>x\<leftarrow>p\<lbrace>\<Psi> x\<rbrace>" and b: "\<Phi>'\<Rightarrow>\<^isub>h \<Phi>"
  shows "\<lbrace>\<Phi>'\<rbrace>x\<leftarrow>p\<lbrace>\<Psi> x\<rbrace>"
proof -
  have "\<forall>x. \<lbrace>\<Psi> x\<rbrace>\<lbrace>\<Psi> x\<rbrace>"
    by (rule emptySeq)
  from a b this show ?thesis
    by (rule wk)
qed

lemma "wk_post":
  assumes a: "\<lbrace>\<Phi>\<rbrace>x\<leftarrow>p\<lbrace>\<Psi> x\<rbrace>" and c: "\<forall>x. (\<Psi> x) \<Rightarrow>\<^isub>h (\<Psi>' x)"   
  shows "\<lbrace>\<Phi>\<rbrace>x\<leftarrow>p\<lbrace>\<Psi>' x\<rbrace>"
proof -
  have "\<lbrace>\<Phi>\<rbrace>\<lbrace>\<Phi>\<rbrace>"
    apply (rule allE)
    apply (rule emptySeq)
    by simp
  from a this c show ?thesis
    by (rule wk)
qed

text{*
  Two Hoare-Triples with differnt preconditions @{text \<Phi>} and @{text \<Psi>} 
  but eqal sequence and postcondition can be combined to one Hoare-Triple
  with precondition @{text "\<Phi> \<or> \<Psi>"}\abs
Proof:\\
@{text   "[a\<leftarrow>\<Phi>;     x\<leftarrow>p;b\<leftarrow>\<xi> x](a \<longrightarrow> b)"}\\
  --------------------------------- (pre) (dsef-switch)\\
(1)@{text "[a\<leftarrow>\<Phi>;c\<leftarrow>\<Psi>;x\<leftarrow>p;b\<leftarrow>\<xi> x](a \<longrightarrow> b)"}\\
---\\
@{text   "[c\<leftarrow>\<Psi>; x\<leftarrow>p; b\<leftarrow>\<xi> x](c \<longrightarrow> b)"}\\
  --------------------------------- (pre)\\
(2)@{text "[a\<leftarrow>\<Phi>;c\<leftarrow>\<Psi>;x\<leftarrow>p;b\<leftarrow>\<xi> x](c \<longrightarrow> b)"}\\
---\\
                    (1) (2)\\
  ----------------------------------------------- (andI)\\
@{text   "[a\<leftarrow>\<Phi>;c\<leftarrow>\<Psi>;x\<leftarrow>p;b\<leftarrow>\<xi> x]((a\<longrightarrow>b) \<and>(c \<longrightarrow> b))"}\\
  ------------------------------------------------ (wk)\\
@{text   "[a\<leftarrow>\<Phi>;c\<leftarrow>\<Psi>;x\<leftarrow>p;b\<leftarrow>\<xi> x](a\<or>c \<longrightarrow> b)"}\\
  ------------------------------------------------ (preOp)\\
@{text   "[d\<leftarrow>do{a\<leftarrow>\<Phi>;c\<leftarrow>\<Psi>;ret(a\<or>c)};x\<leftarrow>p;b\<leftarrow>\<xi> x] (d\<longrightarrow>b)"}
*}
lemma "disj":
  assumes a: "\<lbrace>\<Phi>\<rbrace> x\<leftarrow>p \<lbrace>\<Upsilon> x\<rbrace>" and b:"\<lbrace>\<Psi>\<rbrace> x\<leftarrow>p \<lbrace>\<Upsilon> x\<rbrace>"
  shows "\<lbrace>(\<Phi>\<or>\<^isub>D\<Psi>)\<rbrace> x\<leftarrow>p \<lbrace>\<Upsilon> x\<rbrace>"
(* {{{ Proof }}} *)
proof -
  (*<*)  
  have Dsef_\<Phi>: "\<down>\<Phi> \<in> Dsef"
    by (simp add: Rep_Dsef)    
  from this have dsef_\<Phi>: "dsef \<down>\<Phi>"
    by (simp add: Dsef_def)
  have Dsef_\<Psi>: "\<down>\<Psi> \<in> Dsef"
    by (simp add: Rep_Dsef)    
  from this have dsef_\<Psi>: "dsef \<down>\<Psi>"
    by (simp add: Dsef_def)
  (*>*)  

  have 
    "[(a,c,x,b)\<leftarrow>do{a\<leftarrow>\<down>\<Phi>;c\<leftarrow>\<down>\<Psi>;x\<leftarrow>p;b\<leftarrow>\<down>\<Upsilon> x;ret(a,c,x,b)}] (a \<longrightarrow> b)"
  (* {{{ Proof }}} *)
    proof -
      from a have 
	"\<forall>c. [u\<leftarrow>do {a\<leftarrow>\<down>\<Phi>; x\<leftarrow>p; b\<leftarrow>\<down>\<Upsilon> x; ret (a, x, b)}]
	                                    (fst u \<longrightarrow> snd (snd u))"
	by (simp add: hoare_def gdj_def)
      from this have 
	"[c\<leftarrow>\<down>\<Psi>; u\<leftarrow>do {a\<leftarrow>\<down>\<Phi>; x\<leftarrow>p; b\<leftarrow>\<down>\<Upsilon> x; ret (a, x, b)}]
	                                    (fst u \<longrightarrow> snd (snd u))"
	by (rule pre)
      from this 
      have "[c\<leftarrow>\<down>\<Psi>; a\<leftarrow>\<down>\<Phi>; x\<leftarrow>p; b\<leftarrow>\<down>\<Upsilon> x](a \<longrightarrow> b)"
	by (simp add: gdj_def)
      from this dsef_\<Phi> dsef_\<Psi> have 
	"[a\<leftarrow>\<down>\<Phi>; c\<leftarrow>\<down>\<Psi>;x\<leftarrow>p; b\<leftarrow>\<down>\<Upsilon> x](a \<longrightarrow> b)"
	apply (subst dsef_switch)
	apply simp 
	apply simp .
      from this prems show ?thesis
	by (simp add: gdj_def)
    qed
  (* }}} *)
  moreover
  from b have 
    "[(a,c,x,b)\<leftarrow>do{a\<leftarrow>\<down>\<Phi>;c\<leftarrow>\<down>\<Psi>;x\<leftarrow>p;b\<leftarrow>\<down>\<Upsilon> x;ret(a,c,x,b)}] (c \<longrightarrow> b)"
  (* {{{ Proof }}} *)
    proof -
      from prems have 
	"\<forall>a. [u\<leftarrow>do {c\<leftarrow>\<down>\<Psi>; x\<leftarrow>p; b\<leftarrow>\<down>\<Upsilon> x; ret (c, x, b)}]
	                                    (fst u \<longrightarrow> snd (snd u))"
	by (simp add: hoare_def gdj_def)
      from this have 
	"[a\<leftarrow>\<down>\<Phi>; u\<leftarrow>do {c\<leftarrow>\<down>\<Psi>; x\<leftarrow>p; b\<leftarrow>\<down>\<Upsilon> x; ret (c, x, b)}]
	                                    (fst u \<longrightarrow> snd (snd u))"
	by (rule pre)
      from this show ?thesis
	by (simp add: gdj_def)
    qed
  (* }}} *)
  ultimately have 
    "[(a,c,x,b)\<leftarrow>do{a\<leftarrow>\<down>\<Phi>;c\<leftarrow>\<down>\<Psi>;x\<leftarrow>p;b\<leftarrow>\<down>\<Upsilon> x;ret(a,c,x,b)}] 
                                                 ((a\<longrightarrow>b) \<and> (c\<longrightarrow>b))"
    by (rule andI_exp)
  from this have 
    "[(a,c,x,b)\<leftarrow>do{a\<leftarrow>\<down>\<Phi>;c\<leftarrow>\<down>\<Psi>;x\<leftarrow>p;b\<leftarrow>\<down>\<Upsilon> x;ret(a,c,x,b)}] (a\<or>c\<longrightarrow>b)"
    by (simp add: wk)
  from this have 
    "[(d,x,b)\<leftarrow>do{d\<leftarrow>do{a\<leftarrow>\<down>\<Phi>;c\<leftarrow>\<down>\<Psi>;ret(a\<or>c)};x\<leftarrow>p;b\<leftarrow>\<down>\<Upsilon> x;
                                               ret(d,x,b)}] (d\<longrightarrow>b)"
    by (rule preOp)
  moreover have "(do{x\<leftarrow>\<down>\<Phi>; y\<leftarrow>\<down>\<Psi>; ret (x \<or> y)}) \<in> Dsef"
    proof -
      have "\<forall>x y. dsef (ret (x\<or>y::bool))"
	by (simp add: dsef_ret)
      from this have "\<forall>x y. (ret (x\<or>y::bool)) \<in> Dsef"
	by (simp add: Dsef_def)
      from Dsef_\<Phi> Dsef_\<Psi> this show ?thesis
	by (simp add: weak_Dsef2seq_exp)
    qed
  ultimately show ?thesis
    by (simp add: hoare_def condDisj_def)
qed
(* }}} *)

text{*
  Two Hoare-Triples with equal precondition and sequence but
  differnt postconditions @{text \<Psi>} and @{text \<Upsilon>} can be combined to one 
  Hoare-Triple with postcondition @{text "\<Psi> \<and> \<Upsilon>"}*}
lemma "conj":
  assumes a: "\<lbrace>\<Phi>\<rbrace>x\<leftarrow>p\<lbrace>\<Psi> x\<rbrace>" and b: "\<lbrace>\<Phi>\<rbrace>x\<leftarrow>p\<lbrace>\<Upsilon> x\<rbrace>"
  shows "\<lbrace>\<Phi>\<rbrace>x\<leftarrow>p\<lbrace>(\<Psi> x)\<and>\<^isub>D(\<Upsilon> x)\<rbrace>"
(* {{{ Proof }}} *)
(* Proof is equal to the sefj-proof*)
proof -
  (*<*)  
  have Dsef_\<Psi>: "\<forall>x. \<down>\<Psi> x \<in> Dsef"
    by (simp add: Rep_Dsef)    
  from this have dsef_\<Psi>: "\<forall>x. dsef (\<down>\<Psi> x)"
    by (simp add: Dsef_def)
  have Dsef_\<Upsilon>: "\<forall>x. \<down>\<Upsilon> x \<in> Dsef"
    by (simp add: Rep_Dsef)    
  from this have dsef_\<Upsilon>: "\<forall>x. dsef(\<down>\<Upsilon> x)"
    by (simp add: Dsef_def)
  (*>*)  
  
  have "[a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>(\<Psi> x);c\<leftarrow>\<down>(\<Upsilon> x)] (a\<longrightarrow>b)"
  (* {{{ Proof }}} *)
  proof -
    from a have "[a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>(\<Psi> x)] (a\<longrightarrow>b)"
      by (simp add: hoare_def)
    from this show ?thesis
      by (rule app_exp')
  qed
  (* }}} *)
  moreover have "[a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>(\<Psi> x);c\<leftarrow>\<down>(\<Upsilon> x)] (a\<longrightarrow>c)"
  (* {{{ Proof }}} *)
  proof -
    from b have "[a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;c\<leftarrow>\<down>(\<Upsilon> x)] (a\<longrightarrow>c)"
      by (simp add: hoare_def)
    from this have "[a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;c\<leftarrow>\<down>(\<Upsilon> x);b\<leftarrow>\<down>(\<Psi> x)] (a\<longrightarrow>c)"
      by (rule app_exp')
    from dsef_\<Psi> dsef_\<Upsilon> this show ?thesis
      apply (subst dsef_switch') .
  qed
  (* }}} *)
  ultimately 
  have c: "[a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>(\<Psi> x);c\<leftarrow>\<down>(\<Upsilon> x)] ((a\<longrightarrow>b) \<and> (a\<longrightarrow>c))"
    by (simp add: andI_exp)
  have "\<forall>a x b c. ((a\<longrightarrow>b) \<and> (a\<longrightarrow>c)) \<longrightarrow> (a\<longrightarrow>(b\<and>c))"
    by simp
  from this c have 
    "[a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>(\<Psi> x);c\<leftarrow>\<down>(\<Upsilon> x)] (a\<longrightarrow>(b\<and>c))"
    by (rule wk_exp)
  from this have 
    "[(a,x,b,c)\<leftarrow>do{a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<down>(\<Psi> x);c\<leftarrow>\<down>(\<Upsilon> x);
                                          ret(a,x,b,c)}](a\<longrightarrow>(b\<and>c))"
    by simp
  from this have 
    "[(a,x,d)\<leftarrow>do{a\<leftarrow>\<down>\<Phi>;x\<leftarrow>p;d\<leftarrow>do{b\<leftarrow>\<down>(\<Psi> x);c\<leftarrow>\<down>(\<Upsilon> x);ret(b\<and>c)};
                                          ret(a,x,d)}] (a\<longrightarrow>d)"
    by (rule postOp)
  moreover 
  have "\<forall>x. (do {b\<leftarrow>\<down>\<Psi> x; c\<leftarrow>\<down>\<Upsilon> x; ret (b \<and> c)}) \<in> Dsef"
    proof -
      have "\<forall>b c. dsef (ret(b\<and>c::bool))"
	by (simp add: dsef_ret)
      from this have "\<forall>b c. (ret(b\<and>c::bool)) \<in> Dsef"
	by (simp add: Dsef_def)
      from Dsef_\<Psi> Dsef_\<Upsilon> this show ?thesis
	by (simp add: weak_Dsef2seq_exp)
    qed
  from this 
  have 
    "\<forall>x. ((\<down>\<up>(do {b\<leftarrow>Rep_Dsef (\<Psi> x);c\<leftarrow>Rep_Dsef (\<Upsilon> x);ret (b \<and> c)}))
          = do {b\<leftarrow>Rep_Dsef (\<Psi> x); c\<leftarrow>Rep_Dsef (\<Upsilon> x); ret (b \<and> c)})"
    by simp
  ultimately show ?thesis
    by (simp add: hoare_def condConj_def)
qed    
(* }}} *)

lemma "if_True":
  assumes "\<lbrace>\<Phi>\<and>\<^isub>D\<Up>v\<rbrace> x\<leftarrow>p \<lbrace>\<Psi> x\<rbrace>"
  shows "\<lbrace>\<Phi>\<and>\<^isub>D\<Up>v\<rbrace> x\<leftarrow>(if v then p else q)\<lbrace>\<Psi> x\<rbrace>"
proof (cases v)
  case True
  from this prems show "\<lbrace>\<Phi>\<and>\<^isub>D \<Up>v\<rbrace>x\<leftarrow>if v then p else q\<lbrace>\<Psi> x\<rbrace>"
    by (simp add: hoare_def condConj_def)
next
  case False
  have Dsef_ret: "(ret False) \<in> Dsef"
    by (simp add: dsef_ret Dsef_def)
  have f1: "\<lbrace>\<Phi>\<and>\<^isub>D \<Up>v\<rbrace>\<lbrace>\<Up>False\<rbrace>"
    proof -
      have Dsef_\<Phi>: "\<down>\<Phi> \<in> Dsef"
	by (simp add: Rep_Dsef)    
      moreover
      from Dsef_ret have "(ret False) \<in> Dsef"
	by simp
      moreover have "\<forall>x y. ret (x \<and> y) \<in> Dsef"
	by (simp add: dsef_ret Dsef_def)
      ultimately have "do {x\<leftarrow>\<down>\<Phi>; y\<leftarrow>ret False; ret (x \<and> y)} \<in> Dsef"
	by (rule weak_Dsef2seq_exp)
      from prems this Dsef_ret show ?thesis
	by (simp add: hoare_Tupel_def condConj_def gdj_def)
    qed
  from Dsef_ret have "\<lbrace>\<Up>False\<rbrace>x\<leftarrow>if v then p else q\<lbrace>\<Psi> x\<rbrace>"
    by (simp add: hoare_def gdj_def)
  from this f1 show "\<lbrace>\<Phi>\<and>\<^isub>D \<Up>v\<rbrace>x\<leftarrow>if v then p else q\<lbrace>\<Psi> x\<rbrace>"
    by (rule wk_pre)
qed

lemma "if_False":
  assumes "\<lbrace>\<Phi>\<and>\<^isub>D\<Up>\<not>v\<rbrace> x\<leftarrow>q \<lbrace>\<Psi> x\<rbrace>"
  shows "\<lbrace>\<Phi>\<and>\<^isub>D\<Up>\<not>v\<rbrace> x\<leftarrow>(if v then p else q)\<lbrace>\<Psi> x\<rbrace>"
proof (cases v)
  case True
  have Dsef_ret: "(ret False) \<in> Dsef"
    by (simp add: dsef_ret Dsef_def)
  have f1: "\<lbrace>\<Phi>\<and>\<^isub>D \<Up>\<not>v\<rbrace>\<lbrace>\<Up>False\<rbrace>"
    proof -
      have Dsef_\<Phi>: "\<down>\<Phi> \<in> Dsef"
	by (simp add: Rep_Dsef)    
      moreover
      from Dsef_ret have "(ret False) \<in> Dsef"
	by simp
      moreover have "\<forall>x y. ret (x \<and> y) \<in> Dsef"
	by (simp add: dsef_ret Dsef_def)
      ultimately have "do {x\<leftarrow>\<down>\<Phi>; y\<leftarrow>ret False; ret (x \<and> y)} \<in> Dsef"
	by (rule weak_Dsef2seq_exp)
      from prems this Dsef_ret show ?thesis
	by (simp add: hoare_Tupel_def condConj_def gdj_def)
    qed
  from Dsef_ret have "\<lbrace>\<Up>False\<rbrace>x\<leftarrow>if v then p else q\<lbrace>\<Psi> x\<rbrace>"
    by (simp add: hoare_def gdj_def)
  from this f1 show "\<lbrace>\<Phi>\<and>\<^isub>D \<Up>\<not>v\<rbrace>x\<leftarrow>if v then p else q\<lbrace>\<Psi> x\<rbrace>"
    by (rule wk_pre)
next
  case False
  from this prems show "\<lbrace>\<Phi>\<and>\<^isub>D \<Up>\<not>v\<rbrace>x\<leftarrow>if v then p else q\<lbrace>\<Psi> x\<rbrace>"
    by (simp add: hoare_def condConj_def split_def)
qed

lemma if: 
  assumes a: "\<lbrace>\<Phi>\<and>\<^isub>D b\<rbrace> x\<leftarrow>p \<lbrace>\<Psi> x\<rbrace>" and b: "\<lbrace>\<Phi>\<and>\<^isub>D \<not>\<^isub>Db\<rbrace> y\<leftarrow>q \<lbrace>\<Psi> y\<rbrace>"
  shows "\<lbrace>\<Phi>\<rbrace> x\<leftarrow>(if\<^isub>D b then p else q)\<lbrace>\<Psi> x\<rbrace>"
proof -
  (*<*)  
  have Dsef_\<Phi>: "\<down>\<Phi> \<in> Dsef"
    by (simp add: Rep_Dsef)
  moreover have Dsef_b: "\<down>b \<in> Dsef"
    by (simp add: Rep_Dsef)
  moreover have Dsef_and: "\<forall>x y. ret (x \<and> y) \<in> Dsef"
    by (simp add: dsef_ret Dsef_def)
  ultimately have Dsef1: "do {x\<leftarrow>\<down>\<Phi>; y\<leftarrow>\<down>b; ret (x \<and> y)}\<in> Dsef"
    by (rule weak_Dsef2seq_exp)
  
  from Dsef_b have dsef_b: "dsef \<down>b"
    by (simp add: Dsef_def)
  from Dsef_\<Phi> have dsef_\<Phi>: "dsef \<down>\<Phi>"
    by (simp add: Dsef_def)
  
  have Dsef_ret: "\<forall>x. (ret (x::bool)) \<in> Dsef"
    by (simp add: dsef_ret Dsef_def)
  from Dsef_\<Phi> this Dsef_and have Dsef2:
    "\<forall>x. do {a\<leftarrow>\<down>\<Phi>; y\<leftarrow>ret x; ret (a \<and> y)} \<in> Dsef"
    apply (simp only: weak_Dsef2seq_exp)
    by simp
  have "\<forall>xa x y. dsef (ret (x \<and> y \<and> xa))"
    by (simp add: dsef_ret)
  from dsef_\<Phi> dsef_b this have Dsef3: "\<forall>xa. (do {x\<leftarrow>\<down>\<Phi>; y\<leftarrow>\<down>b; ret (x \<and> y \<and> xa)}) \<in> Dsef"
    apply auto
    by (simp add: weak_dsef2seq_exp Dsef_def)
  have "\<forall>x. ret(\<not> x) \<in> Dsef"
    by (simp add: dsef_ret Dsef_def)
  from Dsef_b and this have Dsef4: "do {x\<leftarrow>\<down>b; ret (\<not> x)} \<in> Dsef"
    by (simp add: weak_Dsef2seq)
  have "\<forall>x xa. ret (x \<and> \<not> xa) \<in> Dsef"
    by (simp add: dsef_ret Dsef_def)    
  from Dsef_\<Phi> Dsef_b this have Dsef5: "do {x\<leftarrow>\<down>\<Phi>; xa\<leftarrow>\<down>b; ret (x \<and> \<not> xa)} \<in> Dsef"
    by (simp add: weak_Dsef2seq_exp)
  have Dsef6: "do {x\<leftarrow>\<down>\<Phi>; y\<leftarrow>\<down>b; xa\<leftarrow>\<down>\<Phi>; xb\<leftarrow>\<down>b; ret (x \<and> y \<or> xa \<and> \<not> xb)} \<in> Dsef"
    proof -
      have "\<forall> x y xa xb. ret (x \<and> y \<or> xa \<and> \<not> xb) \<in> Dsef"
	by (simp add: dsef_ret Dsef_def)
      from Dsef_\<Phi> and Dsef_b and this have
	"\<forall>x y. do{xa\<leftarrow>\<down>\<Phi>; xb\<leftarrow>\<down>b; ret (x \<and> y \<or> xa \<and> \<not> xb)} \<in> Dsef"
	apply auto
	by (simp add: weak_Dsef2seq_exp)
      from Dsef_\<Phi> and Dsef_b and this show ?thesis
	by (simp add: weak_Dsef2seq_exp)
    qed
  have Dsef7: "\<forall>xa. do {x\<leftarrow>\<down>\<Phi>; xb\<leftarrow>\<down>b; ret (x \<and> \<not> xb \<and> \<not> xa)} \<in> Dsef"
    proof -
      have "\<forall>xa x xb. ret (x \<and> \<not> xb \<and> \<not> xa) \<in> Dsef"
	by (simp add: dsef_ret Dsef_def)
      from Dsef_\<Phi> Dsef_b this show ?thesis
	by (simp add: weak_Dsef2seq_exp)
    qed
  have Dsef8: "do {x\<leftarrow>\<down>\<Phi>; y\<leftarrow>\<down>b; ret (x \<and> y)} \<in> Dsef"
    proof -
      have "\<forall>x y. ret (x \<and> y) \<in> Dsef"
	by (simp add: dsef_ret Dsef_def)
      from Dsef_\<Phi> Dsef_b this show ?thesis
	by (simp add: weak_Dsef2seq_exp)
    qed
  from dsef_b have cp_b: "cp \<down>b"
    by (simp add: dsef_def)
  from dsef_\<Phi> have cp_\<Phi>: "cp \<down>\<Phi>"
    by (simp add: dsef_def)
  (*>*)  
  
  have "\<lbrace>\<Phi>\<and>\<^isub>D b\<rbrace> x\<leftarrow>(if\<^isub>D b then p else q)\<lbrace>\<Psi> x\<rbrace>"
    proof -
      have "\<lbrace>\<Phi>\<and>\<^isub>D b\<rbrace> v\<leftarrow>\<down>b\<lbrace>(\<Phi>\<and>\<^isub>Db)\<and>\<^isub>D \<Up>v\<rbrace>"
	proof -
	  from Dsef_ret Dsef_b Dsef_\<Phi> Dsef1 Dsef2 Dsef3 cp_b show ?thesis
	    apply (simp add: hoare_def condConj_def)
	    apply (simp add: cp_ret2seq)
	    apply (rule double2)
	    apply (simp add: Dsef_def)
	    apply (simp add: Dsef_def)
	    by (simp add: gdj_def Dsef_def)
	qed
      moreover from a have
	"\<forall>v. \<lbrace>(\<Phi>\<and>\<^isub>Db)\<and>\<^isub>D \<Up>v\<rbrace>x\<leftarrow>p\<lbrace>\<Psi> x\<rbrace>"
	proof -
	  from Dsef1 Dsef3 dsef_\<Phi> dsef_b have "\<forall>v. \<lbrace>(\<Phi>\<and>\<^isub>Db)\<and>\<^isub>D \<Up>v\<rbrace>\<lbrace>\<Phi>\<and>\<^isub>Db\<rbrace>"
	    apply (simp add: hoare_Tupel_def condConj_def dsef_ret Dsef_def)
	    apply auto
	    apply (rule double)
	    apply auto
	    by (simp add: gdj_def)
	  from a this have "\<forall>v. \<lbrace>(\<Phi>\<and>\<^isub>Db)\<and>\<^isub>D \<Up>v\<rbrace>x\<leftarrow>p\<lbrace>\<Psi> x\<rbrace>"
	    apply auto
	    apply (rule wk_pre)
	    apply simp
	    by simp
	  from this show ?thesis
	    by (simp add: hoare_def condConj_def)
	qed
      from this have "\<forall>v. \<lbrace>(\<Phi>\<and>\<^isub>Db)\<and>\<^isub>D \<Up>v\<rbrace>x\<leftarrow>if v then p else q\<lbrace>\<Psi> x\<rbrace>"
	by (simp add: if_True)
      ultimately have seq:
	"\<lbrace>\<Phi>\<and>\<^isub>D b\<rbrace> v\<leftarrow>\<down>b;x\<leftarrow>if v then p else q\<lbrace>\<Psi> x\<rbrace>"
	by (rule seq)
      from this have "\<lbrace>\<Phi>\<and>\<^isub>D b\<rbrace> x\<leftarrow>do{v\<leftarrow>\<down>b;if v then p else q}\<lbrace>\<Psi> x\<rbrace>"
	by (rule hoare_ctr)
      from this show ?thesis
	by (simp add: if\<^isub>D_def  if\<^isub>T_def) 
    qed
  moreover
  have "\<lbrace>\<Phi>\<and>\<^isub>D \<not>\<^isub>Db\<rbrace> x\<leftarrow>(if\<^isub>D b then p else q)\<lbrace>\<Psi> x\<rbrace>"
    proof -
      have "\<lbrace>\<Phi>\<and>\<^isub>D \<not>\<^isub>Db\<rbrace> v\<leftarrow>\<down>b\<lbrace>(\<Phi>\<and>\<^isub>D\<not>\<^isub>Db)\<and>\<^isub>D \<Up>\<not>v\<rbrace>"
	proof -
	  from Dsef_ret Dsef_b Dsef_\<Phi> Dsef4 Dsef5 Dsef6 Dsef7 cp_b show ?thesis
	    apply (simp add: hoare_def condConj_def condNot_def)
	    apply (simp add: cp_ret2seq)
	    apply (rule double2)
	    apply (simp add: Dsef_def)
	    apply (simp add: Dsef_def)
	    by (simp add: gdj_def Dsef_def)
	qed
      moreover have
	"\<forall>v. \<lbrace>(\<Phi>\<and>\<^isub>D \<not>\<^isub>Db)\<and>\<^isub>D \<Up>\<not>v\<rbrace>x\<leftarrow>q\<lbrace>\<Psi> x\<rbrace>"
	proof -
	  from Dsef2 Dsef2 Dsef3 Dsef4 Dsef5 Dsef6 Dsef7 Dsef8 dsef_\<Phi> dsef_b have 
	    "\<forall>v. \<lbrace>(\<Phi>\<and>\<^isub>D \<not>\<^isub>Db)\<and>\<^isub>D \<Up>\<not>v\<rbrace>\<lbrace>\<Phi>\<and>\<^isub>D\<not>\<^isub>Db\<rbrace>"
	    apply (simp add: hoare_Tupel_def condConj_def dsef_ret Dsef_def condNot_def)
	    apply auto
	    apply (rule double)
	    apply auto
	    by (simp add: gdj_def)
	  from b this have "\<forall>v. \<lbrace>(\<Phi>\<and>\<^isub>D\<not>\<^isub>Db)\<and>\<^isub>D \<Up>\<not>v\<rbrace>x\<leftarrow>q\<lbrace>\<Psi> x\<rbrace>"
	    apply auto
	    apply (rule wk_pre)
	    apply simp
	    by simp
	  from this show ?thesis
	    by (simp add: hoare_def condConj_def)
	qed
      from this have "\<forall>v. \<lbrace>(\<Phi>\<and>\<^isub>D\<not>\<^isub>Db)\<and>\<^isub>D \<Up>\<not>v\<rbrace>x\<leftarrow>if v then p else q\<lbrace>\<Psi> x\<rbrace>"
	by (simp add: if_False)
      ultimately have seq:
	"\<lbrace>\<Phi>\<and>\<^isub>D \<not>\<^isub>Db\<rbrace> v\<leftarrow>\<down>b;x\<leftarrow>if v then p else q\<lbrace>\<Psi> x\<rbrace>"
	by (rule seq)
      from this have "\<lbrace>\<Phi>\<and>\<^isub>D \<not>\<^isub>Db\<rbrace> x\<leftarrow>do{v\<leftarrow>\<down>b;if v then p else q}\<lbrace>\<Psi> x\<rbrace>"
	by (rule hoare_ctr)
      from this show ?thesis
	by (simp add: if\<^isub>D_def) 
    qed
  ultimately have
    "\<lbrace>(\<Phi>\<and>\<^isub>D b)\<or>\<^isub>D(\<Phi>\<and>\<^isub>D \<not>\<^isub>Db)\<rbrace> x\<leftarrow>(if\<^isub>D b then p else q)\<lbrace>\<Psi> x\<rbrace>"
    by (rule disj)
  moreover
  from Dsef1 Dsef3 Dsef4 Dsef5 Dsef6 cp_\<Phi> dsef_\<Phi> dsef_b have 
    "\<lbrace>\<Phi>\<rbrace>\<lbrace>(\<Phi>\<and>\<^isub>D b)\<or>\<^isub>D(\<Phi>\<and>\<^isub>D \<not>\<^isub>Db)\<rbrace>"
    apply (simp add: condConj_def condDisj_def condNot_def hoare_Tupel_def)
    apply (simp only: cp_ret2seq)
    apply (rule double)
    apply auto
    by (simp add: gdj_def)
  ultimately show ?thesis
    by (rule wk_pre)
qed    

text{*The rule for iter is not prooven yet. To demonstrate the use of 
  Hoare-Triples we axiomatize it because there are only a few 
  \quak{real} algorithms without iteration*}    
axioms 
  iter: "\<lbrace>(\<Phi> x) \<and>\<^isub>D (b x)\<rbrace> y\<leftarrow>(p x) \<lbrace>\<Phi> y\<rbrace> \<Longrightarrow>
         \<lbrace>\<Phi> x\<rbrace> y\<leftarrow>(iter\<^isub>D b p x)\<lbrace>(\<Phi> y) \<and>\<^isub>D (\<not>\<^isub>D(b y))\<rbrace>"

end