theory dsefCalc = dsefSyntax + gdjCalc:

lemma weak_cp2seq: 
  assumes dsef_r: "\<forall>x. dsef (r x)" and
          cp_p:"cp p" and sef_p: "sef p"
  shows "cp (do {x\<leftarrow>p; r x})"
proof -
  from dsef_r have cp_r:  "\<forall>x. cp (r x)"
    by (simp add: dsef_def)
  from dsef_r have com_r: "\<forall>x. (\<forall>q. (r x) comwith q)"
    by (simp add: dsef_def)
  from dsef_r have sef_r: "\<forall>x. (sef (r x))"
    by (simp add: dsef_def)     

  have "do {u\<leftarrow>do {x\<leftarrow>p; r x}; v\<leftarrow>do {y\<leftarrow>p; r y}; ret (u,v)} = 
    do {x\<leftarrow>p; z\<leftarrow>do{u\<leftarrow>r x;y\<leftarrow>p;ret(u,y)}; v\<leftarrow>r (snd z); ret ((fst z),v)}"
    by simp
  moreover
  from com_r sef_r cp_p sef_p have 
    "\<dots> = do {x\<leftarrow>p; z\<leftarrow>do{y\<leftarrow>p;u\<leftarrow>r x;ret(u,y)}; v\<leftarrow>r (snd z); ret ((fst z),v)}"
    by (simp add: switch3)
  moreover
  have
    "\<dots> = do {x\<leftarrow>p; y\<leftarrow>p; u\<leftarrow>r x; v\<leftarrow>r y; ret (u,v)}"
    by simp
  moreover from cp_p cp_r have 
    "\<dots> = do {u\<leftarrow>p; x\<leftarrow>r u; ret (x,x)}"
    by (simp only: cp_ret2seq)
  ultimately show ?thesis by (simp add: cp_def)
qed

lemma weak_com2seq:
  assumes dsef_r:"\<forall>x. dsef (r x)" and dsef_p:"dsef p"
  shows "\<forall>q::bool T. (cp q \<and> sef q) \<longrightarrow> cp (do {x\<leftarrow>do{x\<leftarrow>p;r x}; y\<leftarrow>q; ret(x,y)})"
proof -
  from dsef_r have cp_r: "\<forall>x. cp (r x)"
    by (simp add: dsef_def)
  from dsef_p have cp_p: "cp p"
    by (simp add: dsef_def)

  have 
    "\<forall>q::bool T. (cp q \<and> sef q) \<longrightarrow>
     do {u\<leftarrow>do{x\<leftarrow>do{x\<leftarrow>p;r x}; y\<leftarrow>q;ret(x,y)};
         v\<leftarrow>do{x\<leftarrow>do{x\<leftarrow>p;r x}; y\<leftarrow>q; ret(x,y)};ret(u,v)}=
     do {x\<^isub>1\<leftarrow>p;y\<^isub>1\<leftarrow>r x\<^isub>1;z\<^isub>1\<leftarrow>q;
         x\<^isub>2\<leftarrow>p;y\<^isub>2\<leftarrow>r x\<^isub>2;z\<^isub>2\<leftarrow>q;ret((y\<^isub>1,z\<^isub>1),(y\<^isub>2,z\<^isub>2))}"
    by simp
  from this have 
    "\<forall>q::bool T. (cp q \<and> sef q) \<longrightarrow>
     do {u\<leftarrow>do{x\<leftarrow>do{x\<leftarrow>p;r x}; y\<leftarrow>q;ret(x,y)};
         v\<leftarrow>do{x\<leftarrow>do{x\<leftarrow>p;r x}; y\<leftarrow>q; ret(x,y)};ret(u,v)}=
     do {x\<^isub>1\<leftarrow>p;y\<^isub>1\<leftarrow>r x\<^isub>1;u\<leftarrow>do{z\<^isub>1\<leftarrow>q;
         x\<^isub>2\<leftarrow>p;ret(z\<^isub>1,x\<^isub>2)};y\<^isub>2\<leftarrow>r (snd u);z\<^isub>2\<leftarrow>q;ret((y\<^isub>1,fst u),(y\<^isub>2,z\<^isub>2))}"
    by simp
  from this dsef_p have 
    "\<forall>q::bool T. (cp q \<and> sef q) \<longrightarrow>
     do {x\<^isub>1\<leftarrow>p;y\<^isub>1\<leftarrow>r x\<^isub>1;z\<^isub>1\<leftarrow>q;
         x\<^isub>2\<leftarrow>p;y\<^isub>2\<leftarrow>r x\<^isub>2;z\<^isub>2\<leftarrow>q;ret((y\<^isub>1,z\<^isub>1),(y\<^isub>2,z\<^isub>2))} =
     do {x\<^isub>1\<leftarrow>p;u\<leftarrow>do{y\<^isub>1\<leftarrow>r x\<^isub>1;
         x\<^isub>2\<leftarrow>p;ret(y\<^isub>1,x\<^isub>2)};z\<^isub>1\<leftarrow>q;y\<^isub>2\<leftarrow>r (snd u);z\<^isub>2\<leftarrow>q;ret((fst u,z\<^isub>1),(y\<^isub>2,z\<^isub>2))}"
    apply (unfold dsef_def)
    by (simp add: switch2)
  moreover from dsef_r dsef_p have 
    "\<forall>q::bool T. (cp q \<and> sef q) \<longrightarrow>
     do {x\<^isub>1\<leftarrow>p;u\<leftarrow>do{y\<^isub>1\<leftarrow>r x\<^isub>1;
         x\<^isub>2\<leftarrow>p;ret(y\<^isub>1,x\<^isub>2)};z\<^isub>1\<leftarrow>q;y\<^isub>2\<leftarrow>r (snd u);z\<^isub>2\<leftarrow>q;ret((fst u,z\<^isub>1),(y\<^isub>2,z\<^isub>2))}=
     do {x\<^isub>1\<leftarrow>p;x\<^isub>2\<leftarrow>p;do{y\<^isub>1\<leftarrow>r x\<^isub>1;z\<^isub>1\<leftarrow>q;y\<^isub>2\<leftarrow>r x\<^isub>2;z\<^isub>2\<leftarrow>q;ret((y\<^isub>1,z\<^isub>1),(y\<^isub>2,z\<^isub>2))}}"
    by (simp add: dsef_def switch2)
  ultimately have 
    "\<forall>q::bool T. (cp q \<and> sef q) \<longrightarrow>
     do {x\<^isub>1\<leftarrow>p;y\<^isub>1\<leftarrow>r x\<^isub>1;z\<^isub>1\<leftarrow>q;
         x\<^isub>2\<leftarrow>p;y\<^isub>2\<leftarrow>r x\<^isub>2;z\<^isub>2\<leftarrow>q;ret((y\<^isub>1,z\<^isub>1),(y\<^isub>2,z\<^isub>2))} =
     do {x\<^isub>1\<leftarrow>p;x\<^isub>2\<leftarrow>p;do{y\<^isub>1\<leftarrow>r x\<^isub>1;z\<^isub>1\<leftarrow>q;y\<^isub>2\<leftarrow>r x\<^isub>2;z\<^isub>2\<leftarrow>q;ret((y\<^isub>1,z\<^isub>1),(y\<^isub>2,z\<^isub>2))}}"
    by simp
  from this cp_p have 
    "\<forall>q::bool T. (cp q \<and> sef q) \<longrightarrow>
     do {x\<^isub>1\<leftarrow>p;y\<^isub>1\<leftarrow>r x\<^isub>1;z\<^isub>1\<leftarrow>q;
         x\<^isub>2\<leftarrow>p;y\<^isub>2\<leftarrow>r x\<^isub>2;z\<^isub>2\<leftarrow>q;ret((y\<^isub>1,z\<^isub>1),(y\<^isub>2,z\<^isub>2))} =
     do {x\<^isub>1\<leftarrow>p;y\<^isub>1\<leftarrow>r x\<^isub>1;u\<leftarrow>do{z\<^isub>1\<leftarrow>q;y\<^isub>2\<leftarrow>r x\<^isub>1;ret(z\<^isub>1,y\<^isub>2)};z\<^isub>2\<leftarrow>q;ret((y\<^isub>1,fst u),(snd u,z\<^isub>2))}"
    by (simp add: cp_ret2seq)
  moreover from dsef_r have 
    "\<forall>q::bool T. (cp q \<and> sef q) \<longrightarrow>
     do {x\<^isub>1\<leftarrow>p;y\<^isub>1\<leftarrow>r x\<^isub>1;u\<leftarrow>do{z\<^isub>1\<leftarrow>q;y\<^isub>2\<leftarrow>r x\<^isub>1;ret(z\<^isub>1,y\<^isub>2)};z\<^isub>2\<leftarrow>q;ret((y\<^isub>1,fst u),(snd u,z\<^isub>2))} =
     do {x\<^isub>1\<leftarrow>p;y\<^isub>1\<leftarrow>r x\<^isub>1;y\<^isub>2\<leftarrow>r x\<^isub>1;z\<^isub>1\<leftarrow>q;z\<^isub>2\<leftarrow>q;ret((y\<^isub>1,z\<^isub>1),(y\<^isub>2,z\<^isub>2))}"
    by (simp add: dsef_def switch2)
  ultimately have
    "\<forall>q::bool T. (cp q \<and> sef q) \<longrightarrow>
     do {x\<^isub>1\<leftarrow>p;y\<^isub>1\<leftarrow>r x\<^isub>1;z\<^isub>1\<leftarrow>q;
         x\<^isub>2\<leftarrow>p;y\<^isub>2\<leftarrow>r x\<^isub>2;z\<^isub>2\<leftarrow>q;ret((y\<^isub>1,z\<^isub>1),(y\<^isub>2,z\<^isub>2))} =
     do {x\<^isub>1\<leftarrow>p;y\<^isub>1\<leftarrow>r x\<^isub>1;y\<^isub>2\<leftarrow>r x\<^isub>1;z\<^isub>1\<leftarrow>q;z\<^isub>2\<leftarrow>q;ret((y\<^isub>1,z\<^isub>1),(y\<^isub>2,z\<^isub>2))}"
    by simp
  from this cp_r have 
    "\<forall>q::bool T. (cp q \<and> sef q) \<longrightarrow>
     do {x\<^isub>1\<leftarrow>p;y\<^isub>1\<leftarrow>r x\<^isub>1;z\<^isub>1\<leftarrow>q;
         x\<^isub>2\<leftarrow>p;y\<^isub>2\<leftarrow>r x\<^isub>2;z\<^isub>2\<leftarrow>q;ret((y\<^isub>1,z\<^isub>1),(y\<^isub>2,z\<^isub>2))} =
     do {x\<^isub>1\<leftarrow>p;y\<^isub>1\<leftarrow>r x\<^isub>1;z\<^isub>1\<leftarrow>q;ret((y\<^isub>1,z\<^isub>1),(y\<^isub>1,z\<^isub>1))}"
    by (simp add: cp_ret2seq)
  from this show ?thesis
    by (simp add: cp_def)
qed

lemma dsef_ret: "dsef (ret x)"
(* {{{ Proof }}} *) 
proof (unfold dsef_def)
  have "cp (ret x)" by (simp add: cp_def)
  moreover have "sef (ret x)" 
    by (simp add: sef_def com_def del:delBind)
  moreover have 
    "(\<forall>q. (cp q) \<and> (sef q) \<longrightarrow> 
          (cp (do{x\<leftarrow>ret x; y\<leftarrow>q; ret (x, y)})))"
    by (simp add: weak_cp2retSeq)
  from this have "\<forall>q. ((ret x) comwith q)"
    by (simp add: com_def)
  ultimately show 
    "(sef (ret x)) \<and> (cp (ret x)) \<and> (\<forall>q. ((ret x) comwith q))"
    by blast
qed
(* }}} *)

lemma sef_rm2of3:
  assumes "sef \<Phi>"
  shows "[a\<leftarrow>\<Phi>';b\<leftarrow>\<Phi>;c\<leftarrow>\<Psi> a](\<xi> a c) \<Longrightarrow> [a\<leftarrow>\<Phi>';c\<leftarrow>\<Psi> a](\<xi> a c)"
proof -
  assume "[a\<leftarrow>\<Phi>';b\<leftarrow>\<Phi>;c\<leftarrow>\<Psi> a](\<xi> a c)"
  from this have
    "[u\<leftarrow>do{a\<leftarrow>\<Phi>';b\<leftarrow>\<Phi>;c\<leftarrow>\<Psi> a;ret(a,b,c)}](\<xi> (fst u) (snd(snd u)))"
    by (simp add: gdj_def)
  from this have
    "do{u\<leftarrow>do{a\<leftarrow>\<Phi>';b\<leftarrow>\<Phi>;c\<leftarrow>\<Psi> a;ret(a,b,c)};
               ret(\<xi> (fst u) (snd(snd u)),
               (fst u),(snd(snd u)))} =
     do{u\<leftarrow>do{a\<leftarrow>\<Phi>';b\<leftarrow>\<Phi>;c\<leftarrow>\<Psi> a;ret(a,b,c)};
               ret(True,
               (fst u),(snd(snd u)))}"
    by (rule gdj2doSeq)
  from this have 
    "do{a\<leftarrow>\<Phi>';b\<leftarrow>\<Phi>;c\<leftarrow>\<Psi> a;ret(\<xi> a c,a,c)} =
     do{a\<leftarrow>\<Phi>';b\<leftarrow>\<Phi>;c\<leftarrow>\<Psi> a;ret(True,a,c)}"
    by (simp add: gdj_def)
  from this have
    "do{a\<leftarrow>\<Phi>';c\<leftarrow>do{b\<leftarrow>\<Phi>;\<Psi> a};ret(\<xi> a c,a,c)} =
     do{a\<leftarrow>\<Phi>';c\<leftarrow>do{b\<leftarrow>\<Phi>;\<Psi> a};ret(True,a,c)}"
    by simp
  moreover from prems have "sef \<Phi>"
    by simp
  ultimately have
    "do{a\<leftarrow>\<Phi>';c\<leftarrow>\<Psi> a;ret(\<xi> a c,a,c)} =
     do{a\<leftarrow>\<Phi>';c\<leftarrow>\<Psi> a;ret(True,a,c)}"
    by (simp add: seFree)
  from this
  show ?thesis
    by (simp add: gdj_def)
qed
(* }}} *)

lemma sef_rm2of4:
  assumes "sef \<Phi>"
  shows "[a\<leftarrow>\<Phi>';b\<leftarrow>\<Phi>;x\<leftarrow>p;c\<leftarrow>\<Psi> x](\<xi> a x c) \<Longrightarrow> 
         [a\<leftarrow>\<Phi>';x\<leftarrow>p;c\<leftarrow>\<Psi> x](\<xi> a x c)"
(* {{{ Proof }}} *) 
proof -
  assume "[a\<leftarrow>\<Phi>';b\<leftarrow>\<Phi>;x\<leftarrow>p;c\<leftarrow>\<Psi> x](\<xi> a x c)"
  from this have 
    "[a\<leftarrow>\<Phi>';b\<leftarrow>\<Phi>;u\<prec>-(x,c)\<leftarrow>do{x\<leftarrow>p;c\<leftarrow>\<Psi> x;ret(x,c)}](\<xi> a x c)"
    by simp
  from prems this
  have "[a\<leftarrow>\<Phi>';u\<prec>-(x,c)\<leftarrow>do{x\<leftarrow>p;c\<leftarrow>\<Psi> x;ret(x,c)}](\<xi> a x c)"
    by (simp only: sef_rm2of3) 
  moreover
  from this have "[a\<leftarrow>\<Phi>';x\<leftarrow>p;c\<leftarrow>\<Psi> x](\<xi> a x c)"
    by (simp add: ctr_cut2)
  ultimately show ?thesis
    by simp
qed
(* }}} *)

lemma sef_rm3of4:
  assumes "\<forall>x. sef (\<Psi> x)"
  shows "[a\<leftarrow>\<Phi>';x\<leftarrow>p;c\<leftarrow>\<Psi> x;d\<leftarrow>\<Psi>' x](\<xi> a x d) \<Longrightarrow> 
         [a\<leftarrow>\<Phi>';x\<leftarrow>p;d\<leftarrow>\<Psi>' x](\<xi> a x d)"
(* {{{ Proof }}} *) 
proof -
  assume "[a\<leftarrow>\<Phi>';x\<leftarrow>p;c\<leftarrow>\<Psi> x;d\<leftarrow>\<Psi>' x](\<xi> a x d)"
  from this have
    "[u\<leftarrow>do{a\<leftarrow>\<Phi>';x\<leftarrow>p;c\<leftarrow>\<Psi> x;d\<leftarrow>\<Psi>' x;ret(a,x,c,d)}]
                       (\<xi> (fst u) (fst(snd u)) (snd(snd(snd u))))"
    by (simp add: gdj_def)
  from this have 
    "do{u\<leftarrow>do{a\<leftarrow>\<Phi>';x\<leftarrow>p;c\<leftarrow>\<Psi> x;d\<leftarrow>\<Psi>' x;ret(a,x,c,d)};
               ret(\<xi> (fst u) (fst(snd u)) (snd(snd(snd u))),
               (fst u),(fst(snd u)),(snd(snd(snd u))))} =
     do{u\<leftarrow>do{a\<leftarrow>\<Phi>';x\<leftarrow>p;c\<leftarrow>\<Psi> x;d\<leftarrow>\<Psi>' x;ret(a,x,c,d)};
               ret(True,
               (fst u),(fst(snd u)),(snd(snd(snd u))))}"
    by (rule gdj2doSeq)
  from this have 
    "do{a\<leftarrow>\<Phi>';x\<leftarrow>p;c\<leftarrow>\<Psi> x;d\<leftarrow>\<Psi>' x; ret(\<xi> a x d,a,x, d)} =
     do{a\<leftarrow>\<Phi>';x\<leftarrow>p;c\<leftarrow>\<Psi> x;d\<leftarrow>\<Psi>' x; ret(True,a,x, d)}"
    by (simp add: gdj_def)
  from this have
    "do{a\<leftarrow>\<Phi>';x\<leftarrow>p;d\<leftarrow>do{c\<leftarrow>\<Psi> x;\<Psi>' x}; ret(\<xi> a x d,a,x, d)} =
     do{a\<leftarrow>\<Phi>';x\<leftarrow>p;d\<leftarrow>do{c\<leftarrow>\<Psi> x;\<Psi>' x}; ret(True,a,x, d)}"
    by simp
  moreover from prems have "\<forall>x. sef (\<Psi> x)"
    by simp
  ultimately
  have 
    "do{a\<leftarrow>\<Phi>';x\<leftarrow>p;d\<leftarrow>\<Psi>' x; ret(\<xi> a x d,a,x, d)} =
     do{a\<leftarrow>\<Phi>';x\<leftarrow>p;d\<leftarrow>\<Psi>' x; ret(True,a,x, d)}"
    by (simp add: seFree)
  from this show ?thesis
    by (simp add: gdj_def)
qed
(* }}} *)

lemma sef_rm3of5: 
  assumes "\<forall>x. sef (\<Psi> x)"
  shows "[a\<leftarrow>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<Psi> x;y\<leftarrow>q x;c\<leftarrow>\<Upsilon> x y]\<xi> a x c y \<Longrightarrow> 
         [a\<leftarrow>\<Phi>;x\<leftarrow>p;y\<leftarrow>q x;c\<leftarrow>\<Upsilon> x y]\<xi> a x c y"
proof -
  assume "[a\<leftarrow>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<Psi> x;y\<leftarrow>q x;c\<leftarrow>\<Upsilon> x y]\<xi> a x c y"
  from this 
  have 
    "[a\<leftarrow>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<Psi> x;u\<leftarrow>do{y\<leftarrow>q x;c\<leftarrow>\<Upsilon> x y;ret(y,c)}]\<xi> a x (snd u) (fst u)"
    by (simp add: gdj_def)
  moreover from this prems have 
    "[a\<leftarrow>\<Phi>;x\<leftarrow>p;u\<leftarrow>do{y\<leftarrow>q x;c\<leftarrow>\<Upsilon> x y;ret(y,c)}]\<xi> a x (snd u) (fst u)"
    by (simp only: sef_rm3of4)
  moreover from this have 
    "[a\<leftarrow>\<Phi>;x\<leftarrow>p;y\<leftarrow>q x;c\<leftarrow>\<Upsilon> x y]\<xi> a x c y"
    by (simp add: gdj_def)
  ultimately show ?thesis
    by (simp add: gdj_def)
qed

lemma dsef_switch:
  assumes dsef_a: "dsef a" and dsef_b: "dsef b"
  shows "([x\<leftarrow>a;y\<leftarrow>b;z\<leftarrow>p;v\<leftarrow>r z] \<Phi> x y z v) = 
         ([y\<leftarrow>b;x\<leftarrow>a;z\<leftarrow>p;v\<leftarrow>r z] \<Phi> x y z v)"
(* {{{ Proof }}} *) 
proof
  assume "([x\<leftarrow>a;y\<leftarrow>b;z\<leftarrow>p;v\<leftarrow>r z] \<Phi> x y z v)"
  from this have 
    "([(x,y)\<leftarrow>do{x\<leftarrow>a;y\<leftarrow>b;ret(x,y)};z\<leftarrow>p;v\<leftarrow>r z] \<Phi> x y z v)"
    by simp
  from dsef_a dsef_b this have 
    "([(x,y)\<leftarrow>do{y\<leftarrow>b;x\<leftarrow>a;ret(x,y)};z\<leftarrow>p;v\<leftarrow>r z] \<Phi> x y z v)"
    by (simp add: dsef_def switch)
  from this have 
    "[u\<leftarrow>do{(x,y)\<leftarrow>do{y\<leftarrow>b;x\<leftarrow>a;ret(x,y)};z\<leftarrow>p;v\<leftarrow>r z;ret(x,y,z,v)}] 
       \<Phi> (fst u) (fst(snd u)) (fst(snd(snd u))) (snd(snd(snd u)))"
    by (simp add: gdj_def)
  from this have 
   "do{u\<leftarrow>do{(x,y)\<leftarrow>do{y\<leftarrow>b;x\<leftarrow>a;ret(x,y)};z\<leftarrow>p;v\<leftarrow>r z;ret(x,y,z,v)};
             ret(\<Phi> (fst u) (fst(snd u)) (fst(snd(snd u))) 
                 (snd(snd(snd u))),
                 (fst(snd u)),(fst u),(fst(snd(snd u))),
                 (snd(snd(snd u))))} =
   do{u\<leftarrow>do{(x,y)\<leftarrow>do{y\<leftarrow>b;x\<leftarrow>a;ret(x,y)};z\<leftarrow>p;v\<leftarrow>r z;ret(x,y,z,v)};
             ret(True     ,
                 (fst(snd u)),(fst u),(fst(snd(snd u))),
                 (snd(snd(snd u))))}"
    by (rule gdj2doSeq)
  from this have 
    "do{(x,y)\<leftarrow>do{y\<leftarrow>b;x\<leftarrow>a;ret(x,y)};z\<leftarrow>p;v\<leftarrow>r z;
                             ret(\<Phi> x y z v,y,x,z,v)} =
     do{(x,y)\<leftarrow>do{y\<leftarrow>b;x\<leftarrow>a;ret(x,y)};z\<leftarrow>p;v\<leftarrow>r z;
                             ret(True     ,y,x,z,v)}"
    by simp
  from this show "([y\<leftarrow>b;x\<leftarrow>a;z\<leftarrow>p;v\<leftarrow>r z] \<Phi> x y z v)"
    by (simp add: gdj_def)
next
  assume "([y\<leftarrow>b;x\<leftarrow>a;z\<leftarrow>p;v\<leftarrow>r z] \<Phi> x y z v)"
  from this have 
    "([(y,x)\<leftarrow>do{y\<leftarrow>b;x\<leftarrow>a;ret(y,x)};z\<leftarrow>p;v\<leftarrow>r z] \<Phi> x y z v)"
    by simp
  from dsef_a dsef_b this have 
    "([(y,x)\<leftarrow>do{x\<leftarrow>a;y\<leftarrow>b;ret(y,x)};z\<leftarrow>p;v\<leftarrow>r z] \<Phi> x y z v)"
    by (simp add: dsef_def switch)
  from this have 
    "[u\<leftarrow>do{(y,x)\<leftarrow>do{x\<leftarrow>a;y\<leftarrow>b;ret(y,x)};z\<leftarrow>p;v\<leftarrow>r z;ret(y,x,z,v)}] 
       \<Phi> (fst(snd u)) (fst u) (fst(snd(snd u))) (snd(snd(snd u)))"
    by (simp add: gdj_def)
  from this have 
   "do{u\<leftarrow>do{(y,x)\<leftarrow>do{x\<leftarrow>a;y\<leftarrow>b;ret(y,x)};z\<leftarrow>p;v\<leftarrow>r z;ret(y,x,z,v)};
              ret(\<Phi> (fst(snd u)) (fst u) (fst(snd(snd u))) 
              (snd(snd(snd u))),(fst(snd u)),(fst u),
              (fst(snd(snd u))),(snd(snd(snd u))))} =
    do{u\<leftarrow>do{(y,x)\<leftarrow>do{x\<leftarrow>a;y\<leftarrow>b;ret(y,x)};z\<leftarrow>p;v\<leftarrow>r z;ret(y,x,z,v)};
              ret(True     ,
              (fst(snd u)),(fst u),(fst(snd(snd u))),
              (snd(snd(snd u))))}"
    by (rule gdj2doSeq)
  from this have 
    "do{x\<leftarrow>a;y\<leftarrow>b;z\<leftarrow>p;v\<leftarrow>r z;ret(\<Phi> x y z v,x,y,z,v)} =
     do{x\<leftarrow>a;y\<leftarrow>b;z\<leftarrow>p;v\<leftarrow>r z;ret(True,x,y,z,v)}"
    by simp
  from this show "([x\<leftarrow>a;y\<leftarrow>b;z\<leftarrow>p;v\<leftarrow>r z] \<Phi> x y z v)"
    by (simp add: gdj_def)
qed
(* }}} *)

lemma dsef_switch':
  assumes dsef_a: "\<forall>y. dsef (a y)" and dsef_b: "\<forall>y. dsef (b y)"
  shows "[x\<leftarrow>p;y\<leftarrow>q;z\<leftarrow>a y;v\<leftarrow>b y] \<Phi> x y z v = 
         [x\<leftarrow>p;y\<leftarrow>q;v\<leftarrow>b y;z\<leftarrow>a y] \<Phi> x y z v"
(* {{{ Proof }}} *) 
proof 
  assume "[x\<leftarrow>p;y\<leftarrow>q;z\<leftarrow>a y;v\<leftarrow>b y] \<Phi> x y z v"
  from this have 
    "[x\<leftarrow>p;y\<leftarrow>q;(z,v)\<leftarrow>do{z\<leftarrow>a y;v\<leftarrow>b y;ret(z,v)}] \<Phi> x y z v"
    by simp
  from dsef_a dsef_b this have 
    "[x\<leftarrow>p;y\<leftarrow>q;(z,v)\<leftarrow>do{v\<leftarrow>b y;z\<leftarrow>a y;ret(z,v)}] \<Phi> x y z v"
    by (simp add: dsef_def switch') 
  from this have 
    "[u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q;(z,v)\<leftarrow>do{v\<leftarrow>b y;z\<leftarrow>a y;ret(z,v)};ret(x,y,z,v)}]
      \<Phi> (fst u) (fst(snd u)) (fst(snd(snd u))) (snd(snd(snd u))) "
    by (simp add: gdj_def)
  from this have 
    "do {u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q;(z,v)\<leftarrow>do{v\<leftarrow>b y;z\<leftarrow>a y;ret(z,v)};
            ret(x,y,z,v)};
            ret(\<Phi> (fst u) (fst(snd u)) (fst(snd(snd u))) 
               (snd(snd(snd u))),(fst u),(fst(snd u)),
               (snd(snd(snd u))),(fst(snd(snd u))))} =
    do {u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q;(z,v)\<leftarrow>do{v\<leftarrow>b y;z\<leftarrow>a y;ret(z,v)};
            ret(x,y,z,v)};
            ret(True,
               (fst u),(fst(snd u)),(snd(snd(snd u))),
               (fst(snd(snd u))))}"
    by (rule gdj2doSeq)
  from this show "[x\<leftarrow>p;y\<leftarrow>q;v\<leftarrow>b y;z\<leftarrow>a y] \<Phi> x y z v"
    by (simp add: gdj_def)
next  
  assume "[x\<leftarrow>p;y\<leftarrow>q;v\<leftarrow>b y;z\<leftarrow>a y] \<Phi> x y z v"
  from this have 
    "[x\<leftarrow>p;y\<leftarrow>q;(v,z)\<leftarrow>do{v\<leftarrow>b y;z\<leftarrow>a y;ret(v,z)}] \<Phi> x y z v"
    by simp
  from dsef_a dsef_b this have 
    "[x\<leftarrow>p;y\<leftarrow>q;(v,z)\<leftarrow>do{z\<leftarrow>a y;v\<leftarrow>b y;ret(v,z)}] \<Phi> x y z v"
    by (simp add: dsef_def switch')
  from this have 
    "[u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q;(v,z)\<leftarrow>do{z\<leftarrow>a y;v\<leftarrow>b y;ret(v,z)};ret(x,y,v,z)}]
       \<Phi> (fst u) (fst(snd u)) (snd(snd(snd u))) (fst(snd(snd u)))"
    by (simp add: gdj_def)
  from this have 
    "do {u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q;(v,z)\<leftarrow>do{z\<leftarrow>a y;v\<leftarrow>b y;ret(v,z)};
            ret(x,y,v,z)};
            ret(\<Phi> (fst u) (fst(snd u)) (snd(snd(snd u))) 
                (fst(snd(snd u))),(fst u),(fst(snd u)),
                (snd(snd(snd u))),(fst(snd(snd u))))} =
     do {u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q;(v,z)\<leftarrow>do{z\<leftarrow>a y;v\<leftarrow>b y;ret(v,z)};
            ret(x,y,v,z)};
            ret(True,
                (fst u),(fst(snd u)),(snd(snd(snd u))),
                (fst(snd(snd u))))}"
    by (rule gdj2doSeq)
  from this show "[x\<leftarrow>p;y\<leftarrow>q;z\<leftarrow>a y;v\<leftarrow>b y] \<Phi> x y z v"
    by (simp add: gdj_def)
qed
(* }}} *)

lemma weak_dsef2seq: 
  assumes dsef_p: "dsef p" and dsef_r: "\<forall>x. dsef (r x)"
  shows "dsef (do{x\<leftarrow>p;r x})"
(* {{{ Proof }}} *) 
proof -
  (*<*)
  from dsef_p have sef_p: "sef p"
    by (simp add: dsef_def)
  from dsef_r have sef_r: "\<forall>x. sef (r x)"
    by (simp add: dsef_def)
  (*>*)

  from dsef_r dsef_p have cp_do: "cp (do{x\<leftarrow>p;r x})"
    by (simp add: dsef_def weak_cp2seq)
  from sef_p sef_r have sef_do: "sef (do{x\<leftarrow>p;r x})"
    by (simp add: sef_def)
  have com_do:
    "\<forall>q::bool T. ((cp q \<and> sef q) \<longrightarrow> do{x\<leftarrow>p;r x} comwith q)"
    proof -
      from dsef_r dsef_p have com_do:
	"\<forall>q::bool T. ((cp q \<and> sef q) \<longrightarrow> cp (do{x\<leftarrow>do{x\<leftarrow>p;r x}; y\<leftarrow>q; ret (x, y)}))"
	by (rule weak_com2seq)
      from this show ?thesis
	by (simp add: com_def)
    qed
  from cp_do sef_do com_do show "dsef (do{x\<leftarrow>p;r x})"
    by (simp add: dsef_def com_def)
qed
(* }}} *)

lemma weak_dsef2seq_exp:
  assumes dsef_p: "dsef p" and 
          dsef_q: "dsef q" and 
          dsef_r: "\<forall>x y. dsef (r x y)"
  shows "dsef (do{x\<leftarrow>p;y\<leftarrow>q;r x y})"
(* {{{ Proof }}} *) 
proof -
  from dsef_q dsef_r have 
    "\<forall>x. (\<forall>y. dsef (r x y) \<longrightarrow> dsef(do{y\<leftarrow>q;r x y}))"
    by (simp add: weak_dsef2seq)
  from dsef_r this have "\<forall>x. dsef(do{y\<leftarrow>q;r x y})"
    by simp
  from dsef_p this show ?thesis
    by (simp add: weak_dsef2seq)
qed
(* }}} *)

lemma weak_Dsef2seq: 
  assumes Dsef_p: "p \<in> Dsef" and Dsef_r: "\<forall>x. (r x) \<in> Dsef"
  shows "(do{x\<leftarrow>p;r x}) \<in> Dsef"
(* {{{ Proof }}} *)
proof -
  from Dsef_p have dsef_p: "dsef p"
    by (simp add: Dsef_def)
  from Dsef_r have dsef_r: "\<forall>x. dsef (r x)"
    by (simp add: Dsef_def)
  from dsef_p dsef_r have "dsef (do{x\<leftarrow>p;r x})"
    by (simp add: weak_dsef2seq)
  from this show ?thesis
    by (simp add: Dsef_def)
qed
(* }}} *)

lemma weak_Dsef2seq_exp:
  assumes Dsef_p: "p \<in> Dsef" and 
          Dsef_q: "q \<in> Dsef" and 
          Dsef_r: "\<forall>x y. (r x y) \<in> Dsef"
  shows "(do{x\<leftarrow>p;y\<leftarrow>q;r x y}) \<in> Dsef"
(* {{{ Proof }}} *)
proof -
  from Dsef_p have dsef_p: "dsef p"
    by (simp add: Dsef_def)
  from Dsef_q have dsef_q: "dsef q"
    by (simp add: Dsef_def)
  from Dsef_r have dsef_r: "\<forall>x y. dsef (r x y)"
    by (simp add: Dsef_def)
  from dsef_p dsef_q dsef_r have "dsef (do{x\<leftarrow>p;y\<leftarrow>q;r x y})"
    by (simp add: weak_dsef2seq_exp)
  from this show ?thesis
    by (simp add: Dsef_def)
qed
(* }}} *)

lemma double:
  assumes dsef_\<Phi>: "dsef \<Phi>" and dsef_\<Psi>: "dsef \<Psi>" and
          a: "[(a,b)\<leftarrow>do{a\<leftarrow>\<Phi>;b\<leftarrow>\<Psi>;ret(Q a b,P a b a b)}](a\<longrightarrow>b)"
  shows "[(a,b)\<leftarrow>do{a\<leftarrow>\<Phi>;b\<leftarrow>\<Psi>;c\<leftarrow>\<Phi>;d\<leftarrow>\<Psi>;ret(Q a b,P a b c d)}](a\<longrightarrow>b)"
proof -
  have "\<forall>a b. dsef (ret(a,b))"
    by (simp add: dsef_ret)
  from dsef_\<Phi>  dsef_\<Psi> this have "dsef (do{a\<leftarrow>\<Phi>;b\<leftarrow>\<Psi>;ret(a,b)})"
    by (rule weak_dsef2seq_exp)
  from this have "cp (do{a\<leftarrow>\<Phi>;b\<leftarrow>\<Psi>;ret(a,b)})"
    by (simp add: dsef_def)
  moreover
  from a have 
    "[(a,b)\<leftarrow>do{u\<leftarrow>do{a\<leftarrow>\<Phi>;b\<leftarrow>\<Psi>;ret(a,b)};
          ret(Q (fst u) (snd u),P (fst u) (snd u) (fst u) (snd u))}](a\<longrightarrow>b)"
    by (simp add: gdj_def)
  ultimately have
    "[(a,b)\<leftarrow>do{u\<leftarrow>do{a\<leftarrow>\<Phi>;b\<leftarrow>\<Psi>;ret(a,b)};v\<leftarrow>do{a\<leftarrow>\<Phi>;b\<leftarrow>\<Psi>;ret(a,b)};
          ret(Q (fst u) (snd u),P (fst u) (snd u) (fst v) (snd v))}](a\<longrightarrow>b)"
    by (simp only: cp_ret2seq)
  from this show ?thesis
    by simp
qed

lemma double2:
  assumes dsef_\<Phi>: "dsef \<Phi>" and dsef_\<Psi>: "dsef \<Psi>" and
          a: "[(a,b,b)\<leftarrow>do{a\<leftarrow>\<Phi>;b\<leftarrow>\<Psi>;ret(Q a b,b,P a b a b)}](a\<longrightarrow>b)"
  shows "[(a,b,b)\<leftarrow>do{a\<leftarrow>\<Phi>;b\<leftarrow>\<Psi>;c\<leftarrow>\<Phi>;d\<leftarrow>\<Psi>;ret(Q a b,b,P a b c d)}](a\<longrightarrow>b)"
proof -
  have "\<forall>a b. dsef (ret(a,b))"
    by (simp add: dsef_ret)
  from dsef_\<Phi>  dsef_\<Psi> this have "dsef (do{a\<leftarrow>\<Phi>;b\<leftarrow>\<Psi>;ret(a,b)})"
    by (rule weak_dsef2seq_exp)
  from this have "cp (do{a\<leftarrow>\<Phi>;b\<leftarrow>\<Psi>;ret(a,b)})"
    by (simp add: dsef_def)
  moreover
  from a have 
    "[(a,x,b)\<leftarrow>do{u\<leftarrow>do{a\<leftarrow>\<Phi>;b\<leftarrow>\<Psi>;ret(a,b)};
          ret(Q (fst u) (snd u),(snd u),P (fst u) (snd u) (fst u) (snd u))}](a\<longrightarrow>b)"
    by (simp add: gdj_def)
  ultimately have
    "[(a,x,b)\<leftarrow>do{u\<leftarrow>do{a\<leftarrow>\<Phi>;b\<leftarrow>\<Psi>;ret(a,b)};v\<leftarrow>do{a\<leftarrow>\<Phi>;b\<leftarrow>\<Psi>;ret(a,b)};
          ret(Q (fst u) (snd u),(snd u),P (fst u) (snd u) (fst v) (snd v))}](a\<longrightarrow>b)"
    by (simp only: cp_ret2seq)
  from this show ?thesis
    by simp
qed

end