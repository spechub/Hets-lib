theory gdjKleeneCalc imports gdjKleeneSyntax Lemmabase begin

lemma gdj2doSeq: 
  assumes "[x\<leftarrow>p] \<Phi> x" 
  shows "do {x\<leftarrow>p;q x (\<Phi> x)} = do {x\<leftarrow>p;q x \<top>}" 
(* {{{ Proof }}} *)
proof -
  from prems 
  have "do {x\<leftarrow>p;ret (\<Phi> x, x)} = do{x\<leftarrow>p;ret(\<top>, x)}"
    by (fold gdj_def)
  from this 
  have 
    "do{x\<leftarrow>p;y\<leftarrow>ret (\<Phi> x);ret (y, x)} = 
     do{x\<leftarrow>p;y\<leftarrow>ret \<top>;ret(y, x)}"
    by (simp only: fstUnitLaw)
  from this 
  have "do {x\<leftarrow>p;y\<leftarrow>ret (\<Phi> x);q x y} = do{x\<leftarrow>p;y\<leftarrow>ret \<top>;q x y}"
    by (rule  ret2seqSw)
  from this show ?thesis
    by (simp only: fstUnitLaw)
qed (* }}} *)

lemma gdjEq2doSeq:
  assumes a: "[x\<leftarrow>p] ((q1 x)=(q2 x))"
  shows "do {x\<leftarrow>p;r x (q1 x)} = do {x\<leftarrow>p;r x (q2 x)}"
(* {{{ Proof }}} *)
proof -
  have "do {x\<leftarrow>p;r x (q1 x)} = do {x\<leftarrow>p;r x ((q1 x) res \<top>)}"
    by (simp add: res_def)
  moreover 
  from prems have "\<dots> = do {x\<leftarrow>p;r x ((q1 x) res ((q1 x)=(q2 x)))}"
    apply (subst gdj2doSeq) back
    apply simp
    apply (rule sym)
    apply (subst gdj2doSeq)
    apply (assumption)
    by blast
  moreover
  have "\<dots> = do {x\<leftarrow>p;r x ((q2 x) res ((q1 x)=(q2 x)))}"
    proof -
      have 
	"\<forall>x. ((q1 x) res ((q1 x)=(q2 x)) = 
	     ((q2 x) res ((q1 x)=(q2 x))))"
	by (rule eq_res)
      from this show ?thesis
	by simp
    qed
  moreover 
  from prems have "\<dots> = do {x\<leftarrow>p;r x (q2 x)}"
    apply (unfold res_def)
    apply (subst gdj2doSeq)
    apply simp
    apply (unfold if_def)
    by simp
  ultimately show ?thesis
    by simp
qed (* }}} *)


lemma doSeq2gdjEq:
  assumes "do{x\<leftarrow>p;ret(x,(a\<^isub>1 x)::'a)} = do{x\<leftarrow>p;ret(x,(a\<^isub>2 x)::'a)}"
  shows "[x\<leftarrow>p](a\<^isub>1 x=a\<^isub>2 x)"
(* {{{ Proof }}} *)
proof -
  from prems have 
    "do{x\<leftarrow>p;y\<leftarrow>ret (a\<^isub>1 x); ret(x,y)} = 
     do{x\<leftarrow>p;y\<leftarrow>ret (a\<^isub>2 x); ret(x,y)}"
    by simp
  from this have 
    "do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>ret (a\<^isub>1 x); ret(x,y)};ret u} = 
     do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>ret (a\<^isub>2 x); ret(x,y)};ret u}"
    by simp
  from this have
    "do{(x,y)\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>ret (a\<^isub>1 x); ret(x,y)};
                  ret (y=(a\<^isub>2 x), x)} = 
     do{(x,y)\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>ret (a\<^isub>2 x); ret(x,y)};
                  ret (y=(a\<^isub>2 x), x)}"
    by (rule ret2seq)
  from this show ?thesis
    by (simp add: gdj_def)
qed (* }}} *)

lemma sef2cp:
  assumes "sef p"
  shows "cp p = [x\<leftarrow>p;y\<leftarrow>p](x=y)"
(* {{{ Proof }}} *)
proof
  assume "cp p"
  from this have "(do{x\<leftarrow>p;y\<leftarrow>p;ret(x,y)} = do{x\<leftarrow>p;ret(x,x)})"
    by (simp add: cp_def)
  from this prems have 
    "(do{x\<leftarrow>p;y\<leftarrow>p;ret(x,y)} = do{x\<leftarrow>p;y\<leftarrow>p;ret(x,x)})"
    by (simp add: "seFree")
  from this have 
    "(do{(x,y)\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>p;ret(x,y)};ret ((x,y),x)} = 
    do{(x,y)\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>p;ret(x,y)};ret ((x,y),y)})"
    by simp
  from this have "[z\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>p;ret(x,y)}](fst z=snd z)"
    by (simp add: doSeq2gdjEq)
  from this show "[x\<leftarrow>p;y\<leftarrow>p](x=y)"
    by (simp add: gdj_def)
next
  assume "[x\<leftarrow>p;y\<leftarrow>p](x=y)"
  from this have "[z\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>p;ret(x,y)}](fst z=snd z)"
    by (simp add: gdj_def)
  from this have 
    "(do{z\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>p;ret(x,y)};ret(fst z, (fst z))} = 
    do{z\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>p;ret(x,y)};ret (fst z, (snd z))})"
    by (rule gdjEq2doSeq)
  from this have "(do{x\<leftarrow>p;y\<leftarrow>p;ret(x,y)} = do{x\<leftarrow>p;y\<leftarrow>p;ret(x,x)})"
    by simp
  from this prems have 
    "(do{x\<leftarrow>p;y\<leftarrow>p;ret(x,y)} = do{x\<leftarrow>p;ret(x,x)})"
    by (simp add: "seFree")
  from this show "cp p"
    by (simp add: cp_def)
qed (* }}} *)

lemma "cpsefProps(ii\<rightarrow>iv)":
  assumes cp_p:  "cp p" and sef_p: "sef p" and 
          ii: "(do{x\<leftarrow>p;y\<leftarrow>q;ret(x,y)} = do{y\<leftarrow>q;x\<leftarrow>p;ret(x,y)})"
  shows "[x\<leftarrow>p;y\<leftarrow>q;z\<leftarrow>p](x=z)"
(* {{{ Proof }}} *)
proof -
  from prems have t: "[(x, z)\<leftarrow>do {x\<leftarrow>p; z\<leftarrow>p; ret (x, z)}](x = z)"
    by (simp add: sef2cp)
  from this have "[u\<leftarrow>do{x\<leftarrow>p;z\<leftarrow>p;ret(x,z)}] (fst u=snd u)"
    by (simp add: gdj_def)
  from this have
    "do {u\<leftarrow>do{x\<leftarrow>p; z\<leftarrow>p; ret(x,z)};
         v\<leftarrow>q;
         ret ((fst u)=(snd u),fst u,snd u,v)} = 
     do {u\<leftarrow>do{x\<leftarrow>p; z\<leftarrow>p; ret(x,z)};
         v\<leftarrow>q;
         ret (\<top>,fst u,snd u,v)}"
    by (rule gdj2doSeq)
  from this have
    "do {x\<leftarrow>p;z\<leftarrow>p;v\<leftarrow>q;ret (x=z,x,z,v)} = 
     do {x\<leftarrow>p;z\<leftarrow>p;v\<leftarrow>q;ret (\<top>,x,z,v)}"
    by simp
  from this 
  have "[(x,z,y)\<leftarrow>do{x\<leftarrow>p; z\<leftarrow>p; y\<leftarrow>q;ret(x,z,y)}](x = z)"
    by (simp add: gdj_def)
  from this have 
      "[(x,z,y)\<leftarrow>do{x\<leftarrow>p; (z,y)\<leftarrow>do{z\<leftarrow>p;y\<leftarrow>q;ret(z,y)}; ret(x,z,y)}]
                                                          (x = z)"
    by simp 
  moreover 
  from ii have "do{z\<leftarrow>p;y\<leftarrow>q;ret(z,y)} = do{y\<leftarrow>q;z\<leftarrow>p;ret(z,y)}"
    by simp
  ultimately have 
    "[(x,z,y)\<leftarrow>do{x\<leftarrow>p; (z,y)\<leftarrow>do{y\<leftarrow>q;z\<leftarrow>p;ret(z,y)};ret(x,z,y)}]
                                                          (x = z)"
    by simp
  from this have 
    "[u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q;z\<leftarrow>p;ret(x,z,y)}]((fst u) = (fst(snd u)))"
    by (simp add: gdj_def)
  from this have 
    "(do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q;z\<leftarrow>p;ret(x,z,y)};
         ret((fst u)=fst(snd u),fst u,snd(snd u),fst(snd u))}) = 
     (do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q;z\<leftarrow>p;ret(x,z,y)};
         ret(True,fst u,snd(snd u),fst(snd u))})"
    by (rule gdj2doSeq)
  from this show ?thesis
    by (simp add: gdj_def)
qed (* }}} *)

lemma "cpsefProps(iv\<rightarrow>iii)": 
  assumes sef_p: "sef p" and iv: "[x\<leftarrow>p;y\<leftarrow>q;z\<leftarrow>p](x=z)"
  shows "do{x\<leftarrow>p;y\<leftarrow>q;r x y} = do{y\<leftarrow>q;x\<leftarrow>p;r x y}"
(* {{{ Proof }}} *)
proof -
  from sef_p have "do{x\<leftarrow>p;y\<leftarrow>q;r x y} = do{x\<leftarrow>p;y\<leftarrow>q;z\<leftarrow>p;r x y}"
    by (simp add: seFree)
  moreover have
    "\<dots> = do{x\<leftarrow>p;y\<leftarrow>q;z\<leftarrow>p;r z y}"
    proof -
      from iv have 
	"[u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q;z\<leftarrow>p;ret(x,y,z)}](fst u=snd(snd u))"
	by (simp add: gdj_def)
      from this have 
	"do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q;z\<leftarrow>p;ret(x,y,z)};
	              r (fst u) (fst(snd u))} =
	 do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q;z\<leftarrow>p;ret(x,y,z)};
	              r (snd(snd u)) (fst(snd u))}"
	by (rule gdjEq2doSeq)
      from this show ?thesis
	by simp
    qed
  moreover from prems have 
    "\<dots> =  do{y\<leftarrow>q;z\<leftarrow>p;r z y}"
    by (simp add: seFree)
  ultimately show ?thesis
    by simp
qed (* }}} *)

axioms seq2ret:
  "do{x\<leftarrow>p;y\<leftarrow>q;r x y} = do{y\<leftarrow>q;x\<leftarrow>p;r x y} \<Longrightarrow> do{y\<leftarrow>q;x\<leftarrow>p;ret(x,y)} = do{x\<leftarrow>p;y\<leftarrow>q;ret(x,y)}"

lemma "cpsefProps(iii\<rightarrow>i)": 
  assumes sef_p: "sef p" and sef_q: "\<forall>x. sef q" and 
          cp_p: "cp p" and cp_q: "cp q" and 
          iii: "do{x\<leftarrow>p;y\<leftarrow>q;r x y} = do{y\<leftarrow>q;x\<leftarrow>p;r x y}"
  shows "cp(do{x\<leftarrow>p;y\<leftarrow>q;ret(x,y)})"
(* {{{ Proof }}} *)
proof -
  let ?s = "do{x\<leftarrow>p;y\<leftarrow>q;ret(x,y)}"

  have "do{w\<leftarrow>?s;z\<leftarrow>?s;ret (w,z)} = do{u\<leftarrow>p;w\<leftarrow>do{v\<leftarrow>q;x\<leftarrow>p;ret(v,x)};y\<leftarrow>q;ret((u,fst w),(snd w,y))}"
    by simp
  moreover from prems have "\<dots> = do{u\<leftarrow>p;w\<leftarrow>do{x\<leftarrow>p;v\<leftarrow>q;ret(v,x)};y\<leftarrow>q;ret((u,fst w),(snd w,y))}"
    apply (subst seq2ret)
    apply auto
    apply (rule seq2ret)
    by simp
  moreover have "\<dots> = do{u\<leftarrow>p;x\<leftarrow>p;do{v\<leftarrow>q;y\<leftarrow>q;ret((u,v),(x,y))}}"
    by simp
  moreover from cp_p have "\<dots> = do{u\<leftarrow>p;do{v\<leftarrow>q;y\<leftarrow>q;ret((u,v),(u,y))}}"
    by (simp only: cp_ret2seq)
  moreover from cp_q have "\<dots> = do{u\<leftarrow>p;do{v\<leftarrow>q;ret((u,v),(u,v))}}"
    by (simp only: cp_ret2seq)
  ultimately have "do{w\<leftarrow>?s;z\<leftarrow>?s;ret (w,z)} = do{u\<leftarrow>p;do{v\<leftarrow>q;ret((u,v),(u,v))}}"
    by simp
  moreover have "\<dots> = do{w\<leftarrow>?s;ret(w,w)}"
    by simp
  ultimately have "do{w\<leftarrow>?s;z\<leftarrow>?s;ret (w,z)} = do{w\<leftarrow>?s;ret(w,w)}"
    by (rule trans)
  from this show ?thesis
    by (simp only: cp_def)
qed (* }}} *)

lemma switch:
  assumes com_a: "\<forall>q. a comwith q" and
          sef_a: "sef a" and
          cp_b:"cp b" and sef_b: "sef b"
  shows "do{x\<leftarrow>a;y\<leftarrow>b;ret(x,y)} = do{y\<leftarrow>b;x\<leftarrow>a;ret(x,y)}"
(* {{{ Proof }}} *) 
proof -
  from com_a sef_a have 
    "(\<forall>q::'b T. (cp q) \<and> (sef q) \<longrightarrow> 
                  cp (do {x\<leftarrow>a; y\<leftarrow>q; ret (x, y)}))"
    apply (unfold com_def)
    by (rule com_def commute_tcoerc)
  from com_a sef_b cp_b this have cp_do: 
    "cp(do {x\<leftarrow>a; y\<leftarrow>b; ret(x,y)})"
    by (simp add: com_def)
  from sef_a sef_b cp_do show ?thesis 
    by (rule "cpsefProps(i\<rightarrow>ii)")
qed (* }}} *)

lemma switch2:
  assumes  com_b: "\<forall>q::bool T. b comwith q" and 
           sef_b: "sef b"  and 
           cp_a:  "cp a" and sef_a: "sef a"
  shows "do{x\<leftarrow>a;y\<leftarrow>b;ret(x,y)} = do{y\<leftarrow>b;x\<leftarrow>a;ret(x,y)}"
(* {{{ Proof }}} *) 
proof -
  from prems have "do{y\<leftarrow>b;x\<leftarrow>a;ret(y,x)}=do{x\<leftarrow>a;y\<leftarrow>b;ret(y,x)} "
    by (rule switch)
  from this have "do{y\<leftarrow>b;x\<leftarrow>a;ret(x,y)}=do{x\<leftarrow>a;y\<leftarrow>b;ret(x,y)}"
    by (rule ret2seqSw')
  from this show ?thesis
    by simp
qed (* }}} *)

lemma switch':
  assumes com_a: "\<forall>z. (\<forall>q::bool T. (a z) comwith q)" and 
          sef_a: "\<forall>z. sef (a z)"  and 
          cp_b:  "\<forall>z. cp (b z)" and 
          sef_b: "\<forall>z. sef (b z)"
  shows "\<forall>z. do{x\<leftarrow>a z;y\<leftarrow>b z;ret(x,y)} = 
             do{y\<leftarrow>b z;x\<leftarrow>a z;ret(x,y)}"
(* {{{ Proof }}} *) 
proof -
  from com_a have 
    "\<forall>z. (\<forall>q::bool T. (cp q) \<and> (sef q) \<longrightarrow> 
                      cp (do {x\<leftarrow>(a z); y\<leftarrow>q; ret (x, y)}))"
    by (simp add: com_def)
  from this have 
    "\<forall>z. (\<forall>q::'c T. (cp q) \<and> (sef q) \<longrightarrow> 
              cp (do {x\<leftarrow>(a z); y\<leftarrow>q; ret (x, y)}))"
    by (rule tst)
  from com_a sef_b cp_b this have cp_do:  
    "\<forall>z. cp(do {x\<leftarrow>(a z); y\<leftarrow>(b z); ret(x,y)})"
    by (simp add: com_def)
  have all: 
      "\<forall>z. ((sef (a z)) \<and> (sef (b z)) \<and> 
            cp(do {x\<leftarrow>(a z); y\<leftarrow>(b z); ret(x,y)})) \<Longrightarrow>
       \<forall>z. (do {x\<leftarrow>(a z); y\<leftarrow>(b z); ret (x, y)} = 
            do {y\<leftarrow>(b z); x\<leftarrow>(a z); ret (x, y)})"
    apply (rule allI)
    apply (rule "cpsefProps(i\<rightarrow>ii)")
    by simp_all
  from sef_a sef_b cp_do have 
    "\<forall>z. ((sef (a z)) \<and> (sef (b z)) \<and> 
          cp(do {x\<leftarrow>(a z); y\<leftarrow>(b z); ret(x,y)}))"
    by simp
  from all this show ?thesis
    by simp
qed (* }}} *)

lemma switch3: 
  assumes com_a: "\<forall>z q. (a z) comwith q" and 
          sef_a: "\<forall>z. sef (a z)" and 
          cp_b:  "cp b" and 
          sef_b: "sef b"
  shows "\<forall>z. do {x\<leftarrow>a z; y\<leftarrow>b; ret (x, y)} = do {y\<leftarrow>b; x\<leftarrow>a z; ret (x, y)}"
(* {{{ Proof }}} *)
proof (rule switch')
  from prems show "\<forall>z q. a z comwith q"
    by simp
  from prems show "\<forall>z. sef a z"
    by simp
  from prems show "\<forall>z. cp b"
    by simp
  from prems show "\<forall>z. sef b"
    by simp
qed (* }}} *)

text{* example:
  assumes @{text "[a\<leftarrow>\<Phi>;x\<leftarrow>p;b\<leftarrow>\<Psi> x;c\<leftarrow>\<Upsilon> x] (a\<longrightarrow>(r b c))"}
  shows @{text "[a\<leftarrow>\<Phi>;x\<leftarrow>p;d\<leftarrow>do{b\<leftarrow>\<Psi> x;c\<leftarrow>\<Upsilon> x;ret(r b c)}] (a\<longrightarrow>d)"}
*}
lemma postOp:
  assumes "[x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>s x y z] \<Phi> x y (t z v)"
  shows "[x\<leftarrow>p;y\<leftarrow>q x;d\<leftarrow>do{z\<leftarrow>r x y;v\<leftarrow>s x y z;ret(t z v)}] \<Phi> x y d"
(* {{{ Proof }}} *)
proof -
  from prems have 
    "do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>s x y z;ret(x,y,z,v)};
        z\<leftarrow>ret(\<Phi> (fst u) (fst(snd u)) 
             (t (fst(snd(snd u))) (snd(snd(snd u)))));
        ret(z,u)}=
    do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>s x y z;ret(x,y,z,v)};
        z\<leftarrow>ret(\<top>);
        ret(z,u)}"
    by (simp add: gdj_def)
  from this have 
    "do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>s x y z;ret(x,y,z,v)};
        z\<leftarrow>ret(\<Phi> (fst u) (fst(snd u)) 
              (t (fst(snd(snd u))) (snd(snd(snd u)))));
        ret(z,(fst u),(fst(snd u)),
              (t (fst(snd(snd u))) (snd(snd(snd u)))))}=
     do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>s x y z;ret(x,y,z,v)};
        z\<leftarrow>ret(\<top>);
        ret(z,(fst u),(fst(snd u)),
              (t (fst(snd(snd u))) (snd(snd(snd u)))))}"
    by (rule ret2seqSw)
  from this show ?thesis
    by (simp add: gdj_def)
qed (* }}} *)

text{* expample:
  assumes @{text "[a\<leftarrow>\<Phi>;b\<leftarrow>\<Psi>;x\<leftarrow>p;c\<leftarrow>\<Upsilon> x] ((r a b)\<longrightarrow>c)"}
  shows @{text "[d\<leftarrow>do{a\<leftarrow>\<Phi>;b\<leftarrow>\<Psi>;ret(r a b)};x\<leftarrow>p;c\<leftarrow>\<Upsilon> x] (d\<longrightarrow>c)"}
*}
lemma preOp:
  assumes "[x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r;v\<leftarrow>s z] \<Phi> (t x y) z v"
  shows "[d\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;ret(t x y)};z\<leftarrow>r;v\<leftarrow>s z] \<Phi> d z v"
(* {{{ Proof }}} *)
proof - 
    from prems have 
      "do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r;v\<leftarrow>s z;ret(x,y,z,v)};
          z\<leftarrow>ret(\<Phi> (t (fst u) (fst(snd u))) 
                (fst(snd(snd u))) (snd(snd(snd u))));
          ret(z,u)}=
       do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r;v\<leftarrow>s z;ret(x,y,z,v)};
          z\<leftarrow>ret(\<top>);
          ret(z,u)}"
      by (simp add: gdj_def)
    from this have 
      "do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r;v\<leftarrow>s z;ret(x,y,z,v)};
          z\<leftarrow>ret(\<Phi> (t (fst u) (fst(snd u))) 
               (fst(snd(snd u))) (snd(snd(snd u))));
          ret(z,(t (fst u) (fst(snd u))),
               (fst(snd(snd u))),(snd(snd(snd u))))}=
       do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r;v\<leftarrow>s z;ret(x,y,z,v)};
          z\<leftarrow>ret(\<top>);
          ret(z,(t (fst u) (fst(snd u))),
               (fst(snd(snd u))),(snd(snd(snd u))))}"
      by (rule ret2seqSw)
  from this show ?thesis
    by (simp add: gdj_def)
qed (* }}} *)

(*<*)lemma "-*": "[x\<leftarrow>p](\<xi> x) = [x\<leftarrow>p;y\<leftarrow>ret ()](\<xi> x)"
(* {{{ Proof }}} *)
proof
  assume "[x\<leftarrow>p](\<xi> x)"
  from this
  have 
    "do {x\<leftarrow>p; do{ret (); ret (\<xi> x, x, ())}} = 
     do {x\<leftarrow>p; do{ret (); ret (True, x, ())}}"
    by (rule gdj2doSeq)
  from this show "[x\<leftarrow>p;y\<leftarrow>ret ()](\<xi> x)"
    by (simp add: gdj_def)
next
  assume "[x\<leftarrow>p;y\<leftarrow>ret ()](\<xi> x)"
  from this have 
    "do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>ret();ret(x,y)};v\<leftarrow>ret(\<xi> (fst u));ret(v,u)} = 
     do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>ret();ret(x,y)};v\<leftarrow>ret(\<top>);ret(v,u)}"
    by (simp add: gdj_def)
  from this have 
    "do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>ret();ret(x,y)};v\<leftarrow>ret(\<xi> (fst u));ret(v,fst u)}=
     do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>ret();ret(x,y)};v\<leftarrow>ret(\<top>);ret(v, fst u)}"
    by (rule ret2seqSw)
  moreover
  have "sef (ret ())"
    by (simp add: sef_def)
  ultimately 
  show "[x\<leftarrow>p](\<xi> x)"
    by (simp add: seFree gdj_def)
qed (* }}} *)

lemma "-**": "[x\<leftarrow>p;y\<leftarrow>q x](\<xi> x y) = [x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>ret ()](\<xi> x y)"
(* {{{ Proof }}} *)
proof 
  assume "[x\<leftarrow>p;y\<leftarrow>q x](\<xi> x y)"
  from this have
    "do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;ret(x,y)};
             v\<leftarrow>ret(\<xi> (fst u) (snd u));
             ret(v,u)} = 
     do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;ret(x,y)};
             v\<leftarrow>ret(\<top>);
             ret(v,u)}"
    by (simp add: gdj_def)
  from this have
    "do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;ret(x,y)};
             v\<leftarrow>ret(\<xi> (fst u) (snd u));
             do{z\<leftarrow>ret ();ret(v,fst u,snd u,z)}} = 
     do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;ret(x,y)};
             v\<leftarrow>ret(\<top>);
             do{z\<leftarrow>ret();ret(v,fst u, snd u,z)}}"
    by (rule ret2seqSw)
  from this show "[x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>ret ()](\<xi> x y)"
    by (simp add: gdj_def) 
next
  assume "[x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>ret ()](\<xi> x y)"
  from this have 
    "do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>ret();ret(x,y,z)};
             v\<leftarrow>ret(\<xi> (fst u) (fst (snd u)));
             ret(v,u)} = 
     do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>ret();ret(x,y,z)};
             v\<leftarrow>ret(\<top>);
             ret(v,u)}"
    by (simp add: gdj_def)
  from this have 
    "do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>ret();ret(x,y,z)};
             v\<leftarrow>ret(\<xi> (fst u) (fst (snd u)));
             ret(v,fst u,fst (snd u))} = 
     do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>ret();ret(x,y,z)};
             v\<leftarrow>ret(\<top>);
             ret(v,fst u,fst (snd u))}"
    by (rule ret2seqSw)
  moreover have "sef ret()"
    by (simp add: sef_def)
  ultimately
  have
    "do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;ret(x,y)};v\<leftarrow>ret(\<xi>(fst u)(snd u));ret(v,u)} 
   = do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;ret(x,y)};v\<leftarrow>ret(\<top>);ret(v,u)}"
    by (simp add: seFree)
  from this
  show "[x\<leftarrow>p;y\<leftarrow>q x](\<xi> x y)"
    by (simp add: gdj_def)
qed (* }}} *)

lemma "-***": "[x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y](\<xi> x y z) = 
              [x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>ret ()](\<xi> x y z)"
(* {{{ Proof }}} *)
proof
  assume "[x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y](\<xi> x y z)"
  from this have
    "do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;ret(x,y,z)};
             w\<leftarrow>ret(\<xi> (fst u) (fst (snd u)) (snd (snd u)));
             ret(w,u)} = 
     do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;ret(x,y,z)};
             w\<leftarrow>ret(\<top>);
             ret(w,u)}"
    by (simp add: gdj_def)
  from this have
    "do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;ret(x,y,z)};
             w\<leftarrow>ret(\<xi> (fst u) (fst(snd u)) (snd(snd u)));
             do{v\<leftarrow>ret ();ret(w,fst u,fst(snd u),snd(snd u),v)}} =
     do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;ret(x,y,z)};
             w\<leftarrow>ret(\<top>);
             do{v\<leftarrow>ret();ret(w,fst u,fst(snd u),snd(snd u),v)}}"
    by (rule ret2seqSw)
  from this show "[x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>ret ()](\<xi> x y z)"
    by (simp add: gdj_def) 
next
  assume "[x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>ret ()](\<xi> x y z)"
  from this have 
    "do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>ret();ret(x,y,z,v)};
             w\<leftarrow>ret(\<xi> (fst u) (fst (snd u)) (fst(snd(snd u))));
             ret(w,u)} = 
     do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>ret();ret(x,y,z,v)};
             w\<leftarrow>ret(\<top>);
             ret(w,u)}"
    by (simp add: gdj_def)
  from this have 
    "do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>ret();ret(x,y,z,v)};
             w\<leftarrow>ret(\<xi> (fst u) (fst (snd u)) (fst(snd(snd u))));
             ret(w,fst u,fst (snd u),fst(snd(snd u)))} = 
     do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>ret();ret(x,y,z,v)};
             w\<leftarrow>ret(\<top>);
             ret(w,fst u,fst (snd u),fst(snd(snd u)))}"
    by (rule ret2seqSw)
  moreover have "sef ret()"
    by (simp add: sef_def)
  ultimately
  have
    "do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;ret(x,y,z)};
             v\<leftarrow>ret(\<xi> (fst u) (fst(snd u))(snd(snd u)));
             ret(v,u)} = 
     do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;ret(x,y,z)};
             v\<leftarrow>ret(\<top>);
             ret(v,u)}"
    by (simp add: seFree)
  from this
  show "[x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y](\<xi> x y z)"
    by (simp add: gdj_def)
qed (* }}} *)(*>*)

lemma pre: 
  assumes "\<forall>x. ([y\<leftarrow>q x] \<Phi> x y)"
  shows "[x\<leftarrow>p;y\<leftarrow>q x] \<Phi> x y"
(* {{{ Proof }}} *)
proof -
  have 
    "\<forall>x. ([y\<leftarrow>q x] \<Phi> x y) \<Longrightarrow> 
     \<forall>x. (do {y\<leftarrow>q x;ret (\<Phi> x y,x,y)} = do {y\<leftarrow>q x;ret (\<top>,x,y)})"
    apply (rule allI)
    apply (rule gdj2doSeq)
    by simp
  from this prems have 
    "(\<lambda>x. do {y\<leftarrow>q x;ret (\<Phi> x y,x,y)}) = 
     (\<lambda>x. do {y\<leftarrow>q x;ret (\<top>,x,y)})"
    by simp
  from this show ?thesis
    by (simp add: gdj_def)
qed (* }}} *)

lemma "pre_exp": 
  assumes "\<forall>u v. ([x\<leftarrow>p u v] \<Phi> u v x)"
  shows "[u\<leftarrow>r;v\<leftarrow>s u;x\<leftarrow>p u v] \<Phi> u v x"
(* {{{ Proof }}} *)
proof -
  from prems have "\<forall>u. ([v\<leftarrow>s u;x\<leftarrow>p u v] \<Phi> u v x)"
    by (simp add: pre)
  from this have "\<forall>u. ([w\<leftarrow>do{(v,x)\<leftarrow>do{v\<leftarrow>s u;x\<leftarrow>p u v;ret(v,x)};ret(v,x)}] \<Phi> u v x)"
    by simp
  from this have 
    "([u\<leftarrow>r;w\<leftarrow>(v,x)\<leftarrow>do{v\<leftarrow>s u;x\<leftarrow>p u v;ret(v,x)}] \<Phi> u v x)"
    by (rule pre)
  from this show ?thesis
    by simp
qed (* }}} *)

(*<*)(* {{{ Help-Lemmata }}} *)
lemma "*-": 
  shows "[x\<leftarrow>p](\<xi> x) = [y\<leftarrow>ret();x\<leftarrow>p](\<xi> x)"
(* {{{ Proof }}} *)
proof
  assume "[x\<leftarrow>p](\<xi> x)"
  from this have "\<forall>y. ([x\<leftarrow>p] \<xi> x) "
    by simp
  from this show "[y\<leftarrow>ret(); x\<leftarrow>p](\<xi> x)"
    by (rule pre)
next
  assume "[y\<leftarrow>ret();x\<leftarrow>p]\<xi> x"
  from this have 
    "do{u\<leftarrow>do{y\<leftarrow>ret();x\<leftarrow>p;ret(y,x)};v\<leftarrow>ret(\<xi> (snd u));ret(v,u)} =
     do{u\<leftarrow>do{y\<leftarrow>ret();x\<leftarrow>p;ret(y,x)};v\<leftarrow>ret(\<top>);ret(v,u)}"
    by (simp add: gdj_def)
  from this have 
    "do{u\<leftarrow>do{y\<leftarrow>ret();x\<leftarrow>p;ret(y,x)};v\<leftarrow>ret(\<xi> (snd u));ret(v,snd u)} 
   = do{u\<leftarrow>do{y\<leftarrow>ret();x\<leftarrow>p;ret(y,x)};v\<leftarrow>ret(\<top>);ret(v,snd u)}"
    by (rule ret2seqSw)
  moreover 
  have "sef (ret())"
    by (simp add: sef_def)
  ultimately
  show "[x\<leftarrow>p]\<xi> x"
    by (simp add: seFree gdj_def)
qed (* }}} *)

lemma "**-": 
  shows "[x\<leftarrow>p; y\<leftarrow>q x] \<Phi> x y = [z\<leftarrow>ret();x\<leftarrow>p; y\<leftarrow>q x] \<Phi> x y"
(* {{{ Proof }}} *)
proof -
  have "[(x,y)\<leftarrow>do{x\<leftarrow>p; y\<leftarrow>q x;ret (x,y)}] \<Phi> x y = 
       [z\<leftarrow>ret();u\<prec>-(x,y)\<leftarrow>do{x\<leftarrow>p; y\<leftarrow>q x;ret(x,y)}] \<Phi> x y"
    by (rule "*-")
  from this show ?thesis
    by simp
qed (* }}} *)

lemma "***-": 
  shows "[x\<leftarrow>p; y\<leftarrow>q x;z\<leftarrow>r x y] \<Phi> x y z = 
         [v\<leftarrow>ret();x\<leftarrow>p; y\<leftarrow>q x;z\<leftarrow>r x y] \<Phi> x y z"
(* {{{ Proof }}} *)
proof -
  have "[x\<leftarrow>p; u\<prec>-(y,z)\<leftarrow>do{y\<leftarrow>q x;z\<leftarrow>r x y;ret (y,z)}] \<Phi> x y z = 
       [v\<leftarrow>ret();x\<leftarrow>p;u\<prec>-(y,z)\<leftarrow>do{y\<leftarrow>q x;z\<leftarrow>r x y;ret(y,z)}] \<Phi> x y z"
    by (rule "**-")
  from this show ?thesis
    by simp
qed (* }}} *) (* }}} *)(*>*)

lemma sef\<^isub>0: 
  assumes a: "[x\<leftarrow>p;y\<leftarrow>q x] \<Phi> x" and b: "\<forall>x. sef (q x)"
  shows   "[x\<leftarrow>p] \<Phi> x"
(* {{{ Proof }}} *)
proof -
  from prems have "[u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;ret(x,y)}] \<Phi> (fst u)"
    by (simp add: gdj_def)
  from this 
  have "do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;ret(x,y)};ret(\<Phi> (fst u),(fst u))} = 
        do{u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;ret(x,y)};ret(\<top>,(fst u))}"
    by (rule gdj2doSeq)
  from b this have 
    "do{x\<leftarrow>p;y\<leftarrow>ret(\<Phi> x,x);ret y} = do{x\<leftarrow>p;y\<leftarrow>ret(\<top>,x);ret y}"
    by (simp add: seFree)
  from this show ?thesis
    by (simp add: gdj_def)
qed (* }}} *)

lemma andI: 
  assumes a:"[x\<leftarrow>p] \<Phi> x" and b:"[x\<leftarrow>p] \<xi> x"
  shows "[x\<leftarrow>p] (\<Phi> x \<and> \<xi> x)" 
(* {{{ Proof }}} *)
proof -
  from a have 
    "(do {x\<leftarrow>p;ret (\<Phi> x \<and> \<xi> x, x)}) = do {x\<leftarrow>p;ret (\<top> \<and> \<xi> x, x)}"
    apply (unfold gdj_def)
    apply (rule gdj2doSeq)
    by (fold gdj_def)
  moreover
  from b have "\<dots> = do {x\<leftarrow>p;ret (\<top> \<and> \<top>, x)}"
    apply (unfold gdj_def)
    apply (rule gdj2doSeq)
    by (fold gdj_def)
  moreover 
  have "\<dots> = do {x\<leftarrow>p;ret (\<top>, x)}"
    by simp
  ultimately show ?thesis
    by (simp add: gdj_def)
qed (* }}} *)

lemma andI_exp: 
  assumes a:"[x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>s x y z] \<Phi> x y z v" and 
          b:"[x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>s x y z] \<xi> x y z v"
  shows 
  "[x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>s x y z] ((\<Phi> x y z v) \<and> (\<xi> x y z v))"
(* {{{ Proof }}} *)
proof -
  from a have a': 
    "[u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>s x y z;ret(x,y,z,v)}] 
                     \<Phi> (fst u) (fst (snd u)) (fst (snd (snd u))) 
                       (snd (snd (snd u)))"
    by (simp add: gdj_def)
  from b have b': 
    "[u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>s x y z;ret(x,y,z,v)}] 
                     \<xi> (fst u) (fst (snd u)) (fst (snd (snd u))) 
                       (snd (snd (snd u)))"
    by (simp add: gdj_def)
  have "[u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>s x y z;ret(x,y,z,v)}] 
              ((\<Phi> (fst u) (fst (snd u)) (fst (snd (snd u))) 
                  (snd (snd (snd u))) \<and>
               (\<xi> (fst u) (fst (snd u)) (fst (snd (snd u))) 
                  (snd (snd (snd u))))))"
    proof -
      from a' have 
	"do {u\<leftarrow>do {x\<leftarrow>p; y\<leftarrow>q x; z\<leftarrow>r x y; v\<leftarrow>s x y z; 
	      ret (x, y, z, v)};
              ret (\<Phi> (fst u) (fst (snd u)) (fst (snd (snd u))) 
	             (snd (snd (snd u))) \<and>
                   \<xi> (fst u) (fst (snd u)) (fst (snd (snd u))) 
	             (snd (snd (snd u))),
             u)} = 
	do {u\<leftarrow>do {x\<leftarrow>p; y\<leftarrow>q x; z\<leftarrow>r x y; v\<leftarrow>s x y z; 
	      ret (x, y, z, v)};
              ret (True \<and>
                   \<xi> (fst u) (fst (snd u)) (fst (snd (snd u))) 
	             (snd (snd (snd u))),
             u)}"
	by (rule gdj2doSeq)
      moreover
      from b' have
	"\<dots> = do {u\<leftarrow>do {x\<leftarrow>p; y\<leftarrow>q x; z\<leftarrow>r x y; v\<leftarrow>s x y z; 
	         ret (x, y, z, v)};
                 ret (True \<and> True,u)}"
	by (rule gdj2doSeq)
      ultimately
      have 
	"do {u\<leftarrow>do {x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>s x y z;ret (x,y,z,v)};
                 ret (\<Phi> (fst u) (fst (snd u)) (fst (snd (snd u))) 
	                (snd (snd (snd u))) \<and>
                      \<xi> (fst u) (fst (snd u)) (fst (snd (snd u))) 
	                (snd (snd (snd u))),
             u)} = 
	 do {u\<leftarrow>do {x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>s x y z; ret (x,y,z,v)};
                 ret (True,u)}"
	by simp
      from this show ?thesis
	by (simp add: gdj_def)
    qed
  from this show ?thesis
    by (simp add: gdj_def)
qed (* }}} *)

lemma wk:
  assumes a: "\<forall>x. (\<Phi> x \<longrightarrow> \<xi> x)" and b: "[x\<leftarrow>p] \<Phi> x"
  shows  "[x\<leftarrow>p] \<xi> x" 
(* {{{ Proof }}} *)
proof -
  have "do {x\<leftarrow>p;ret (\<xi> x, x)} = do {x\<leftarrow>p;ret (\<top> \<and> \<xi> x, x)}"
    by simp
  moreover
  from b have "\<dots> = do {x\<leftarrow>p;ret (\<Phi> x \<and> \<xi> x, x)}"
    proof -
      from b have 
	"do {x\<leftarrow>p;ret (\<Phi> x \<and> \<xi> x, x)} = do {x\<leftarrow>p;ret (\<top> \<and> \<xi> x, x)}" 
	by (rule gdj2doSeq)
      from this show ?thesis ..
    qed
  moreover 
  have "\<dots> = do {x\<leftarrow>p;ret (\<Phi> x, x)}"
  proof -
    from a have "\<forall>x. (\<Phi> x \<and> \<xi> x) = \<Phi> x"
      by (simp add: allandI)
    from this show ?thesis
      by simp
  qed
  moreover 
  from b have "\<dots> = do {x\<leftarrow>p;ret (\<top>, x)}"
    by (simp add: gdj_def)
  ultimately show ?thesis
    by (simp add: gdj_def)
qed (* }}} *)

lemma wk_exp:
  assumes a: "\<forall>x y z v. (\<Phi> x y z v \<longrightarrow> \<xi> x y z v)" and 
          b: "[x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>s x y z] \<Phi> x y z v"
  shows  "[x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>s x y z] \<xi> x y z v"
(* {{{ Proof }}} *)
proof -
  from a have "\<forall>x y z v. (\<Phi> x y z v \<longrightarrow> \<xi> x y z v)"
    by simp
  from this have 
    "\<forall>u. (\<Phi> (fst u) (fst(snd u)) (fst(snd(snd u))) 
            (snd(snd(snd u))) \<longrightarrow> 
          \<xi> (fst u) (fst(snd u)) (fst(snd(snd u))) 
            (snd(snd(snd u))))"
    by simp
  moreover 
  from b have
    "[u\<prec>-(x,y,z,v)\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>s x y z;ret(x,y,z,v)}]
                                                       (\<Phi> x y z v)"
    by simp
  from this have 
    "[u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>s x y z;ret(x,y,z,v)}] 
      (\<Phi> (fst u) (fst(snd u)) (fst(snd(snd u))) (snd(snd(snd u))))"
    by (simp add: gdj_def)
  ultimately have 
    "[u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>s x y z;ret(x,y,z,v)}] 
      (\<xi> (fst u) (fst(snd u)) (fst(snd(snd u))) (snd(snd(snd u))))"
    by (rule wk)
  from this have
    "[u\<prec>-(x,y,z,v)\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>s x y z;ret(x,y,z,v)}]
                                                       (\<xi> x y z v)"
    by (simp add: gdj_def)
  from this show ?thesis
    by simp
qed (* }}} *)

lemma eq:
  assumes a: "[x\<leftarrow>p](q\<^isub>1 x = q\<^isub>2 x)" and 
          b:"[x\<leftarrow>p; y\<leftarrow>q\<^isub>1 x; z\<leftarrow>r x y] \<Phi> x y z"
  shows "[x\<leftarrow>p; y\<leftarrow>q\<^isub>2 x; z\<leftarrow>r x y] \<Phi> x y z" 
(* {{{ Proof }}} *)
proof -
  from a have 
    "(do {x\<leftarrow>p;y\<leftarrow>q\<^isub>2 x;z\<leftarrow>r x y;ret (\<Phi> x y z,x,y,z)}) = 
     (do {x\<leftarrow>p;u\<leftarrow>(do{y\<leftarrow>q\<^isub>2 x;z\<leftarrow>r x y;ret(y,z)});
                         ret (\<Phi> x (fst u) (snd u),x,fst u,snd u)})"
    by simp
  moreover 
  from a have "\<dots> = (do {x\<leftarrow>p;u\<leftarrow>(do{y\<leftarrow>q\<^isub>1 x;z\<leftarrow>r x y;ret(y,z)});
                         ret (\<Phi> x (fst u) (snd u),x,fst u,snd u)})"
    proof -
      from a have 
	"(do {x\<leftarrow>p;u\<leftarrow>(do{y\<leftarrow>q\<^isub>1 x;z\<leftarrow>r x y;ret(y,z)});
	                 ret (\<Phi> x (fst u) (snd u),x,fst u,snd u)})= 
	 (do {x\<leftarrow>p;u\<leftarrow>(do{y\<leftarrow>q\<^isub>2 x;z\<leftarrow>r x y;ret(y,z)});
	                 ret (\<Phi> x (fst u) (snd u),x,fst u,snd u)})"
	by (rule gdjEq2doSeq)
      from this show ?thesis 
	by simp
    qed
  moreover
  have"\<dots> = do {x\<leftarrow>p;y\<leftarrow>q\<^isub>1 x;z\<leftarrow>r x y;ret (\<Phi> x y z,x,y,z)}"
    by simp
  moreover 
  from b  have "\<dots> = do {x\<leftarrow>p;y\<leftarrow>q\<^isub>1 x;z\<leftarrow>r x y;ret (\<top>,x,y,z)}" 
    by (simp add: gdj_def)
  ultimately have 
    "(do {x\<leftarrow>p;y\<leftarrow>q\<^isub>2 x;z\<leftarrow>r x y;ret (\<Phi> x y z,x,y,z)}) = 
      do {x\<leftarrow>p;y\<leftarrow>q\<^isub>1 x;z\<leftarrow>r x y;ret (\<top>,x,y,z)}"
    by simp
  moreover have 
    "\<dots> = (do {x\<leftarrow>p;(y,z)\<leftarrow>(do{y\<leftarrow>q\<^isub>1 x;z\<leftarrow>r x y;ret(y,z)});
                                                   ret (\<top>,x,y,z)})"
    by simp
  ultimately 
  have 
    "(do {x\<leftarrow>p;y\<leftarrow>q\<^isub>2 x;z\<leftarrow>r x y;ret (\<Phi> x y z,x,y,z)}) =  
     (do {x\<leftarrow>p;(y,z)\<leftarrow>(do{y\<leftarrow>q\<^isub>1 x;z\<leftarrow>r x y;ret(y,z)});ret (\<top>,x,y,z)})"
    by (rule trans)
  moreover 
  from a have 
    "\<dots> = (do {x\<leftarrow>p;(y,z)\<leftarrow>(do{y\<leftarrow>q\<^isub>2 x;z\<leftarrow>r x y;ret(y,z)});
                                                   ret (\<top>,x,y,z)})"
    by (rule gdjEq2doSeq)
  moreover
  have "\<dots> = do {x\<leftarrow>p;y\<leftarrow>q\<^isub>2 x;z\<leftarrow>r x y;ret (\<top>,x,y,z)}"
    by simp
  ultimately have 
    "(do {x\<leftarrow>p;y\<leftarrow>q\<^isub>2 x;z\<leftarrow>r x y;ret (\<Phi> x y z,x,y,z)}) = 
      do {x\<leftarrow>p;y\<leftarrow>q\<^isub>2 x;z\<leftarrow>r x y;ret (\<top>,x,y,z)}"
    by simp
  from this show ?thesis
    by (simp add: gdj_def)
qed (* }}} *)

lemma app: 
  assumes a:"[x\<leftarrow>p] \<Phi> x"  
  shows "[x\<leftarrow>p;y\<leftarrow>q x] \<Phi> x" 
(* {{{ Proof }}} *)
proof -
  from a have 
    "do {x\<leftarrow>p; y\<leftarrow>q x; ret (\<Phi> x,x,y)} = 
     do {x\<leftarrow>p; y\<leftarrow>q x; ret (\<top>,x,y)}"
    by (rule gdj2doSeq)
  from this show ?thesis
    by (simp add: gdj_def)
qed (* }}} *)

lemma app_exp: 
  assumes a:"[x\<leftarrow>p;y\<leftarrow>q x] \<Phi> x y"  
  shows "[x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y] \<Phi> x y" 
(* {{{ Proof }}} *)
proof -
  from a have 
    "[u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;ret(x,y)}] \<Phi> (fst u) (snd u)"
    by (simp add: gdj_def)
  from this have
    "do {u\<leftarrow>do{x\<leftarrow>p; y\<leftarrow>q x; ret(x,y)};
               z\<leftarrow>r (fst u) (snd u);
               ret (\<Phi> (fst u) (snd u),fst u,snd u,z)} = 
     do {u\<leftarrow>do{x\<leftarrow>p; y\<leftarrow>q x; ret(x,y)};
               z\<leftarrow>r (fst u) (snd u);
               ret (\<top>,fst u,snd u,z)}"
    by (rule gdj2doSeq)
  from this have
    "do {x\<leftarrow>p; y\<leftarrow>q x; z\<leftarrow>r x y; ret (\<Phi> x y,x,y,z)} = 
    do {x\<leftarrow>p; y\<leftarrow>q x; z\<leftarrow>r x y; ret (\<top>,x,y,z)}"
    by simp
  from this show ?thesis
    by (simp add: gdj_def)
qed (* }}} *)

lemma app_exp': 
  assumes a:"[x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y] \<Phi> x y z"  
  shows "[x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;v\<leftarrow>t x y z] \<Phi> x y z" 
(* {{{ Proof }}} *)
proof -
  from a have 
    "[u\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x y;ret(x,y,z)}] 
                               \<Phi> (fst u) (fst(snd u)) (snd(snd u))"
    by (simp add: gdj_def)
  from this have
    "do {u\<leftarrow>do{x\<leftarrow>p; y\<leftarrow>q x; z\<leftarrow>r x y;ret(x,y,z)};
               v\<leftarrow>t (fst u) (fst(snd u)) (snd(snd u));
               ret (\<Phi> (fst u) (fst(snd u)) (snd(snd u)),(fst u),
                   (fst(snd u)),(snd(snd u)),v)} = 
     do {u\<leftarrow>do{x\<leftarrow>p; y\<leftarrow>q x; z\<leftarrow>r x y;ret(x,y,z)};
               v\<leftarrow>t (fst u) (fst(snd u)) (snd(snd u));
               ret (\<top>,(fst u),(fst(snd u)),(snd(snd u)),v)}"
    by (rule gdj2doSeq)
  from this have
    "do {x\<leftarrow>p; y\<leftarrow>q x; z\<leftarrow>r x y;v\<leftarrow>t x y z; ret (\<Phi> x y z,x,y,z,v)} = 
    do {x\<leftarrow>p; y\<leftarrow>q x; z\<leftarrow>r x y;v\<leftarrow>t x y z; ret (\<top>,x,y,z,v)}"
    by simp
  from this show ?thesis
    by (simp add: gdj_def)
qed (* }}} *)

lemma \<eta>: 
  "[x\<leftarrow>p; y\<leftarrow>ret (a x); z\<leftarrow>(q x y)] (\<Phi> x y z) = 
   [x\<leftarrow>p; z\<leftarrow>(q x (a x))] (\<Phi> x (a x) z)"
(* {{{ Proof }}} *)
proof 
  assume "[x\<leftarrow>p; y\<leftarrow>ret (a x); z\<leftarrow>(q x y)] (\<Phi> x y z)"
  from this have 
    "[u\<leftarrow>(do{x\<leftarrow>p; y\<leftarrow>ret (a x); z\<leftarrow>(q x y);ret(x,y,z)})] 
                       (\<Phi> (fst u) (a (fst u))) (snd (snd u))"
    by (simp add: gdj_def)    
  from this 
  have 
    "do{u\<leftarrow>do {x\<leftarrow>p; y\<leftarrow>ret (a x); z\<leftarrow>q x y; ret (x,y,z)};
                ret(\<Phi> (fst u) (a (fst u)) (snd (snd u)),fst u,
                    snd (snd u))} = 
       do{u\<leftarrow>do {x\<leftarrow>p; y\<leftarrow>ret (a x); z\<leftarrow>q x y; ret (x,y,z)};
                ret(\<top>,fst u,snd(snd u))}"
    by (rule gdj2doSeq)
  from this show "[x\<leftarrow>p; z\<leftarrow>(q x (a x))] (\<Phi> x (a x) z)"
    by (simp add: gdj_def)
next
  assume "[x\<leftarrow>p; z\<leftarrow>(q x (a x))] (\<Phi> x (a x) z)"
  from prems have 
    "[u\<leftarrow>do {x\<leftarrow>p; z\<leftarrow>q x (a x); ret (x, z)}]
                                     \<Phi> (fst u) (a (fst u)) (snd u)"
    by (simp add: gdj_def)
  from this 
  have 
    "do{u\<leftarrow>do {x\<leftarrow>p; z\<leftarrow>q x (a x); ret (x, z)};
        ret(\<Phi> (fst u) (a (fst u)) (snd u),fst u,a (fst u),snd u)} =
     do{u\<leftarrow>do {x\<leftarrow>p; z\<leftarrow>q x (a x); ret (x, z)};
        ret(\<top>,fst u,a (fst u),snd u)}"
    by (rule gdj2doSeq)
  from this show "[x\<leftarrow>p; y\<leftarrow>ret (a x); z\<leftarrow>(q x y)] (\<Phi> x y z)"
    by (simp add: gdj_def)
qed (* }}} *)

lemma \<eta>_cut: "[y\<leftarrow>ret a; z\<leftarrow>(q y)] (\<Phi> y) = [z\<leftarrow>(q a)] (\<Phi> a)"
(* {{{ Proof }}} *)
proof -
  have 
    "[y\<leftarrow>ret a; z\<leftarrow>(q y)] (\<Phi> y) = [u\<leftarrow>ret();y\<leftarrow>ret a; z\<leftarrow>(q y)] (\<Phi> y)"
    by (rule "**-")
  moreover 
  have "[z\<leftarrow>(q a)] (\<Phi> a) = [u\<leftarrow>ret();z\<leftarrow>(q a)] (\<Phi> a)"
    by (rule "*-")
  moreover 
  have 
    "[u\<leftarrow>ret();y\<leftarrow>ret a; z\<leftarrow>(q y)] (\<Phi> y) = [u\<leftarrow>ret();z\<leftarrow>(q a)] (\<Phi> a)"
    by (rule \<eta>) 
  ultimately show ?thesis
    by simp
qed (* }}} *)

lemma ctr: 
  assumes a: "[v\<leftarrow>t;x\<leftarrow>p v;y\<leftarrow>q v x;z\<leftarrow>r v y] (\<Phi> v y z)" 
  shows "[v\<leftarrow>t;y\<leftarrow>(do {x\<leftarrow>p v;q v x});z\<leftarrow>r v y] (\<Phi> v y z)"
(* {{{ Proof }}} *)
proof -
  from prems 
  have "[u\<leftarrow>do{v\<leftarrow>t;x\<leftarrow>p v;y\<leftarrow>q v x;z\<leftarrow>r v y;ret(v,x,y,z)}] 
        (\<Phi> (fst u) (fst (snd (snd u))) (snd (snd (snd u))))"
    by (simp add: gdj_def)
  from this have
    "do{u\<leftarrow>do{v\<leftarrow>t;x\<leftarrow>p v;y\<leftarrow>q v x;z\<leftarrow>r v y;ret(v,x,y,z)}; 
           ret (\<Phi> (fst u) (fst (snd (snd u))) (snd (snd (snd u))), 
               (fst u), (fst (snd (snd u))), (snd (snd (snd u))))}=
     do{u\<leftarrow>do{v\<leftarrow>t;x\<leftarrow>p v;y\<leftarrow>q v x;z\<leftarrow>r v y;ret(v,x,y,z)}; 
           ret (True, 
               (fst u), (fst (snd (snd u))), (snd (snd (snd u))))}"
    by (rule gdj2doSeq) 
  from this show ?thesis
    by (simp add: gdj_def)
qed (* }}} *)

lemma ctr_cut: 
  assumes a: "[x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r y] (\<Phi> y z)"
  shows "[y\<leftarrow>(do {x\<leftarrow>p;q x});z\<leftarrow>r y] (\<Phi> y z)"
(* {{{ Proof }}} *)
proof -
  from a have "[v\<leftarrow>ret();x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r y] (\<Phi> y z)"
    by (simp add: "***-")
  from this have "[v\<leftarrow>ret();y\<leftarrow>do{x\<leftarrow>p;q x};z\<leftarrow>r y] (\<Phi> y z)"
    by (rule ctr)
  from this show ?thesis
    apply (subst "**-")
    by simp
qed (* }}} *)

lemma ctr_cut2: 
  assumes "[u\<leftarrow>t;x\<leftarrow>p u;y\<leftarrow>q u x] (\<Phi> u y)"
  shows "[u\<leftarrow>t;y\<leftarrow>(do {x\<leftarrow>p u;q u x})] (\<Phi> u y)"
(* {{{ Proof }}} *)
proof -
  from prems have "[u\<leftarrow>t;x\<leftarrow>p u;y\<leftarrow>q u x;z\<leftarrow>ret ()] (\<Phi> u y)"
    by (simp add: "-***")
  from this have "[u\<leftarrow>t;y\<leftarrow>(do {x\<leftarrow>p u;q u x});z\<leftarrow>ret()] (\<Phi> u y)"
    by (rule ctr)
  from this show ?thesis
    apply (subst "-**")
    by simp
qed (* }}} *)

lemma tau: 
  assumes "\<forall>x.(\<Phi> x)" 
  shows "[x\<leftarrow>p] \<Phi> x"
(* {{{ Proof }}} *)
proof -
  from prems show ?thesis
    by (simp add: gdj_def)
qed (* }}} *)

lemma tau_exp: 
  assumes "\<forall>x. \<forall>y.(\<Phi> x y)" 
  shows "[x\<leftarrow>p;y\<leftarrow>q] \<Phi> x y"
(* {{{ Proof }}} *)
proof -
  from prems show ?thesis
    by (simp add: tau pre)
qed (* }}} *)

lemma rp: 
  assumes a:"\<forall>x.(q\<^isub>1 x = q\<^isub>2 x)" and 
          b: "[x\<leftarrow>p; y\<leftarrow>q\<^isub>1 x; z\<leftarrow>r x y] \<Phi> x y z"
  shows "[x\<leftarrow>p; y\<leftarrow>q\<^isub>2 x; z\<leftarrow>r x y] \<Phi> x y z"
(* {{{ Proof }}} *)
proof -   
  from a have "[x\<leftarrow>p] (q\<^isub>1 x = q\<^isub>2 x)"
    by (rule tau)
  from this b show "[x\<leftarrow>p; y\<leftarrow>q\<^isub>2 x; z\<leftarrow>r x y] \<Phi> x y z" 
    by (rule eq)
qed (* }}} *)

lemma rp_cut: 
  assumes a: "\<forall>x.((q\<^isub>1 x) = (q\<^isub>2 x))" and b:"[x\<leftarrow>p; y\<leftarrow>q\<^isub>1 x] \<Phi> x y"
  shows "[x\<leftarrow>p; y\<leftarrow>q\<^isub>2 x] \<Phi> x y"
(* {{{ Proof }}} *)
proof -
  from b have "[x\<leftarrow>p; y\<leftarrow>q\<^isub>1 x;z\<leftarrow>ret()] \<Phi> x y"
    by (simp add: "-**")
  from a this have  "[x\<leftarrow>p; y\<leftarrow>q\<^isub>2 x;z\<leftarrow>ret()] \<Phi> x y"
    by (rule rp)
  from this show ?thesis
    by (simp add: "-**")
qed (* }}} *)

lemma sef: 
  assumes a: "[x\<leftarrow>p;y\<leftarrow>q x;z\<leftarrow>r x] \<Phi> x z" and b: "\<forall>x. sef (q x)"
  shows "[x\<leftarrow>p;z\<leftarrow>r x] \<Phi> x z"
(* {{{ Proof }}} *)
proof -
  from b have "\<forall>x. ((do{y\<leftarrow>q x;r x}) = r x)" 
    by (simp add: seFree)
  moreover 
  from a
  have "[x\<leftarrow>p;z\<leftarrow>do{y\<leftarrow>q x;r x}] \<Phi> x z"
    by (rule ctr_cut2)
  ultimately show ?thesis
    by (rule rp_cut)
qed (* }}} *)

end