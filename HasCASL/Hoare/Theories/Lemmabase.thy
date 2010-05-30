theory Lemmabase imports MonadSyntax begin

(*<*)lemma allandI: "((r \<longrightarrow> q) = ((r \<and> q) = r))"
(* {{{ Proof }}} *)
proof (cases q)
  case True
  from this show ?thesis
    by simp
next
  case False
  from this show ?thesis
    by simp
qed 
(* }}} *)(*>*)

(*lemma 4.4: "(\<lbrakk>p = ret unit\<rbrakk> \<Longrightarrow> dis p) \<and> \<lbrakk>dis p\<rbrakk> \<Longrightarrow> p = ret unit"*)
(*lemma "sef_retUnit": "(p = ret ()) = sef p"
  apply (rule iffI)
  apply (simp_all add: sef_def)
done*)

(*lemma 4.4: "(\<lbrakk>p = ret unit\<rbrakk> \<Longrightarrow> dis p) \<and> \<lbrakk>dis p\<rbrakk> \<Longrightarrow> p = ret unit"*)

lemma "sef_retUnit": "(p = ret ()) = sef p"
proof 
  assume "p = ret ()"
  from this have "sef (ret ())"
    by (simp add: sef_def)
  from prems this show "sef p"
    by blast
next
  (* {{{ 2. case }}} *)  
  assume "sef p"
  from this have "p = do {y\<leftarrow>p;ret ()}"
    by simp
  moreover
  from prems this have "p = ret ()"
    apply (unfold sef_def)
    by simp
  ultimately show "p = ret ()" 
    by blast
  (* }}} *)
qed

lemma "seFree": 
  assumes "sef p"  
  shows "do {p;q} = q" 
(* {{{ Proof }}} *)  
proof - 
  have "do {p;q} = do {p; ret (); q}"
    by (simp add: bind'_def del: delBind)
  also 
  have "\<dots> = do {do{p; ret ()}; q}"
    by simp
  also
  from prems have "\<dots> = do {ret ();q}" 
    by (simp add: sef_def)
  also  
  have "\<dots> = q" 
    by (simp add: bind'_def del: delBind)
  finally show "do {p;q} = q" .
qed 
(* }}} *)  

lemma "seFree2":
  assumes ret_q: "q = ret()" and sef_p:"sef p"
  shows "do {p;q} = p"
(* {{{ Proof }}} *)  
proof -
  from prems have "p = ret()"
    by (simp only: sef_retUnit)
  from this ret_q have "p = q"
    by blast
  moreover
  from sef_p have "do{p;q} = q"
    by (simp only: seFree)
  ultimately show ?thesis
    by simp
qed 
(* }}} *)

lemma ret2seq:
  assumes "do {x\<leftarrow>p;ret x} = do {x\<leftarrow>q;ret x}"
  shows "do {x\<leftarrow>p;r x} = do {x\<leftarrow>q;r x}"
(* {{{ Proof }}} *)  
proof -
  have "do {x\<leftarrow>p;r x} = do {z\<leftarrow>(do {x\<leftarrow>p;ret x});r z}"
    apply (subst sndUnitLaw) ..
  moreover from prems
  have "\<dots> = do {z\<leftarrow>(do {x\<leftarrow>q;ret x});r z}"
    by auto
  moreover
  have "\<dots> = do {x\<leftarrow>q;r x}" 
    apply (subst sndUnitLaw) ..
  ultimately show ?thesis by simp
qed 
(* }}} *)

lemma ret2seq_exp:
  assumes "do {x\<leftarrow>p1;y\<leftarrow>p2 x;ret (x,y)} = do {x\<leftarrow>q1;y\<leftarrow>q2 x;ret (x,y)}"
  shows "do {x\<leftarrow>p1;y\<leftarrow>p2 x;r x y} = do {x\<leftarrow>q1;y\<leftarrow>q2 x;r x y}"
(* {{{ Proof }}} *)  
proof -
  from prems have
    "do {z\<leftarrow>(do{x\<leftarrow>p1;y\<leftarrow>p2 x;ret (x,y)});ret z} = 
     do {z\<leftarrow>(do{x\<leftarrow>q1;y\<leftarrow>q2 x;ret (x,y)});ret z}"
    by (simp only: sndUnitLaw)
  from this have 
    "do {z\<leftarrow>(do{x\<leftarrow>p1;y\<leftarrow>p2 x;ret (x,y)});r (fst z) (snd z)} =
     do {z\<leftarrow>(do{x\<leftarrow>q1;y\<leftarrow>q2 x;ret (x,y)});r (fst z) (snd z)}" 
    by (rule ret2seq)
  from this show ?thesis
    by simp
qed 
(* }}} *)

lemma ret2seqSw:
  assumes "do {x\<leftarrow>p1;y\<leftarrow>p2 x;ret (y,x)} = 
           do {x\<leftarrow>q1;y\<leftarrow>q2 x;ret (y,x)}"
  shows "do {x\<leftarrow>p1;y\<leftarrow>p2 x;r x y} = do {x\<leftarrow>q1;y\<leftarrow>q2 x;r x y}"
(* {{{ Proof }}} *)  
proof -
  from prems have 
    "do {z\<leftarrow>(do{x\<leftarrow>p1;y\<leftarrow>p2 x;ret (y,x)});ret z} = 
     do {z\<leftarrow>(do{x\<leftarrow>q1;y\<leftarrow>q2 x;ret (y,x)});ret z}"
    by (simp only: sndUnitLaw)
  from this have 
    "do {z\<leftarrow>(do{x\<leftarrow>p1;y\<leftarrow>p2 x;ret (y,x)});r (snd z) (fst z)} = 
     do {z\<leftarrow>(do{x\<leftarrow>q1;y\<leftarrow>q2 x;ret (y,x)});r (snd z) (fst z)}" 
    by (rule ret2seq)
  from this show ?thesis 
    by simp
qed 
(* }}} *)


lemma ret2seqSw':
  assumes "do {x\<leftarrow>p1;y\<leftarrow>p2;ret (x,y)} = 
           do {y\<leftarrow>q1;x\<leftarrow>q2;ret (x,y)}"
  shows "do {x\<leftarrow>p1;y\<leftarrow>p2;r x y} = do {y\<leftarrow>q1;x\<leftarrow>q2;r x y}"
(* {{{ Proof }}} *)  
proof - 
  from prems have 
    "do {z\<leftarrow>(do{x\<leftarrow>p1;y\<leftarrow>p2;ret (x,y)});ret z} = 
     do {z\<leftarrow>(do{y\<leftarrow>q1;x\<leftarrow>q2;ret (x,y)});ret z}"
    by (simp only: sndUnitLaw)
  from this have 
    "do {z\<leftarrow>(do{x\<leftarrow>p1;y\<leftarrow>p2;ret (x,y)});r (fst z)(snd z)} = 
     do {z\<leftarrow>(do{y\<leftarrow>q1;x\<leftarrow>q2;ret (x,y)});r (fst z)(snd z)}" 
    by (rule ret2seq)
  from this show ?thesis 
    by simp
qed 
(* }}} *)


lemma cp_ret2seq:
  assumes "cp p"
  shows "do {x\<leftarrow>p;y\<leftarrow>p;r x y} = do{x\<leftarrow>p;r x x}"
(* {{{ Proof }}} *)  
proof -
  from prems have 
    "do {x\<leftarrow>p; y\<leftarrow>p; ret (x, y)} = do {x\<leftarrow>p; ret (x, x)}"
    by (simp add: cp_def)
  from this have 
    "do{z\<leftarrow>do {x\<leftarrow>p; y\<leftarrow>p; ret (x, y)};ret z} = 
     do{z\<leftarrow>do {x\<leftarrow>p; ret (x, x)};ret z}"
    by simp
  from this have 
    "do{z\<leftarrow>do {x\<leftarrow>p; y\<leftarrow>p; ret (x, y)};r (fst z) (snd z)} = 
     do{z\<leftarrow>do {x\<leftarrow>p; ret (x, x)};r (fst z) (snd z)}"
    by (simp add: "seFree")
  from this show ?thesis
    by simp
qed 
(* }}} *)

lemma eq_res: 
  "\<forall>x. ((r x) res ((r x)=(s x))) = ((s x) res ((r x)=(s x)))"
(* {{{ Proof }}} *)  
proof (cases "\<forall>x.(r x)=(s x)")
  case True
  from this show ?thesis
    by (simp add: res_def)
next 
  case False
  from this show ?thesis
    by (simp add: res_def)
qed 
(* }}} *)
 
(*"4~24/i_ii"*)
lemma "cpsefProps(i\<rightarrow>ii)": 
  assumes sef_p: "sef p" and sef_q: "sef q" and
          i: "cp(do{x\<leftarrow>p;y\<leftarrow>q;ret(x,y)})"
  shows "do{x\<leftarrow>p;y\<leftarrow>q;ret(x,y)} = do{y\<leftarrow>q;x\<leftarrow>p;ret(x,y)}"
(* {{{ Proof }}} *)  
proof -
  let ?s = "do{x\<leftarrow>p;y\<leftarrow>q;ret(x,y)}"
  from sef_p sef_q have sef_s: "sef ?s"
    by (simp add: sef_def del: delBind)
  from i have cp_s: "cp ?s"
    by simp

  have "?s = do{z\<leftarrow>?s; ret z}"
    by simp
  moreover from sef_s have "\<dots> = do{z\<leftarrow>do{?s;?s};ret z}"
    apply (subst "seFree") 
    apply blast ..
  moreover have "\<dots> = do{w\<leftarrow>?s;z\<leftarrow>?s;ret (fst z, snd z)}"
    by simp
  moreover 
  from cp_s sef_s have "\<dots> = do{w\<leftarrow>?s;z\<leftarrow>?s;ret (fst z, snd w)}"
  (* {{{ Proof }}} *)  
  proof -
    from sef_s have 
      "do{w\<leftarrow>?s;z\<leftarrow>?s;ret (fst z, snd z)} = 
       do{w\<leftarrow>?s;ret(fst w,snd w)}"
      by (simp add: seFree del: do_assoc1)
    moreover
    from prems have "\<dots> = do{w\<leftarrow>?s;z\<leftarrow>?s;ret(fst z, snd w)}"
      by (simp add: cp_ret2seq del: assocLaw)
    ultimately show ?thesis
      by (simp del: assocLaw)
  qed 
  (* }}} *)
  moreover have "\<dots> = do{u\<leftarrow>p;v\<leftarrow>q;x\<leftarrow>p;y\<leftarrow>q;ret(x,v)}"
    by simp
  moreover from sef_p sef_q have "\<dots> = do{v\<leftarrow>q;x\<leftarrow>p;ret(x,v)}"
    by (simp add: seFree)
  ultimately show ?thesis
    by simp
qed 
(* }}} *)

lemma "cpsefProps(ii\<rightarrow>iii)":
  assumes ii: "(do{x\<leftarrow>p;y\<leftarrow>q;ret(x,y)} = do{y\<leftarrow>q;x\<leftarrow>p;ret(x,y)})"
  shows "do{x\<leftarrow>p;y\<leftarrow>q;r x y} = do{y\<leftarrow>q;x\<leftarrow>p;r x y}"
(* {{{ Proof }}} *)  
proof -
  from ii have 
    "do{x\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q;ret(x,y)};ret x} = 
     do{x\<leftarrow>do{y\<leftarrow>q;x\<leftarrow>p;ret(x,y)};ret x}"
    by simp
  from this have
    "do{x\<leftarrow>do{x\<leftarrow>p;y\<leftarrow>q;ret(x,y)};r (fst x) (snd x)} = 
     do{x\<leftarrow>do{y\<leftarrow>q;x\<leftarrow>p;ret(x,y)};r (fst x) (snd x)}"
    by (rule ret2seq)
  from this show ?thesis
    by simp
qed 
(* }}} *)    

lemma weak_sef2seq: 
  assumes "sef p" "\<forall>x. sef (r x)"
  shows "sef (do {x\<leftarrow>p; r x})"
(* {{{ Proof }}} *)  
proof -
  have 
    "do {z\<leftarrow>do {x\<leftarrow>p; r x}; ret ()} = 
     do {x\<leftarrow>p; do{r x; ret ()}}"
    by simp
  moreover from prems have "\<dots> = do {x\<leftarrow>p; ret()}"
    by (simp add: sef_def)
  moreover from prems have "\<dots> = ret ()" 
    by (simp add: sef_def)
  ultimately show ?thesis 
    by (simp add: sef_def)
qed 
(* }}} *)

lemma weak_cp2retSeq:
  assumes "cp p"
  shows "cp (do{x\<leftarrow>p; ret(a x)})"
(* {{{ Proof }}} *)  
proof -
  have 
    "(do{u\<leftarrow>do{x\<leftarrow>p;ret(a x)};v\<leftarrow>do{y\<leftarrow>p;ret (a y)};ret (u,v)})=
     (do{x\<leftarrow>p;u\<leftarrow>ret(a x);y\<leftarrow>p;v\<leftarrow>ret (a y);ret (u,v)})"
    by (simp only: assocLaw)
  moreover have 
    "\<dots> = (do{x\<leftarrow>p; y\<leftarrow>p;ret(a x, a y)})"
    by (simp only: fstUnitLaw)
  moreover from prems have
    "\<dots> = (do{x\<leftarrow>p;ret(a x,a x)})"
    by (simp only: cp_ret2seq)
  moreover have
    "\<dots> = do{x\<leftarrow>p;u\<leftarrow>ret(a x);ret(u,u)}"
    by (simp only: fstUnitLaw)
  moreover have
    "\<dots> = do{u\<leftarrow>do{x\<leftarrow>p;ret(a x)};ret(u,u)}"
    by (simp only: assocLaw)
  ultimately show ?thesis
    by (simp only: cp_def)
qed 
(* }}} *)


end