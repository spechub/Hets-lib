header {*Division Nat\"urlicher Zahlen mit Rest*}
	
theory ExampleProof = HoareCalc:

text{*Um die Anwendung des implementierten Hoare-Kal"uls zu 
  demonstrieren, wird der in \cite{Ho69} vorgestellte Beweis
  implementiert. Dies war der erste ver\"offentlichte
  Korrektheitsbeweis auf Basis der Hoare-Triple. Er zeigt, dass die 
  folgende Programmsequenz eine korrekte Umsetzung der Division mit Rest
  beschreibt.
  \Center{
  \code{\DO{r\gets x;q\gets 0;
          z\gets while (y@{text \<le>}r) \DO{
             r\gets (r-y);
             q\gets (q+1);
             ret(r,q)}
          }}}
  Da der Beweis unabh\"angig von der konkreten Belegung der einzelnen
  Variablen vor Eintritt in das Programm sein soll, wird als Vorbedingung
  \code{True} gew\"ahlt. F\"ur die Nachbedingung muss \code{x=r+y*q} gelten. 
  Dies ist nichts anderes als eine Umschreibung daf\"ur,
  dass nach Programmabarbeitung \code{q} das ganzzahlige Ergebnis der
  Division sein soll und \code{r} der Rest, der dabei entsteht. Zu dem soll
  die Abbruchbedingung der Schleife erreicht sein. Es muss also zus\"atzlich 
  @{text "\<not>(y\<le>(r)"} gelten.\abs
  Der hier aufgef\"uhrte Beweis folgt dem Schema, dass Hoare in \cite{Ho69}
  vorgeschlagen hat. Allerdings m\"ussen die einzelnen Schritte zum Teil
  etwas detaillierter bearbeitet werden.
*}
(*  \lemmaNoName{DIV}
  {\premsNoNewline{
      \lemmaNoName{D2} 
      {\premsNoNewline{
          \lemmaNoName{D2}
          {\premsNoNewline{1}{2}}
          {\concl{4}}
        }{3}
      }
      {\concl{5}}
   }
   { \lemmaNoName{D2}
     {\prem{
         \lemmaNoName{D2} 
         {\premsNoNewline{
             \lemmaNoName{D2}
             {\premsNoNewline{7}{8}}
             {\concl{9}}
           }{6}
         }
         {\concl{10}}
       }}
     {\concl{11}}
   }}
  {\concl{DIV = True}}
*)
lemma
  "\<lbrace>\<Up>True\<rbrace> 
     r\<leftarrow>ret (x::nat); 
     q\<leftarrow>ret (0::nat);
     z\<leftarrow>(while\<^isub>D \<up>(ret(y\<le>r)) do{
           r\<leftarrow>ret(r-y);
           q\<leftarrow>ret(1+q);
           ret()
        })
   \<lbrace>(\<Up>(x=r+y*q))\<and>\<^isub>D \<not>\<^isub>D(\<Up>(y\<le>r))\<rbrace>"
proof -
  txt{*Zun\"achst wird gezeigt, dass f\"ur die Sequenz der 
    ersten beiden Programmzeilen
    @{text "\<lbrace>\<Up>True\<rbrace>r\<leftarrow>ret x;q\<leftarrow>ret 0\<lbrace>\<Up>(x=r+y*q)\<rbrace>"}
    gilt. [1]-[4] dienen dabei lediglich als Vorbereitung f\"ur den 
    eigentlichen Sequenzierungsschritt, der in [5] durchgef\"uhrt wird.*}
  have "[1]": "\<lbrace>\<Up>True\<rbrace>\<lbrace>\<Up>(x=x+y*0)\<rbrace>"
    proof -
      have "ret True \<in> Dsef"
	by (simp add: dsef_ret Dsef_def)
      moreover have "\<lbrace>\<Up>True\<rbrace>\<lbrace>\<Up>True\<rbrace>"
	by (simp add: emptySeq)
      ultimately show ?thesis
	by simp
    qed
  have "[2]": "\<lbrace>\<Up>(x=x+y*0)\<rbrace>r\<leftarrow>ret x\<lbrace>\<Up>(x=r+y*0)\<rbrace>"
    proof -
      have "ret True \<in> Dsef"
	by (simp add: dsef_ret Dsef_def)
      moreover have "\<forall>p. \<lbrace>\<Up>True\<rbrace>p\<lbrace>\<Up>True\<rbrace>"
	by (simp add: stateless)
      ultimately show ?thesis
	by (simp add: hoare_def gdj_def)
    qed
  have "[3]": "\<forall>r. \<lbrace>\<Up>(x=r+y*0)\<rbrace>q\<leftarrow>ret 0\<lbrace>\<Up>(x=r+y*q)\<rbrace>"
    proof -
      have "\<forall>r. ret(x=r)\<in> Dsef"
	by (simp add: dsef_ret Dsef_def)
      from this show ?thesis
	by (simp add: hoare_def gdj_def)
    qed
  from "[2]" and "[1]"
  have "[4]": "\<lbrace>\<Up>True\<rbrace>r\<leftarrow>ret x\<lbrace>\<Up>(x=r+y*0)\<rbrace>"
    by (rule wk_pre)

  from "[4]" and "[3]"
  have "[5]": "\<lbrace>\<Up>True\<rbrace>r\<leftarrow>ret x;q\<leftarrow>ret 0\<lbrace>\<Up>(x=r+y*q)\<rbrace>"
    by (rule seq)

  txt{*Um die schw\"achere Vorbedingung @{text "\<lbrace>\<Up>(x=(r-y)+y*(1+q))\<rbrace>"},
    die bei der Bearbeitung der Sequenz @{text "r\<leftarrow>ret(r-y);q\<leftarrow>ret(1+q)"}
    ben\"otigt wird, zu einer geeignet Vorbedingung f\"ur die Anwendung 
    von while zu erweitern, muss gezeigt werden, dass aus der neuen 
    Vorbedingung die schw\"achere folgt.*}
  have "[6]": "\<lbrace>\<Up>(x=r+y*q)\<and>\<^isub>D \<Up>(y\<le>r)\<rbrace>\<lbrace>\<Up>(x=(r-y)+y*(1+q))\<rbrace>"
    proof -
      have "ret (x = r + y * q) \<in> Dsef"
	by (simp add: dsef_ret Dsef_def)
      moreover
      have "ret (y \<le> r) \<in> Dsef"
	by (simp add: dsef_ret Dsef_def)
      moreover
      have "ret (x = r - y + (y + y * q)) \<in> Dsef"
	by (simp add: dsef_ret Dsef_def)
      moreover 
      have "ret (x = r + y * q \<and> y \<le> r) \<in> Dsef"
	by (simp add: dsef_ret Dsef_def)
      ultimately show ?thesis
	by (simp add: condConj_def hoare_Tupel_def gdj_def)
    qed

  txt{*[7]-[9] bearbeiten die Sequenz in der Schleife und zeigen, 
    dass f\"ur sie\\ @{text "\<lbrace>\<Up>(x=(r-y)+y*(1+q))\<rbrace>r\<leftarrow>ret(r-y);q\<leftarrow>ret(1+q)\<lbrace>\<Up>(x=r+y*q)\<rbrace>"}
    gilt.*}
  have "[7]": "\<lbrace>\<Up>(x=(r-y)+y*(1+q))\<rbrace>r\<leftarrow>ret(r-y)\<lbrace>\<Up>(x=r+y*(1+q))\<rbrace>"
    proof -
      have "ret (x = r - y + (y + y * q)) \<in> Dsef"
	by (simp add: dsef_ret Dsef_def)
      from this show ?thesis
	by (simp add: hoare_def gdj_def)
    qed
  have "[8]": "\<forall>r. \<lbrace>\<Up>(x=r+y*(1+q))\<rbrace>q\<leftarrow>ret(1+q)\<lbrace>\<Up>(x=r+y*q)\<rbrace>"
    proof -
      have "\<forall>r. ret (x = r + (y + y * q)) \<in> Dsef"
	by (simp add: dsef_ret Dsef_def)
      from this show ?thesis
	by (simp add: hoare_def gdj_def)
    qed

  from "[7]" and "[8]"
  have "[9]": 
    "\<lbrace>\<Up>(x=(r-y)+y*(1+q))\<rbrace>
        r\<leftarrow>ret(r-y);q\<leftarrow>ret(1+q)
     \<lbrace>\<Up>(x=r+y*q)\<rbrace>"
    by (rule seq)

  txt{*Mit Hilfe von [6] wird unter Verwendung der Regel wk\_pre
    die Vorbedingung von [9] nun noch 
    um die Schleifenbedingung erweitert. Das resultierende Hoare-Tripel
    ist die Vorraussetzung f\"ur die Anwendung der while-Regel in [11].*}
  from "[9]" and "[6]"
  have "[10]": 
    "\<lbrace>\<Up>(x=r+y*q)\<and>\<^isub>D \<Up>(y\<le>r)\<rbrace>
        r\<leftarrow>ret(r-y);q\<leftarrow>ret(1+q)
     \<lbrace>\<Up>(x=r+y*q)\<rbrace>"
    by (rule wk_pre)

  from "[10]" have "[11]": 
    "\<forall>r q. \<lbrace>\<Up>(x=r+y*q)\<rbrace>
       z\<leftarrow>while\<^isub>D \<up>(ret(y\<le>r)) do{r\<leftarrow>ret(r-y);q\<leftarrow>ret((1::nat)+q);ret()}
    \<lbrace>\<Up>(x=r+y*q)\<and>\<^isub>D \<not>\<^isub>D\<Up>(y\<le>r)\<rbrace>"
    proof -
      from "[10]" have "\<forall>r q. 
	\<lbrace>\<Up>(x = r+y*q)\<and>\<^isub>D \<Up>(y \<le> r)\<rbrace>
	    z\<leftarrow>do {r\<leftarrow>ret (r - y); q\<leftarrow>ret (1 + q); ret ()}
	\<lbrace>\<Up>(x=r+y*q)\<rbrace>"
	apply (simp add: hoare_def condConj_def)
	apply (simp add: dsef_ret Dsef_def gdj_def)
	by simp
      moreover have
	"\<forall>r q.
	(\<lbrace>\<Up>(x = r+y*q)\<and>\<^isub>D \<Up>(y \<le> r)\<rbrace>
	    z\<leftarrow>do {r\<leftarrow>ret (r - y); q\<leftarrow>ret (1 + q); ret ()}
	\<lbrace>\<Up>(x=r+y*q)\<rbrace> \<longrightarrow>	
	\<lbrace>\<Up>(x = r+y*q)\<rbrace>
	    z\<leftarrow>iter\<^isub>D (\<lambda>x. \<up>ret(y \<le> r)) 
                     (\<lambda>x. do {r\<leftarrow>ret (r - y); q\<leftarrow>ret (1+q);ret()})
                     ()
   	\<lbrace>\<Up>(x = r+y*q)\<and>\<^isub>D \<not>\<^isub>D\<Up>(y \<le> r)\<rbrace>)"
	apply auto
	apply (rule iter)
	by simp
      ultimately have "
        \<forall>r q. \<lbrace>\<Up>(x = r+y*q)\<rbrace>
	    z\<leftarrow>iter\<^isub>D (\<lambda>x. \<up>ret(y \<le> r)) 
                     (\<lambda>x. do {r\<leftarrow>ret (r - y); q\<leftarrow>ret (1+q);ret()})
                     ()
	\<lbrace>\<Up>(x = r+y*q)\<and>\<^isub>D \<not>\<^isub>D\<Up>(y \<le> r)\<rbrace>"
	by simp
      from this have
	"\<forall>r q. \<lbrace>\<Up>(x=r+y*q)\<rbrace>
	    z\<leftarrow>while\<^isub>D \<up>ret(y \<le> r) do {
	        r\<leftarrow>ret (r - y);
	        q\<leftarrow>ret (1 + q);
	        ret ()}
         \<lbrace>\<Up>(x=r+y*q)\<and>\<^isub>D \<not>\<^isub>D\<Up>(y \<le> r)\<rbrace>"
	by (simp add: while\<^isub>D_def)
      from this show ?thesis
	by simp
    qed
  txt{*Nun muss die Schleifensequenz nur noch ange\"angt werden. 
    Dies l\"asst sich durch die erweiterte Regel f\"ur die Sequenzierung
    ohne weiteres tun.*}
  from "[5]" this show ?thesis
    by (rule seq_exp)
qed

end
