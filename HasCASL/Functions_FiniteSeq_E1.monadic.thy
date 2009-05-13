theory Functions_FiniteSeq_E1
imports "$HETS_LIB/Isabelle/MainHCPairs"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"Ax1\", \"Ax2\", \"Ax3\", \"Ax4\", \"Ax5\", \"Ax6\", \"Ax7\",
     \"Ax8\", \"Ax9\", \"Ax10\", \"Ax11\", \"Ax12\", \"Ax13\", \"Ax14\",
     \"Ax15\", \"Ax1_1\", \"Ax2_1\", \"Ax3_1\"]"

typedecl ('a1) Seq
typedecl X_Nat

consts
X0 :: "X_Nat" ("0''")
X1 :: "X_Nat" ("1''")
X2 :: "X_Nat" ("2''")
X3 :: "X_Nat" ("3''")
X4 :: "X_Nat" ("4''")
X5 :: "X_Nat" ("5''")
X6 :: "X_Nat" ("6''")
X7 :: "X_Nat" ("7''")
X8 :: "X_Nat" ("8''")
X9 :: "X_Nat" ("9''")
X__XAtXAt__X :: "X_Nat => X_Nat => X_Nat" ("(_/ @@/ _)" [54,54] 52)
X__XCaret__X :: "X_Nat => X_Nat => X_Nat" ("(_/ ^''/ _)" [54,54] 52)
X__XExclam :: "X_Nat => X_Nat" ("(_/ !'')" [58] 58)
X__XGtXEq__X :: "X_Nat => X_Nat => bool" ("(_/ >=''/ _)" [44,44] 42)
X__XGt__X :: "X_Nat => X_Nat => bool" ("(_/ >''/ _)" [44,44] 42)
X__XLtXEq__X :: "X_Nat => X_Nat => bool" ("(_/ <=''/ _)" [44,44] 42)
X__XLt__X :: "X_Nat => X_Nat => bool" ("(_/ <''/ _)" [44,44] 42)
X__XMinusXExclam__X :: "X_Nat => X_Nat => X_Nat" ("(_/ -!/ _)" [54,54] 52)
X__XMinusXQuest__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ -?/ _)" [54,54] 52)
X__XPlus__X :: "X_Nat => X_Nat => X_Nat" ("(_/ +''/ _)" [54,54] 52)
X__XSlashXQuest__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ '/?/ _)" [54,54] 52)
X__Xx__X :: "X_Nat => X_Nat => X_Nat" ("(_/ *''/ _)" [54,54] 52)
X__div__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ div''/ _)" [54,54] 52)
X__dvd__X :: "X_Nat => X_Nat => bool" ("(_/ dvd''/ _)" [44,44] 42)
X__mod__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ mod''/ _)" [54,54] 52)
X_all :: "(X_Nat => 'S partial) => ('S => bool) => bool" ("all''/'(_,/ _')" [3,3] 999)
X_concat :: "(X_Nat => 'S partial) * (X_Nat => 'S partial) => X_Nat => 'S partial"
X_empty :: "(X_Nat => 'S partial) => bool" ("empty''/'(_')" [3] 999)
X_even :: "X_Nat => bool" ("even''/'(_')" [3] 999)
X_filter :: "(X_Nat => 'S partial) => ('S => bool) => X_Nat => 'S partial"
X_finite :: "(X_Nat => 'S partial) => bool" ("finite''/'(_')" [3] 999)
X_head :: "(X_Nat => 'S partial) => 'S partial" ("head/'(_')" [3] 999)
X_length :: "(X_Nat => 'S partial) => X_Nat partial" ("length''/'(_')" [3] 999)
X_max :: "X_Nat => X_Nat => X_Nat" ("max''/'(_,/ _')" [3,3] 999)
X_minX1 :: "X_Nat => X_Nat => X_Nat" ("min''/'(_,/ _')" [3,3] 999)
X_minX2 :: "(X_Nat => bool) => X_Nat partial" ("min''''/'(_')" [3] 999)
X_nfh :: "(X_Nat => 'S partial) => 'S partial" ("nfh/'(_')" [3] 999)
X_odd :: "X_Nat => bool" ("odd''/'(_')" [3] 999)
X_pre :: "X_Nat => X_Nat partial" ("pre/'(_')" [3] 999)
X_start :: "(X_Nat => 'S partial) => X_Nat partial" ("start/'(_')" [3] 999)
X_suc :: "X_Nat => X_Nat" ("suc/'(_')" [3] 999)
nf :: "(X_Nat => 'S partial) => X_Nat => 'S partial"
nft :: "(X_Nat => 'S partial) => X_Nat => 'S partial"
tail :: "(X_Nat => 'S partial) => X_Nat => 'S partial"

axioms
Ax1 [rule_format] : "ALL Q. defOp (min''(Q)) --> (EX m. Q m)"

Ax2 [rule_format] :
"ALL Q.
 (EX m. Q m) -->
 min''(Q) =
 (if Q 0' then makePartial 0' else min''(% m. Q (m +' 1')))"

Ax3 [rule_format] : "ALL s. start(s) = min''(% m. defOp (s m))"

Ax4 [rule_format] : "ALL s. head(s) = s 0'"

Ax5 [rule_format] : "ALL s. tail s = (% x. s (x +' 1'))"

Ax6 [rule_format] : "ALL s. head(nf s) = nfh(s)"

Ax7 [rule_format] : "ALL s. tail (nf s) = nf (nft s)"

Ax8 [rule_format] :
"ALL P.
 ALL s.
 head(X_filter s P) =
 (resOp
  (head(s),
   bool2partial (defOp (head(s)) & P (makeTotal (head(s))))))"

Ax9 [rule_format] :
"ALL P. ALL s. tail (X_filter s P) = X_filter (tail s) P"

Ax10 [rule_format] :
"ALL s.
 nfh(s) = lift2partial s (start(s)) 

Ax11 [rule_format] :
"ALL s.
 nft s =
 (% k.  lift2partial s (mapPartial (X__XPlus__X (k +' 1')) (start(s))))

Ax12 [rule_format] :
"ALL s. finite'(s) = (EX X_n. ALL m. m >' X_n --> ~ defOp (s m))"

Ax13 [rule_format] : "ALL s. empty'(s) = (ALL m. ~ defOp (s m))"

Ax14 [rule_format] :
"ALL s.
 ALL t.
 head(X_concat (s, t)) = (if ~ empty'(s) then head(s) else head(t))"

Ax15 [rule_format] :
"ALL s.
 ALL t.
 tail (X_concat (s, t)) =
 (if ~ empty'(s) then X_concat (tail s, t) else tail t)"

declare Ax6 [simp]

theorem Ax1_1 :
"ALL P. ALL s. nf (X_filter s P) = X_filter (nf s) P"
by (auto)

ML "Header.record \"Ax1_1\""

theorem Ax2_1 :
"ALL P. ALL s. X_filter (X_filter s P) P = X_filter s P"
by (auto)

ML "Header.record \"Ax2_1\""

theorem Ax3_1 : "ALL s. defOp (nfh(s)) = (~ empty'(s))"
by (auto)

ML "Header.record \"Ax3_1\""

end
