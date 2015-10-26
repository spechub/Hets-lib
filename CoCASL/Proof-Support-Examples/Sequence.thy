theory Sequence = Main:

ML"fun no_subgoals thm = \
       let fun count_prems (Const (\"==>\",_) $ _ $ t) = 1+count_prems t  \
             | count_prems _ = 0 \
       in count_prems(#prop(rep_thm thm))  \
       end"

ML"fun build_tactic tac = \
   Method.ctxt_args (fn ctxt => ((context (ProofContext.theory_of ctxt); Method.METHOD (fn facts => tac))))"

ML"fun force_simp_fun thm = let val n=no_subgoals thm val thms = Asm_full_simp_tac 1 thm in \
                            case Seq.pull thms of None => Seq.empty \
                                  | Some (x,_) => if n=no_subgoals x then Seq.empty else thms end"      

ML"fun init2_fun thm = let val thms = (REPEAT (rtac allI 1 ORELSE rtac impI 1)) thm in \
                            thms end"

ML"fun solve_fun thm = let val thms = (((REPEAT ((eatac exE 0 1 ORELSE rtac conjI 1) ORELSE eatac conjE 0 1)) THEN TRY (Asm_full_simp_tac 1)) THEN ((REPEAT ((eatac exE 0 1 ORELSE rtac conjI 1) ORELSE eatac conjE 0 1)) THEN TRY (Asm_full_simp_tac 1))) thm in \
                            thms end"

ML"fun init_fun thm = let val thms = (TRY((Asm_full_simp_tac 1) ORELSE ((solve_fun) THEN (blast_tac (claset ()) 1))) THEN (init2_fun)) thm in \
                            thms end"

ML"fun close_fun thm = let val thms = (REPEAT (rtac disjI1 1 ORELSE rtac disjI2 1) THEN REPEAT (eatac exE 0 1 ORELSE eatac conjE 0 1) THEN (force_simp_fun)) thm in \
                            thms end"
ML"fun step_fun thm = let val thms = (REPEAT (rtac disjI2 1) THEN (instantiate_tac [(\"R\" , \"Rcs union (Trans ?R)\" )])) thm in \
                            thms end" 

ML"fun xy_exI_fun thm = let val thms = ((res_inst_tac [(\"x\",\"x\")] exI 1) THEN (res_inst_tac [(\"x\",\"y\")] exI 1)) thm in \
                            thms end" 

ML"fun close_or_step_fun thm = let val thms = ((close_fun) ORELSE ((solve_fun) THEN ((close_fun) ORELSE ((step_fun) THEN TRY (solve_fun) THEN TRY (rtac disjI2 1) THEN TRY (solve_fun) THEN TRY (xy_exI_fun) THEN (solve_fun) THEN TRY (close_fun))))) thm in \
                           thms end"

ML"fun finish_fun thm = let val thms = ((instantiate_tac [(\"R\" , \"(BinRelImage tl (%x y. False))\" )]) THEN (solve_fun) THEN TRY(close_fun)) thm in \
                            thms end" 

ML"fun breakup_fun thm = let val thms = ((Asm_full_simp_tac 1) THEN (REPEAT (eatac exE 0 1 ORELSE eatac conjE 0 1)) THEN (eatac disjE 0 1)) thm in \
                            thms end" 

ML"fun solveb_fun thm = let val thms = (TRY (Asm_full_simp_tac 2)) thm in \
                            thms end" 

method_setup force_simp = "build_tactic (force_simp_fun)" "simp + check if no_subgoal changed"
method_setup init = "build_tactic (init_fun)" "(simp|(solve,blast))?,init2_fun?"
method_setup init2 = "build_tactic (init2_fun)" "((allI|impI)+)?"
method_setup solve= "build_tactic (solve_fun)" "((exE|conjE|conjI)+)?,(simp)?,((exE|conjE|conjI)+)?,(simp)?"
method_setup close= "build_tactic (close_fun)" "((disjI1|disjI2)+)?,((exE|conjE)+)?,force_solve"
method_setup close_or_step= "build_tactic (close_or_step_fun)" "close|(solve,(close|(step,solve?,disjI2?,solve?,xy_exi?,solve,close?)))"
method_setup solveb= "build_tactic (solveb_fun)" "(simp)?"
method_setup finish = "build_tactic (finish_fun)" "inst r false,solve1"
method_setup step = "build_tactic (step_fun)" "((disjI2)+)?,inst r (rcs union (trans r))"
method_setup breakup = "build_tactic (breakup_fun)" "simp,((exE|conjE)+)?,disjE"
method_setup xy_exI = "build_tactic (xy_exI_fun)" "rule_tac x=x in exI, rule_tac x=y n exI"

typedecl "Elem"
typedecl "Sequence"
typedecl "Unit"
consts
"unit" :: "Unit"
"nil" :: "Unit => Sequence"
"cons" :: "Elem => Sequence => Sequence"
"hd" :: "Sequence => Elem"
"tl" :: "Sequence => Sequence"
"stop" :: "Sequence => Unit"
"conc" :: "Sequence => Sequence => Sequence"
"map" :: "(Elem => Elem) => Sequence => Sequence"
"iterate" :: "(Elem => Elem) => Elem => Sequence"

consts
  BinRelImage :: "('a => 'b) => ('a => 'a => bool) => ('b => 'b => bool)"
  Trans :: "('a => 'a => bool) => ('b => 'b => bool)"
  union :: "('a => 'a => bool)  => ('a => 'a => bool) => ('a => 'a => bool)" (infixl 20)
defs
  BinRelImage_def [simp] : "BinRelImage f R == %x y . EX u v . R u v & x = f u & y = f v"
  Trans_def [simp] : "Trans R == (BinRelImage tl R)"
  union_def [simp] : "R union S == % x y . R x y | S x y"

axioms
map_hd [simp]:  "!! f :: Elem => Elem . !! s :: Sequence . !! a :: Elem . (hd s)=a ==> (hd (map f s)) = (f a)"
map_tl [simp]:  "!! f :: Elem => Elem . !! s1 :: Sequence . !! s2 :: Sequence . (tl s1)=s2 ==> (tl (map f s1)) = (map f s2)"
map_stop [simp]:  "!! f :: Elem => Elem . !! s :: Sequence .  (stop s)=unit ==> (stop (map f s)) = unit"
iterate_hd [simp]:  "!! f :: Elem => Elem . !! a :: Elem . (hd (iterate f a)) = (f a)"
iterate_tl [simp]:  "!! f :: Elem => Elem . !! a :: Elem . (tl (iterate f a)) = (iterate f (f a))"
conc_hd_1 [simp]: "!! s1 :: Sequence . !! s2 :: Sequence . !! a :: Elem . (hd s1)=a ==> hd(conc s1 s2)=a"
conc_hd_2 [simp]: "!! s1 :: Sequence . !! s2 :: Sequence . !! b :: Elem . (stop s1)=unit & (hd s2)=b  ==> hd(conc s1 s2)=b"
conc_tl_1 [simp]: "!! s1 :: Sequence . !! s2 :: Sequence . !! s3 :: Sequence . (tl s1)=s3 ==> tl(conc s1 s2)=(conc s3 s2)"
conc_tl_2 [simp]: "!! s1 :: Sequence . !! s2 :: Sequence . !! s4 :: Sequence . (stop s1)=unit & (tl s2)=s4  ==> tl(conc s1 s2)=s4"
conc_stop [simp]: "!! s1 :: Sequence . !! s2 :: Sequence . (stop s1)=unit & (stop s2)=unit ==> stop(conc s1 s2)=unit"

ga_cogenerated_Sequence: "!! R :: Sequence => Sequence => bool . !! u :: Sequence . !! v :: Sequence . ! x :: Sequence . ! y :: Sequence . ((R x) y) --> ((hd x = hd y) & ((R (tl x)) (tl y)))  ==> ((R u) v) ==> u = v"
ga_selector_hd: "!! X1 :: Elem . !! X2 :: Sequence . (hd (cons X1 X2)) = X1"
ga_selector_tl: "!! X1 :: Elem . !! X2 :: Sequence . (tl (cons X1 X2)) = X2"
ga_selector_stop: "!! X1 :: Elem . !! X2 :: Sequence . (stop (nil(unit))) = unit"


consts Ri :: "[Sequence, Sequence] => bool"
defs Ri_def [simp] : "Ri == % x y . ( ? f a . x = (map f (iterate f a)) & y = (iterate f (f a)))"

theorem Sequence_map_iterate: "!! f :: (Elem => Elem) . !! a :: Elem . map f (iterate f a) = iterate f (f a)"
apply(rule_tac R="?Rzero" in ga_cogenerated_Sequence)
apply(tactic "instantiate_tac [(\"Rzero\" , \"% s1 s2. Ri union (Trans ?R)\" )]")
defer
apply(solve)
apply(blast)
apply(init2)

apply(breakup)

apply(solve)
apply(rule disjI1)
apply(blast)

apply(finish)

done

consts R0 :: "[Sequence, Sequence] => bool"
defs R0_def [simp] : "R0 == % x y . ( ? s1 s2 s3 . x = (conc (conc s1 s2) s3) & y = (conc s1 (conc s2 s3)) )"

theorem Sequence_Conc: "!! s1 :: Sequence . !! s2 :: Sequence . !! s3 :: Sequence . conc (conc s1 s2) s3 = conc s1 (conc s2 s3)"
apply(rule_tac R="?Rzero" in ga_cogenerated_Sequence)
apply(tactic "instantiate_tac [(\"Rzero\" , \"% s1 s2 s3. R0 union (Trans ?R)\" )]")
defer
apply(solve)
apply(blast)
apply(init2)

apply(breakup)

apply(solve)
apply(rule disjI1)
apply(blast)

apply(finish)

done

end