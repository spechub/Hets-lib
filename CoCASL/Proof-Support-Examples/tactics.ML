(* tactics for coinduction *)

fun print_term t = Sign.string_of_term (sign_of (the_context())) t

(* the coinduction stack, holding pairs (<type>,<step>), where <type>
   is the name of the current type and where <step> is a
   string which represents the current trial relation. *)

val coinduction_stack = ref ([]:(string * string) list)

fun top_type () = 
   fst (hd(!coinduction_stack))
   handle _ => raise (error "step only applicable within coinduction proof")
fun top_step () = 
   snd (hd(!coinduction_stack))
   handle _ => raise (error "step only applicable within coinduction proof")
fun push_coinduction arg = coinduction_stack := arg::(!coinduction_stack)
fun pop_coinduction () = 
   coinduction_stack := tl(!coinduction_stack)
   handle _ => raise (error "finish only applicable within coinduction proof")

fun build_tactic tac = 
   Method.ctxt_args (fn ctxt => ((context (ProofContext.theory_of ctxt); Method.METHOD (fn facts => tac))))

(* compute current number of subgoals *)

fun no_subgoals thm = 
       let fun count_prems (Const ("==>",_) $ _ $ t) = 1+count_prems t 
             | count_prems _ = 0 
       in count_prems(#prop(rep_thm thm))  
       end

(* get the conlusion of the current theorem *)

fun get_concl (Const ("==>",_) $ _ $ t) = get_concl t
  | get_concl (Const ("all",_) $ (Abs (_,_,t))) = get_concl t
  | get_concl (Const ("Trueprop", _) $ t) = t
  | get_concl t = raise (error "tactics.ML: illegal argument for get_concl")

(* get a list of all "all"s in a theorem *)

fun get_foralls (Const ("==>",_) $ _ $ t) = get_foralls t
  | get_foralls (Const ("all",_) $ (Abs (x,ty,t))) = (x,ty)::get_foralls t
  | get_foralls (Const ("Trueprop", _) $ t) = []
  | get_foralls t = raise (error "tactics.ML: illegal argument for get_foralls")

fun force_fun tac thm = let val n=no_subgoals thm val thms = tac thm in
                            case Seq.pull thms of None => Seq.empty
                                  | Some (x,_) => if n<=no_subgoals x then Seq.empty else thms end  

fun get_ctxt_thm thm = get_thm (the_context()) thm

(* get the current cogeneration axiom, the name of the current type
   and the goal of the current proof *)

fun get_coinduction_data subgoal =
  case get_concl subgoal of
     Const ("op =",Type("fun",[ty,_])) $ t1 $ t2 => 
        (case ty of
           Type(tn,_) => let val simple_tn = implode (tl (snd (take_prefix  (fn x => x<>".") (explode tn))))
                             val quant_vars = get_foralls subgoal
                             fun mk_free (x,_) = Free(x,dummyT)
                             val u1 = Term.subst_bounds (map mk_free quant_vars,t1)
                             val u2 = Term.subst_bounds (map mk_free quant_vars,t2)
                             val xt1 = "x="^print_term u1
                             val yt2 = "y="^print_term u2
                             val conj = xt1^" & "^yt2
                             fun ex_quant (t,(x,ty)) = "? "^x^". "^t
                             val eq = foldl ex_quant (conj, quant_vars)
                         in (get_ctxt_thm ("ga_cogenerated_"^simple_tn),simple_tn,eq)
                             handle _ => raise (error ("No coinduction axiom for type "^tn^" found"))
                         end
         | _ => raise (error "coinduction does not work for polymorphic types") )
   | _ => raise (error ("coinduction works only for equations, not for: "^(print_term subgoal)))

fun get_exI_varname subgoal =
  case get_concl subgoal of
     Const ("Ex",_) $ (Abs (x,ty,t)) => x      
         | _ => "error"

fun count_all (Const ("all",_) $ (Abs (_,_,t))) = 1+count_all t
  | count_all _ = 0

fun lambdas n = if n=0 then "" else "% s ."^lambdas (n-1)

fun force_blast_fun num thm = let val thms = force_fun (blast_tac (claset ()) num) thm in thms end 

fun force_simp_fun num thm = let val thms = force_fun (Asm_full_simp_tac num) thm in thms end   

(* step_fun tries to apply "rtac disjI2" repeatedly as often as possible
   and afterwards gets the current trial relation <Rt> and the current
   type <type> from the coinduction stack. the variable
   <?R_type> is then instantiated with "<Rt> union <trans_type><?R_type>". *)

fun step_fun thm = let val thms = (REPEAT (rtac disjI2 1) THEN (instantiate_tac [("R_"^top_type() , top_step () ^ " union (Trans_"^top_type () ^" ?R_"^ top_type ()^")" )])) thm in  thms end 

fun instantiate_Rzero_fun thm = let val thms = (SUBGOAL (fn (sub,_) => instantiate_tac [("Rzero_"^top_type() , lambdas (count_all sub)^ "?R_"^top_type() )]) 1) thm in 
                            thms end

fun solve_fun num thm = let val thms = (
                                     (
                                       (REPEAT ((eatac exE 0 num ORELSE rtac conjI num) ORELSE eatac conjE 0 num))
                                       THEN TRY (Asm_full_simp_tac num)
                                     )
                                     THEN 
                                     (
                                       (REPEAT ((eatac exE 0 num ORELSE rtac conjI num) ORELSE eatac conjE 0 num))
                                       THEN TRY (Asm_full_simp_tac num)
                                     )
                                   )
                            thm in thms end

fun init_fun thm = let val thms = (TRY((force_simp_fun 2) ORELSE ((solve_fun 2) THEN (REPEAT(rtac disjI1 2)) THEN (blast_tac (claset ()) 2)))
                                   THEN (REPEAT (rtac allI 1 ORELSE rtac impI 1)))
                           thm in thms end

fun close_fun thm = let val thms = ((REPEAT (rtac disjI1 1 ORELSE rtac disjI2 1) THEN REPEAT (eatac exE 0 1 ORELSE eatac conjE 0 1) THEN (force_simp_fun 1))                                   ORELSE
                                   (((solve_fun 1) THEN (rtac disjI1 1)) THEN (force_blast_fun 1)))
                            thm in thms end

fun force_finish_fun thm = let val n=no_subgoals thm val thms = ((instantiate_tac [("R_"^top_type () , "%x y. False" )]) THEN (solve_fun 1) THEN TRY(close_fun)) thm in
                            case Seq.pull thms of None => Seq.empty
                                  | Some (x,_) => if n=no_subgoals x then Seq.empty else (pop_coinduction();thms) end  

fun exI_fun thm = SUBGOAL (fn (sub,_) => res_inst_tac [("x",(get_exI_varname(sub)))] exI 1 ) 1 thm

fun xy_exI_fun thm = let val thms = ((res_inst_tac [("x","x")] exI 1) THEN (res_inst_tac [("x","y")] exI 1))
                             thm in thms end


fun breakup_fun thm = let val thms = ((Asm_full_simp_tac 1) THEN (REPEAT (eatac exE 0 1 ORELSE eatac conjE 0 1)) THEN (eatac disjE 0 1))
                              thm in thms end

fun close_or_step_fun thm = let val thms =  (((rtac disjI2 1) THEN (Force_tac 1))
                                            ORELSE (close_fun)
                                            ORELSE ((solve_fun 1) THEN ((close_fun)
                                            ORELSE (TRY ((rtac conjI 1) THEN (Asm_full_simp_tac 1)) THEN (step_fun) THEN (xy_exI_fun)
                                            THEN ((TRY(rtac conjI 1) THEN (force_simp_fun 1) THEN REPEAT (force_simp_fun 1)) ORELSE
                                            (((rtac conjI 1) THEN (rtac disjI2 1)) THEN REPEAT((exI_fun) THEN (exI_fun) THEN
                                            (((rtac conjI 1) THEN (force_simp_fun 1) THEN REPEAT (force_simp_fun 1)) ORELSE
                                            ((rtac conjI 1) THEN (rtac disjI2 1)))))))))
                                            THEN (TRY(REPEAT(rtac disjI1 1) THEN (blast_tac (claset ()) 1 ) THEN (close_fun))))
                              thm in thms end

fun coinduction_fun thm = 
  SUBGOAL (fn (sub,_) => 
      let val (co_ax,tn,eq) = get_coinduction_data sub
          val step =  "(%x. %y. "^eq^")"
          (* filter out special Isar characters *)
          val trial = implode (filter (fn c => not (ord c mem [232,236])) (explode step)) 
          (* put new values of trans and step on the stack *)
          val _ = push_coinduction (tn,trial)
      in  res_inst_tac [("R","?Rzero_"^top_type ())] co_ax 1
          THEN (instantiate_Rzero_fun) 
          THEN (step_fun)
      end) 1 thm   

fun coinduction_test_fun thm = 
  SUBGOAL (fn (sub,_) => 
      let val (co_ax,tn,eq) = get_coinduction_data sub
          val step =  "(%x. %y. "^eq^")"
          (* filter out special Isar characters *)
          val trial = implode (filter (fn c => not (ord c mem [232,236])) (explode step)) 
          (* put new values of type and step on the stack *)
          val _ = push_coinduction (tn,trial)
      in  res_inst_tac [("R","?Rzero_"^top_type ())] co_ax 1
         (* THEN (instantiate_Rzero_fun) 
          THEN (step_fun)*)
      end) 1 thm

fun circular_coinduction_fun thm = let val thms = ((coinduction_fun) THEN (init_fun) THEN DEPTH_SOLVE(TRY (breakup_fun) THEN TRY(close_or_step_fun) THEN TRY(force_finish_fun)))
                                       thm in thms end







(*

olde:
=====

fun close_or_step_fun_old thm = let val thms = (((rtac disjI2 1) THEN (Force_tac 1)) ORELSE (close_fun) ORELSE ((solve_fun 1) THEN ((close_fun) ORELSE ((step_fun) THEN TRY (solve_fun 1) THEN TRY (rtac disjI2 1) THEN TRY (solve_fun 1) THEN TRY (xy_exI_fun) THEN (solve_fun 1) THEN TRY (close_fun)) THEN (TRY(REPEAT(rtac disjI1 1) THEN (blast_tac (claset ()) 1 ) THEN (close_fun))))))
                              thm in thms end

fun heavy_fun thm = let val thms = (((step_fun) THEN (solve_fun 1) THEN (rtac disjI2 1) THEN (solve_fun 1) THEN (xy_exI_fun) THEN (rtac conjI 1) THEN (rtac disjI2 1) THEN (uv_exI_fun) THEN (solve_fun 1) THEN (Force_tac 1) THEN (close_fun)) THEN TRY (close_fun))
                              thm in thms end

fun heavy_test_fun thm = let val thms = (force_fun(close_or_step_fun) ORELSE force_fun(heavy_fun))
                              thm in thms end

*)