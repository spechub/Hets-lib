(* tactics for coinduction *)

fun print_term t = Sign.string_of_term (sign_of (the_context())) t

val coinduction_stack = ref ([]:(string * string) list)

fun top_trans () = 
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

fun step_fun thm = let val thms = (REPEAT (rtac disjI2 1) THEN (instantiate_tac [("R" ,top_step () ^ " union ("^top_trans () ^" ?R)" )])) thm in
                            thms end 



fun no_subgoals thm = 
       let fun count_prems (Const ("==>",_) $ _ $ t) = 1+count_prems t 
             | count_prems _ = 0 
       in count_prems(#prop(rep_thm thm))  
       end

fun get_concl (Const ("==>",_) $ _ $ t) = get_concl t
  | get_concl (Const ("all",_) $ (Abs (_,_,t))) = get_concl t
  | get_concl (Const ("Trueprop", _) $ t) = t
  | get_concl t = raise (error "tactics.ML: illegal argument for get_concl")

fun get_foralls (Const ("==>",_) $ _ $ t) = get_foralls t
  | get_foralls (Const ("all",_) $ (Abs (x,ty,t))) = (x,ty)::get_foralls t
  | get_foralls (Const ("Trueprop", _) $ t) = []
  | get_foralls t = raise (error "tactics.ML: illegal argument for get_foralls")

fun get_ctxt_thm thm = get_thm (the_context()) thm

fun get_cogeneration_axiom subgoal =
  case get_concl subgoal of
     Const ("op =",Type("fun",[ty,_])) $ t1 $ t2 => 
        (case ty of
           Type(tn,_) => let val simple_tn = implode (tl (snd (take_prefix  (fn x => x<>".") (explode tn))))
                             val xt1 =Const ("op =",dummyT) $ Free("x",dummyT) $ t1
                             val yt2 =Const ("op =",dummyT) $ Free("y",dummyT) $ t2
                             val conj = Const ("op &",dummyT) $ xt1 $ yt2
                             fun ex_quant (t,(x,ty)) = Const ("Ex",dummyT) $ (Abs (x,ty,t))
                             val eq = foldl ex_quant (conj, (get_foralls subgoal))
                         in (get_ctxt_thm ("ga_cogenerated_"^simple_tn),"Trans_"^simple_tn,eq)
                             handle _ => raise (error ("No coinduction axiom for type "^tn^" found"))
                         end
         | _ => raise (error "coinduction does not work for polymorphic types") )
   | _ => raise (error ("coinduction works only for equations, not for: "^(print_term subgoal)))



fun count_all (Const ("all",_) $ (Abs (_,_,t))) = 1+count_all t
  | count_all _ = 0

fun lambdas n = if n=0 then "" else "% s ."^lambdas (n-1)

fun force_blast_fun num thm = let val n=no_subgoals thm val thms = blast_tac (claset ()) num thm in
                            case Seq.pull thms of None => Seq.empty
                                  | Some (x,_) => if n=no_subgoals x then Seq.empty else thms end   

fun force_simp_fun num thm = let val n=no_subgoals thm val thms = Asm_full_simp_tac num thm in
                            case Seq.pull thms of None => Seq.empty
                                  | Some (x,_) => if n=no_subgoals x then Seq.empty else thms end   

fun force_simp_fun2 thm = let val n=no_subgoals thm val thms = Asm_full_simp_tac 2 thm in
                            case Seq.pull thms of None => Seq.empty
                                  | Some (x,_) => if n=no_subgoals x then Seq.empty else thms end   

fun instantiate_Rzero_fun thm = let val thms = (SUBGOAL (fn (sub,_) => instantiate_tac [("Rzero" , lambdas (count_all sub)^ "?R" )]) 1) thm in 
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

fun finish_fun thm = let val thms = ((instantiate_tac [("R" , "%x y. False" )]) THEN (solve_fun 1) THEN TRY(close_fun))
                             thm in (pop_coinduction(); thms) end

fun xy_exI_fun thm = let val thms = ((res_inst_tac [("x","x")] exI 1) THEN (res_inst_tac [("x","y")] exI 1))
                             thm in thms end

fun breakup_fun thm = let val thms = ((Asm_full_simp_tac 1) THEN (REPEAT (eatac exE 0 1 ORELSE eatac conjE 0 1)) THEN (eatac disjE 0 1))
                              thm in thms end


fun coinduction_fun thm = 
  SUBGOAL (fn (sub,_) => 
      let val (co_ax,trans,eq) = get_cogeneration_axiom sub
          val step_term = list_abs_free ([("x",dummyT),("y",dummyT)], eq)
          val br = !show_brackets
          val _ = reset show_brackets
          val step = print_term step_term
          val _ = show_brackets := br
          val step1 = "(%x. %y. "^implode (tl (tl (tl (tl (tl (tl (tl (tl (tl (explode step))))))))))^")"
          val _ = push_coinduction (trans,step1)
      in  res_inst_tac [("R","?Rzero")] co_ax 1
          THEN (instantiate_Rzero_fun) 
          THEN (step_fun)
      end) 1 thm   

