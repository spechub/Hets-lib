signature HCTacSig =
sig
  val my_tac : thm -> tactic
end

structure HCTactic =
struct

fun isDefOp (Const ("defOp",_)) = true
  | isDefOp _ = false

fun isDefOpAppl (a $ _) = isDefOp a
  | isDefOpAppl _ = false

fun getDefOpNum' n [] = 0
  | getDefOpNum' n (x::xs) =
     if isDefOpAppl x then n else getDefOpNum' (n+1) xs

fun getDefOpNum l = getDefOpNum' 1 l

fun strip_trueprop (Const ("Trueprop",_) $ t) = t
  | strip_trueprop (Const ("Goal",_) $ t)     = t
  | strip_trueprop t                          = t

fun strip_all (Const ("all",_) $ Abs (_,_,t)) = t
  | strip_all t                               = t

fun strip_impl (Const ("==>",_) $ _ $ t) = strip_impl t
  | strip_impl t                         = t

val strip_meta = strip_all o strip_trueprop o strip_impl o strip_all

fun get_assums' l (Const ("==>",_) $ t $ u) = get_assums' (l@[t]) u 
  | get_assums' l t                         = l

fun get_assums t = 
  let
    val l = get_assums' [] t
  in
    map strip_trueprop l
  end

fun get_assumNum th =
  let
    val l = (get_assums o strip_meta o List.nth) (0, prems_of th)   
  in
    getDefOpNum l
  end

fun my_tac opThm ntimes asm th =
  let
(*    val opThm = thm opThmName *)
   val npremsTh = nprems_of th
    val sset = ((simpset()) delsimps (thms "pair.simps" @ thms "app.simps" @
                thms "apt.simps" @ thms "defOp.simps")) addsimps [opThm]
    val first = (dresolve_tac [thm "defArg"] 1) THEN
                (eresolve_tac [exE] 1)
    fun simp t = generic_simp_tac false (asm, true, asm) sset 1 t
    fun pullFirst t = fst ((the o Seq.pull) (first t))
    fun firstStep n t = if (n = 1) then (first t)
                          else firstStep (n-1) (pullFirst t)
    val firstTh = firstStep ntimes th
    val (th'',_) = (the o Seq.pull) (firstTh)
    val (th',_) = (the o Seq.pull) (simp th'')
    val npremsTh' = nprems_of th'
    val nr = (get_assumNum th') - 1
    fun second n = (rotate_tac n 1) THEN
                 (dresolve_tac [sym] 1)
    fun pullSecond n t = fst ((the o Seq.pull) (second n t))
    fun secondStep n m t = if (n = 1) then second m t
                           else secondStep (n-1) (m-1) (pullSecond m t)
    val (th''',_) = (the o Seq.pull) (secondStep ntimes nr th')
  in
    if (npremsTh = npremsTh') then simp th''' else simp th''
  end

end
