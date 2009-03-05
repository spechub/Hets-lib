theory MainHCPlus
imports Main
uses "$HETS_LIB/Isabelle/HCTactic"
begin

(* Operator definitions for encoding *)
consts app :: "('a => 'b option) option => 'a option => 'b option"
primrec
  "app None a = None"
  "app (Some f) x = (case x of
                            None => None
                          | Some x' => f x')"

consts apt :: "('a => 'b) option => 'a option => 'b option"
primrec
  "apt None a = None"
  "apt (Some f) x = (case x of
                            None => None
                          | Some x' => Some (f x'))"

consts pApp :: "('a => bool) option => 'a option => bool"
primrec
  "pApp None a = False"
  "pApp (Some f) x = (case x of
                             None => False
                           | Some x' => True)"


consts defOp :: "'a option => bool"
primrec
  "defOp (Some x) = True"
  "defOp None     = False"


consts pair :: "'a option => 'b option => ('a * 'b) option"
primrec
  "pair None a = None"
  "pair (Some x) z = (case z of
                             None => None
                           | Some y => Some (x,y))"


(* Deductions rules of the paritial lambda calculus *)
theorem var: "defOp (Some x)"
apply auto
done

theorem st: "defOp (app (Some f) a) ==> defOp a"
apply auto
apply (case_tac "a = None")
apply auto
done

theorem unit: "Some (x::unit) = Some ()"
apply (auto)
done

theorem symSome: "Some a = Some b ==> Some b = Some a"
apply auto
done

theorem tr: "Some a = Some b & Some b = Some c
               ==> Some a = Some c"
apply auto
done

theorem cong: "Some a = Some b
                 ==> app (Some f) (Some a)
                       = app (Some f) (Some b)"
apply auto
done

theorem ax: "((defOp a --> phi) & defOp a) ==> phi"
apply auto
done

theorem sub: "(!! y::'t . phi (Some y) ==> psi (Some y))
                 ==> phi a
                    ==> defOp a
                       ==>  psi a"
apply (case_tac a)
apply auto
done

theorem eta: "Some (% y::'t . app (Some x) (Some y))
                = Some x"
apply auto
done

theorem beta: "app (Some (% y::'t . a y)) (Some x) =  a x"
apply auto
done

theorem xi: "(!! y::'t . a y = b y)
                ==> Some (% y::'t . a y)
                      = Some (% y::'t . b y)"
apply auto
done

(* Proof rules *)

theorem defArg: "defOp a ==> (? y . a = (Some y))"
apply (case_tac a)
apply auto
done

theorem seqI: "(defOp a ==> a = b ) ==> (defOp b ==> defOp a) ==> a = b"
apply (case_tac a)
apply auto
apply (case_tac b)
apply (auto)
done

theorem stApt: "defOp (apt f a) ==> defOp a"
apply (case_tac "a = None")
apply auto
apply (case_tac "f = None")
apply auto
done

theorem stApt2: "defOp (apt f a) ==> defOp f"
apply (case_tac "f = None")
apply auto
done

theorem pairFst: "defOp (pair x y) ==> defOp x"
apply (case_tac x)
apply auto
done

theorem pairSnd: "defOp (pair x y) ==> defOp y"
apply (case_tac y)
apply auto
apply (case_tac x)
apply auto
done


theorem sub_simple: "(!!y::'t . P (Some y)) ==> defOp a ==> P a"
apply (case_tac a)
apply auto
done

theorem total: "!! a::'s =>'t . !! b::'s option . defOp b ==> defOp (apt (Some a) b)"
apply (case_tac b)
apply auto
done

theorem s_cong: "a = b
                 ==> app f a = app f b"
apply auto
done

theorem pair: "defOp a ==> defOp b ==> defOp (pair a b)"
apply (case_tac a)
apply auto
apply (case_tac b)
apply auto
done

theorem s_sub: "(!! (y::'s). app (Some a) (Some y) = app (Some b) (Some y))
                 ==> defOp c
                    ==> app (Some a) c = app (Some b) c"
apply auto
apply (case_tac c)
apply auto
done

end
