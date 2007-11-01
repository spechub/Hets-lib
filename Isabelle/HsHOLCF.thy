theory HsHOLCF
imports "$ISABELLE_HOME/src/HOLCF/IOA/meta_theory/Abstraction"
"$ISABELLE_HOME/src/HOL/Complex/Complex"
begin

(** types Bool and Ordering **)

domain lBool = FALSE | TRUE
domain lOrdering = LT | EQ | GT

(** type bounded Int **)

constdefs
minB :: int
"minB == -2147483648"
maxB :: int
"maxB == 21474836487"

typedef boundInt = "{x::int. minB <= x & x <= maxB}"
apply (rule_tac x=0 in exI)
apply (unfold minB_def maxB_def)
apply auto
done

types
unitT       = "unit lift"
integerT    = "int lift"
ratT        = "rat lift"
charT       = "char lift"
intT        = "boundInt lift" 

(* class declarations *)

axclass BoundedH < type
axclass Eq < pcpo
axclass Num < Eq
axclass Ord < Eq
axclass Enum < pcpo

(* Bounded *)

consts 
minBound :: "'a::BoundedH"
maxBound :: "'a::BoundedH"

instance unit :: BoundedH ..
instance boundInt :: BoundedH ..
instance lOrdering :: BoundedH ..
instance lBool :: BoundedH ..
instance lift :: (BoundedH) BoundedH ..
instance char :: BoundedH ..
 
defs
lBool_minBound_def: "minBound == FALSE"
lBool_maxBound_def: "maxBound == TRUE"
unit_minBound_def: "minBound == ()"
unit_maxBound_def: "maxBound == ()"
boundInt_minBound_def: "minBound == Abs_boundInt minB"
boundInt_maxBound_def: "maxBound == Abs_boundInt maxB"
lOrdering_minBound_def: "minBound == LT"
lOrdering_maxBound_def: "maxBound == GT"
lift_minBound_def: "minBound == Def minBound"
lift_maxBound_def: "maxBound == Def maxBound"
(*
problem with char -
char_minBound_def: "minBound == ??"
char_maxBound_def: "maxBound == ??"
*)

(**** lifted function types ****)

defaultsort pcpo

domain 'a Lift = Lift (lazy 'a)

types  ('a, 'b) "-->"    = "('a -> 'b) Lift" (infixr 0)

constdefs
  liftedApp :: "('a --> 'b) => ('a => 'b)" ("_$$_" [999,1000] 999)
                                                (* application *)
  "liftedApp f x == case f of
                     Lift $ g => g $ x"
constdefs
  liftedLam :: "('a => 'b) => ('a --> 'b)" (binder "Lam " 10)
                                                (* abstraction *)
  "liftedLam f == Lift $ (LAM x . f x)"

lemmas Lift.rews [simp]

lemma cont2cont_liftedApp [simp]:
  "[| cont f; cont t |] ==> cont (%x. f x $$ (t x))"
  apply (simp add: liftedApp_def)
done

lemma cont2cont_liftedLam [simp]:
  "[| !!x. cont (%y. c x y); !!y. cont (%x. c x y) |]
   ==> cont (%x. Lam y. c x y)"
  apply (simp add: liftedLam_def)
  done

lemma beta[simp] : "cont t ==> (Lam x . t x) $$ u = t u "
by (auto simp add: liftedApp_def liftedLam_def)

lemma beta2_cfun:
  "(ALL x. cont (f x)) --> cont (%w1. (LAM w2. f w1 w2)) --> 
                        (LAM w1 w2. f w1 w2) $ z1 $ z2 = f z1 z2"
apply auto
done


(* lifting of HOL to HOLCF *)

constdefs
fliftbin ::
"('a => 'b => 'c) => ('a lift -> 'b lift -> 'c lift)"
"fliftbin f == flift1 (%x. flift2 (f x))"

fliftbinA ::
"(('a::pcpo) => ('b::pcpo) => ('c::type)) => ('a -> 'b -> 'c lift)"
"fliftbinA f == LAM y. (LAM x. (Def (f y x)))"

(* lifting and unlifting between HOLCF and Hs *)

constdefs
  lifted2cont :: "('a --> 'b) => ('a -> 'b)"
  "lifted2cont f == LAM x . f $$ x"
  cont2lifted :: "('a -> 'b) => ('a --> 'b)"
  "cont2lifted f == Lam x . f $ x"
  cont2lifted2 :: "('a -> 'b -> 'c) => ('a --> 'b --> 'c)"
  "cont2lifted2 f == Lam x . Lam y. f $ x $ y"

(* lifting of HOL to Hs *)

constdefs
llift2 :: "('a::type => 'b::type) => ('a lift --> 'b lift)"
"llift2 f == cont2lifted (flift2 f)"

lliftbin ::
"('a::type => 'b::type => 'c::type) => ('a lift --> 'b lift --> 'c lift)"
"lliftbin f == cont2lifted2 (flift1 (%x. flift2 (f x)))"


(*** lazy products ***)

domain ('a,'b) lprod = lpair (lazy lfst :: 'a) (lazy lsnd :: 'b)

(* lifted constructors and selectors *)
constdefs
  llpair :: "'a --> 'b --> ('a,'b) lprod"
  "llpair == cont2lifted2 lpair"
  llfst :: "('a, 'b) lprod --> 'a"
  "llfst == cont2lifted lfst"
  llsnd :: "('a, 'b) lprod --> 'b"
  "llsnd == cont2lifted lsnd"


(*** lazy sum ***)

domain ('a,'b) lEither = lLeft (lazy 'a) | lRight (lazy 'b)

constdefs
llLeft :: "'a --> ('a,'b) lEither"
"llLeft == cont2lifted lLeft"
llRight :: "'b --> ('a,'b) lEither"
"llRight == cont2lifted lRight"

(*** maybe ***)

domain 'a lMaybe = lNothing | lJust (lazy 'a)

constdefs
llJust :: "'a --> 'a lMaybe"
"llJust == cont2lifted lJust"

(*** lazy lists ***)

domain 'a llist = lNil | "###" (lazy lHd :: 'a)
                       (lazy lTl :: "'a llist") (infixr 65)

(* lifted constructors and selectors *)
constdefs
  llCons :: "'a --> 'a llist --> 'a llist"
  "llCons == cont2lifted2 (op ###)"
  llHd :: "'a llist --> 'a"
  "llHd == cont2lifted lHd"
  llTl :: "'a llist --> 'a llist"
  "llTl == cont2lifted lTl"

lemmas llCons_def [simp]

(* lift lists to Hs *)
constdefs
list2llist :: "'a list => 'a llist"
"list2llist s == foldr (%x y. x ### y) s lNil"
liftList :: "'a list => ('a lift) llist"
"liftList s == list2llist (map Def s)"

types lString = "charT llist"

(*** lifted Boolean operators ***)

consts
andH  :: "lBool --> lBool --> lBool"
orH   :: "lBool --> lBool --> lBool"
notH  :: "lBool --> lBool"
ifteH :: "lBool --> 'c --> 'c --> 'c"
ttr   :: "lBool -> tr"

defs
andH_def :
"andH == Lam x. (Lam y. case x of
                   FALSE => FALSE |
                   TRUE => y)"
orH_def :
"orH == 
Lam x. (Lam y. case x of
                   FALSE => y |
                   TRUE => TRUE)"
notH_def :
"notH == 
Lam x. case x of
          FALSE => TRUE |
          TRUE => FALSE"
 
syntax  "@IFTE"        :: "lBool=>'c=>'c=>'c" 
                                    ("(3IF _/ (THEN _/ ELSE _) FI)" 60)
        "@AND"      :: "lBool => lBool => lBool" ("_ AND _" [36,35] 35)
        "@OR"       :: "lBool => lBool => lBool" ("_ OR _"  [31,30] 30)
 
translations 
             "x AND y" == "andH$$x$$y"
             "x OR y"  == "orH$$x$$y"
             "IF b THEN e1 ELSE e2 FI" == "ifteH$$b$$e1$$e2"

defs 
ttr_def: "ttr == LAM x. case x of  
                FALSE  => FF
              | TRUE => TT"
ifteH_def: "ifteH == Lam a x y. If (ttr $ a) then x else y fi"


(***** CLASSES *****)

(**** Bounded ****)

instance lprod :: ("{BoundedH,pcpo}","{BoundedH,pcpo}") BoundedH ..

defs
lprod_minBound_def: "minBound::('a::{BoundedH,pcpo},'b::{BoundedH,pcpo}) 
                       lprod == lpair $ (minBound::'a) $ (minBound::'b)"
lprod_maxBound_def: "maxBound::('a::{BoundedH,pcpo},'b::{BoundedH,pcpo}) 
                       lprod == lpair $ (maxBound::'a) $ (maxBound::'b)"


(**** Equality ****)

(*** equality - declarations ***)

consts
eqH  :: "'a::Eq --> 'a --> lBool"
neqH :: "'a::Eq --> 'a --> lBool"

consts
eqD ::  "'a::Eq --> 'a --> lBool"
neqD :: "'a::Eq --> 'a --> lBool"

fixrec (permissive)
   "(eqD :: 'a::Eq --> 'a --> lBool) = 
             (Lam x. (Lam y. (notH $$ (neqD $$ x $$ y))))"
and    
   "(neqD :: 'a::Eq --> 'a --> lBool) = 
               (Lam x. (Lam y. (notH $$ (eqD $$ x $$ y))))"
(* mutually recursive definition *) 

constdefs
eqHDF ::  "'a::Eq --> 'a --> lBool"
"eqHDF == Lam x y. notH $$ (neqH $$ x $$ y)"
neqHDF :: "'a::Eq --> 'a --> lBool"
"neqHDF == Lam x y. notH $$ (eqH $$ x $$ y)"
(* used to translate one function when the other is defined *)

(*** equality - instantiations ***)

axclass PEq < type
 
instance unit :: PEq ..
instance int :: PEq ..
instance boundInt :: PEq ..
instance rat :: PEq ..
instance char :: PEq ..

instance lBool :: Eq ..
instance lOrdering :: Eq ..
instance lift :: (PEq) Eq .. 
instance llist :: (Eq) Eq ..
instance lprod :: (Eq, Eq) Eq .. 
instance lEither :: (Eq,Eq) Eq .. 
instance lMaybe :: (Eq) Eq ..

axclass PNum < type

instance int :: PNum ..
instance boundInt :: PNum ..

instance lift :: ("{PEq,PNum}") Num ..

instance lBool :: Ord ..
instance lOrdering :: Ord ..
instance lift :: (PEq) Ord .. 
instance llist :: (Ord) Ord ..
instance lprod :: (Ord,Ord) Ord .. 
instance lEither :: (Ord,Ord) Ord .. 
instance lMaybe :: (Ord) Ord ..

instance lBool :: Enum ..
instance lOrdering :: Enum ..
instance lift :: (PEq) Enum ..  


(*** equality - auxiliary functions ***)

(** for ground types **)

constdefs
eqHI  :: "'a::Eq --> 'a --> lBool"
"eqHI == Lam x y. If Def (x = y) then TRUE else FALSE fi"
neqHI :: "'a::Eq --> 'a --> lBool"
"neqHI == neqHDF"
(* used to translate built-in ground types and 
   derived instances *)


(** for type constructors **)

constdefs
eqLP :: "('a::Eq,'b::Eq) lprod --> ('a,'b) lprod --> lBool"
"eqLP == Lam x y. andH $$ (eqH $$ (lfst $ x) $$ (lfst $ y))  
        $$ (eqH $$ (lsnd $ x) $$ (lsnd $ y))"
eqLS :: "('a::Eq,'b::Eq) lEither --> ('a,'b) lEither --> lBool"
"eqLS == Lam x y. case x of
    lLeft $ w  => case y of 
        lLeft $ z   => eqH $$ w $$ z
      | lRight $ z  => FALSE
  | lRight $ w => case y of
        lLeft $ z   => FALSE
      | lRight $ z  => eqH $$ w $$ z"
eqLM :: "('a::Eq) lMaybe --> 'a lMaybe --> lBool"
"eqLM == Lam x y. case x of
    lNothing  => case y of 
        lNothing   => TRUE
      | lJust $ z    => FALSE
  | lJust $ w => case y of
        lNothing   => FALSE
      | lJust $ z    => eqH $$ w $$ z"

consts 
eqLL :: "('a::{pcpo,Eq}) llist --> 'a llist --> lBool"

fixrec (permissive)
"eqLL = (Lam (x::('a::{pcpo,Eq}) llist). 
   (Lam (y::('a::{pcpo,Eq}) llist). case x of
        lNil => (case y of 
                lNil      => TRUE
              | ((op ###) $ z $ zs) => FALSE)      
         | ((op ###) $ w $ ws)  => (case y of
                lNil => FALSE
              | ((op ###) $ z $ zs) => 
                     (andH $$ (eqH $$ w $$ z)  
                           $$ (eqLL $$ ws $$ zs)))))"


(*** equality - method definition ***)

defs
lBool_eqH_def:  "eqH::(lBool --> lBool --> lBool) == eqHI"
lBool_neqH_def: "neqH::(lBool --> lBool --> lBool) == neqHDF"
lift_eqH_def:  "eqH::(('a::PEq) lift --> 'a lift --> lBool) == eqHI"
lift_neqH_def: "neqH::(('a::PEq) lift --> 'a lift --> lBool) == neqHDF"
lOrdering_eqH_def:  "eqH::(lOrdering --> lOrdering --> lBool) == eqHI"
lOrdering_neqH_def: "neqH::(lOrdering --> lOrdering --> lBool) == neqHDF"

defs
llist_eqH_def:  
  "eqH::(('a::Eq) llist --> 'a llist --> lBool) == eqLL"
llist_neqH_def: 
  "neqH::(('a::Eq) llist --> 'a llist --> lBool) == neqHDF"
lprod_eqH_def:  
  "eqH::(('a::Eq,'b::Eq) lprod --> ('a::Eq,'b::Eq) lprod --> lBool) 
     == eqLP"
lprod_neqH_def: 
  "neqH::(('a::Eq,'b::Eq) lprod --> ('a::Eq,'b::Eq) lprod --> lBool) 
     == neqHDF"
lsum_eqH_def:   
  "eqH::(('a::Eq,'b::Eq) lEither --> ('a::Eq,'b::Eq) lEither --> lBool) 
     == eqLS"
lsum_neqH_def:  
  "neqH::(('a::Eq,'b::Eq) lEither --> ('a::Eq,'b::Eq) lEither --> lBool) 
     == neqHDF"
lMaybe_eqH_def:  
  "eqH::(('a::Eq) lMaybe --> ('a::Eq) lMaybe --> lBool) == eqLM"
lMaybe_neqH_def: 
  "neqH::(('a::Eq) lMaybe --> ('a::Eq) lMaybe --> lBool) == neqHDF"


(* Ord *)

consts
compareH   :: "'a::Ord --> 'a --> lOrdering"
lessH      :: "'a::Ord --> 'a --> lBool"
moreH      :: "'a::Ord --> 'a --> lBool"
leqH    :: "'a::Ord --> 'a --> lBool"
meqH    :: "'a::Ord --> 'a --> lBool"
minH       :: "'a::Ord --> 'a --> 'a"
maxH       :: "'a::Ord --> 'a --> 'a"

consts
compareD   :: "'a::Ord --> 'a --> lOrdering"
leqD      :: "'a::Ord --> 'a --> lBool"

consts
compareHDF   :: "'a::Ord --> 'a --> lOrdering"
lessHDF      :: "'a::Ord --> 'a --> lBool"
moreHDF      :: "'a::Ord --> 'a --> lBool"
leqHDF    :: "'a::Ord --> 'a --> lBool"
meqHDF    :: "'a::Ord --> 'a --> lBool"
minHDF       :: "'a::Ord --> 'a --> 'a"
maxHDF       :: "'a::Ord --> 'a --> 'a"


(* Ord - default method definitions *)

fixrec (permissive)
"compareD =
 (Lam x. (Lam y. (IF eqH $$ x $$ y THEN EQ
              ELSE (IF leqD $$ x $$ y THEN LT
                   ELSE GT FI) FI)))"
and "leqD =
 (Lam x. (Lam y. (neqH $$ (compareD $$ x $$ y) $$ GT)))"

defs
compareHDF_def: 
"compareHDF ==
 (Lam x. (Lam y. (IF eqH $$ x $$ y THEN EQ
              ELSE (IF leqH $$ x $$ y THEN LT
                   ELSE GT FI) FI)))"
leqHDF_def:
"leqHDF ==
 (Lam x. (Lam y. (neqH $$ (compareH $$ x $$ y) $$ GT)))"
lessHDF_def:
"lessHDF ==
 Lam x. Lam y. eqH $$ (compareH $$ x $$ y) $$ LT"
moreHDF_def:
"moreHDF ==
 Lam x. Lam y. eqH $$ (compareH $$ x $$ y) $$ GT"

meqHDF_def:
"meqHDF ==
 Lam x. Lam y. neqH $$ (compareH $$ x $$ y) $$ LT"
minHDF_def:
"minHDF ==
 Lam x. Lam y. IF leqH $$ x $$ y THEN x
                  ELSE y FI"
maxHDF_def:
"maxHDF ==
 Lam x. Lam y. IF leqH $$ x $$ y THEN y
                  ELSE x FI"


(* Num *)

consts 
addH   :: "'a::Num --> 'a --> 'a"
diffH  :: "'a::Num --> 'a --> 'a"
prodH   :: "'a::Num --> 'a --> 'a"
negateH :: "'a::Num --> 'a"
absH    :: "'a::Num --> 'a"
signumH :: "'a::Num --> 'a"
fromIntegerH :: "integerT --> 'a::Num"
zeroH        :: "'a::Num"
oneH         :: "'a::Num"
twoH         :: "'a::Num"

consts 
diffD  :: "'a::Num --> 'a --> 'a"
negateD :: "'a::Num --> 'a"
fromIntegerD :: "integerT --> 'a::Num"

consts 
diffHDF  :: "'a::Num --> 'a --> 'a"
negateHDF :: "'a::Num --> 'a"

defs
fromIntegerD_def: "fromIntegerD == (Lam x::integerT.
   IF eqH $$ x $$ (Def 0) THEN zeroH ELSE 
   IF eqH $$ x $$ (Def 1) THEN oneH  ELSE
   IF eqH $$ x $$ (Def 2) THEN twoH  ELSE
   fromIntegerH $$ x FI FI FI)"

fixrec (permissive)
"diffD = (Lam x. (Lam y. (addH $$ x $$ (negateD $$ y))))"
and
"negateD = (Lam x. diffD $$ (fromIntegerH $$ (Def 0)) $$ x)"

defs
diffHDF_def: "diffHDF == Lam x. (Lam y. (addH $$ x $$ (negateH $$ y)))"
negateHDF_def: "negateHDF == 
                        Lam x. diffH $$ (fromIntegerH $$ (Def 0)) $$ x"


(* some Prelude functions *)

constdefs
otherwiseH :: lBool
"otherwiseH == TRUE"
compH :: "('a --> 'b) --> ('c --> 'a) --> ('c --> 'b)"
"compH == Lam f. Lam g. Lam x. f $$ (g $$ x)"
flipH :: "('a --> 'b --> 'c) --> 'b --> 'a --> 'c"
"flipH == Lam f. Lam x. Lam y. f $$ y $$ x"
subtractH :: "'a::Num --> 'a --> 'a"
"subtractH == flipH $$ diffH"

consts
mapH :: "('a --> 'b) --> 'a llist --> 'b llist"

fixrec "mapH =
        (Lam qX1. Lam qX2. case qX2 of
                    lNil => lNil |
                    pX1 ### pX2 => qX1 $$ pX1 ### mapH $$ qX1 $$ pX2)"


(* Enum *)

consts
succH :: "'a::Enum --> 'a"
predH :: "'a::Enum --> 'a"
toEnumH :: "intT --> 'a::Enum"
fromEnumH :: "'a::Enum --> intT"
enumFromH :: "'a::Enum --> 'a llist"
enumFromThenH :: "'a::Enum --> 'a --> 'a llist"
enumFromToH :: "'a::Enum --> 'a --> 'a llist"
enumFromThenToH :: "'a::Enum --> 'a --> 'a --> 'a llist"

consts
succHDF :: "'a::Enum --> 'a"
predHDF :: "'a::Enum --> 'a"
toEnumHDF :: "intT --> 'a::Enum"
fromEnumHDF :: "'a::Enum --> intT"
enumFromHDF :: "'a::Enum --> 'a llist"
enumFromThenHDF :: "'a::Enum --> 'a --> 'a llist"
enumFromToHDF :: "'a::Enum --> 'a --> 'a llist"
enumFromThenToHDF :: "'a::Enum --> 'a --> 'a --> 'a llist"

defs
succHDF_def :
"succHDF ==
 compH $$ toEnumH $$
 (compH $$ (flipH $$ addH $$ (fromIntegerH $$ (Def 1))) $$
  fromEnumH)"

predHDF_def :
"predHDF ==
 compH $$ toEnumH $$
 (compH $$ (subtractH $$ (fromIntegerH $$ (Def 1))) $$ fromEnumH)"

enumFromToHDF_def :
"enumFromToHDF ==
 Lam x. Lam y. mapH $$ toEnumH $$
               (enumFromToH $$ (fromEnumH $$ x) $$ (fromEnumH $$ y))"

enumFromThenToHDF_def :
"enumFromThenToHDF ==
 Lam x. Lam y. Lam z. mapH $$ toEnumH $$
                      (enumFromThenToH $$ (fromEnumH $$ x) $$
                       (fromEnumH $$ y) $$ (fromEnumH $$ z))"


end
