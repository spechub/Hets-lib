theory HsHOLCF 
imports HOLCF
begin

types 
dInt = "int lift"

axclass Ord < pcpo
axclass Eq < pcpo
(* eq_adm: "adm (% (x,y). x = y)" *)

instance lift :: (type) Eq
by intro_classes 

constdefs 
fliftbin :: 
    "('a::type => 'b::type => 'c::type) => 'a lift -> 'b lift -> 'c lift"
"fliftbin f == LAM y. LAM x. flift1 (%u. flift2 (%v. f v u)) $ x $ y"  

(* a type of lazy lists (from Fixrec_ex) *)
domain 'a llist = lNil | lCons (lazy lHd ::'a) (lazy lTl ::"'a llist")


end
