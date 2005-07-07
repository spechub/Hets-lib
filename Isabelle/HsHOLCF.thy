
theory HsHOLCF = HOLCF + Seq:

types 
dInt = "int lift"

axclass Ord < pcpo
axclass Eq < pcpo
(* eq_adm: "adm (% (x,y). x = y)" *)

constdefs 
fliftbin :: "(('a::type) => ('b::type) => ('c::type)) => ('a lift -> 'b lift -> 'c lift)"
"fliftbin f == (LAM y. (LAM x. (((flift1 (%u. (flift2 (%v. f v u))))$x)$y)))"  

end
