
theory HsHOLCF = HOLCF:

axclass Eq < pcpo
(* eq_adm: "adm (% (x,y). x = y)" *)
axclass Ord < pcpo

constdefs 
fliftbin :: "(('a::type) => 'a => 'a) => ('a lift -> 'a lift -> 'a lift)"
"fliftbin f == (LAM y. (LAM x. (((flift1 (%u. (flift2 (%v. f v u))))$x)$y)))"  

end
