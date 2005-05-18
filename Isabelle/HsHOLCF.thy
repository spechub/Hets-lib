theory HsHOLCF = HOLCF:

constdefs
fliftbin :: "(('a::type) => 'a => 'a) => ('a lift -> 'a lift -> 'a lift)"
"fliftbin f == (LAM y. (LAM x. (((flift1 (%u. (flift2 (%v. f v u))))$x)$y)))"

end
