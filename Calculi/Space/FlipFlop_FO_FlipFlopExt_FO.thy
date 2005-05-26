ML "val hetsLib = (OS.Process.getEnv \"HETS_LIB\"); 
case hetsLib of NONE => add_path \".\" 
| SOME s => add_path (s ^ \"/Isabelle\")"

theory FlipFlop_FO_FlipFlopExt_FO = Main:

typedecl "Point"

consts
"ba" :: "Point => Point => Point => bool"   ( "ba" )
"bo" :: "Point => Point => Point => bool"   ( "bo" )
"dou" :: "Point => Point => Point => bool"   ( "dou" )
"fr" :: "Point => Point => Point => bool"   ( "fr" )
"le" :: "Point => Point => Point => bool"   ( "le" )
"ri" :: "Point => Point => Point => bool"   ( "ri" )
"so" :: "Point => Point => Point => bool"   ( "so" )
"sr" :: "Point => Point => Point => bool"   ( "sr" )
"tri" :: "Point => Point => Point => bool"   ( "tri" )


axioms
X: "!! x :: Point . !! y :: Point . !! z :: Point . (so x y z) = (x = z & (Not (x = y)))"
X1: "!! x :: Point . !! y :: Point . !! z :: Point . (sr x y z) = (y = z & (Not (x = y)))"
X2: "!! x :: Point . !! y :: Point . !! z :: Point . so x y z = sr y x z"
X3: "!! x :: Point . !! y :: Point . !! z :: Point . so x y z = sr y z x"
X4: "!! x :: Point . !! y :: Point . !! z :: Point . so x y z = so z y x"
X5: "!! x :: Point . !! y :: Point . !! z :: Point . sr x y z = so y x z"
X6: "!! x :: Point . !! y :: Point . !! z :: Point . sr x y z = sr x z y"
X7: "!! x :: Point . !! y :: Point . !! z :: Point . sr x y z = so z x y"
X8: "!! x :: Point . !! y :: Point . !! z :: Point . ri x y z = le y x z"
X9: "!! x :: Point . !! y :: Point . !! z :: Point . ri x y z = le x z y"
X10: "!! x :: Point . !! y :: Point . !! z :: Point . ri x y z = ri y z x"
X11: "!! x :: Point . !! y :: Point . !! z :: Point . ri x y z = ri z x y"
X12: "!! x :: Point . !! y :: Point . !! z :: Point . ri x y z = le z y x"
X13: "!! x :: Point . !! y :: Point . !! z :: Point . le x y z = ri y x z"
X14: "!! x :: Point . !! y :: Point . !! z :: Point . le x y z = ri x z y"
X15: "!! x :: Point . !! y :: Point . !! z :: Point . le x y z = le y z x"
X16: "!! x :: Point . !! y :: Point . !! z :: Point . le x y z = le z x y"
X17: "!! x :: Point . !! y :: Point . !! z :: Point . le x y z = ri z y x"
X18: "!! x :: Point . !! y :: Point . !! z :: Point . ba x y z = bo y x z"
X19: "!! x :: Point . !! y :: Point . !! z :: Point . ba x y z = fr x z y"
X20: "!! x :: Point . !! y :: Point . !! z :: Point . ba x y z = bo y z x"
X21: "!! x :: Point . !! y :: Point . !! z :: Point . ba x y z = fr z x y"
X22: "!! x :: Point . !! y :: Point . !! z :: Point . ba x y z = ba z y x"
X23: "!! x :: Point . !! y :: Point . !! z :: Point . fr x y z = fr y x z"
X24: "!! x :: Point . !! y :: Point . !! z :: Point . fr x y z = ba x z y"
X25: "!! x :: Point . !! y :: Point . !! z :: Point . fr x y z = ba y z x"
X26: "!! x :: Point . !! y :: Point . !! z :: Point . fr x y z = bo z x y"
X27: "!! x :: Point . !! y :: Point . !! z :: Point . fr x y z = bo z y x"
X28: "!! x :: Point . !! y :: Point . !! z :: Point . bo x y z = ba y x z"
X29: "!! x :: Point . !! y :: Point . !! z :: Point . bo x y z = bo x z y"
X30: "!! x :: Point . !! y :: Point . !! z :: Point . bo x y z = fr y z x"
X31: "!! x :: Point . !! y :: Point . !! z :: Point . bo x y z = ba z x y"
X32: "!! x :: Point . !! y :: Point . !! z :: Point . bo x y z = fr z y x"
X33: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((ri x y w) & (ri w y z)) ==> ((ri x y z) | (le x y z) | (ba x y z))"
X34: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((ri x y w) & (le w y z)) ==> ((ri x y z) | (le x y z) | (fr x y z) | (bo x y z) | (so x y z))"
X35: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((ri x y w) & (ba w y z)) ==> (le x y z)"
X36: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((ri x y w) & (fr w y z)) ==> (ri x y z)"
X37: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((ri x y w) & (bo w y z)) ==> (ri x y z)"
X38: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((ri x y w) & (so w y z)) ==> (ri x y z)"
X39: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((ri x y w) & (sr w y z)) ==> (sr x y z)"
X40: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((le x y w) & (ri w y z)) ==> ((ri x y z) | (le x y z) | (fr x y z) | (bo x y z) | (so x y z))"
X41: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((le x y w) & (le w y z)) ==> ((ri x y z) | (le x y z) | (ba x y z))"
X42: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((le x y w) & (ba w y z)) ==> (ri x y z)"
X43: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((le x y w) & (fr w y z)) ==> (le x y z)"
X44: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((le x y w) & (bo w y z)) ==> (le x y z)"
X45: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((le x y w) & (so w y z)) ==> (le x y z)"
X46: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((le x y w) & (sr w y z)) ==> (sr x y z)"
X47: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((ba x y w) & (ri w y z)) ==> (le x y z)"
X48: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((ba x y w) & (le w y z)) ==> (ri x y z)"
X49: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((ba x y w) & (ba w y z)) ==> ((fr x y z) | (bo x y z) | (so x y z))"
X50: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((ba x y w) & (fr w y z)) ==> (ba x y z)"
X51: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((ba x y w) & (bo w y z)) ==> (ba x y z)"
X52: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((ba x y w) & (so w y z)) ==> (ba x y z)"
X53: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((ba x y w) & (sr w y z)) ==> (sr x y z)"
X54: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((fr x y w) & (ri w y z)) ==> (ri x y z)"
X55: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((fr x y w) & (le w y z)) ==> (le x y z)"
X56: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((fr x y w) & (ba w y z)) ==> (ba x y z)"
X57: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((fr x y w) & (fr w y z)) ==> (fr x y z)"
X58: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((fr x y w) & (bo w y z)) ==> ((fr x y z) | (bo x y z) | (so x y z))"
X59: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((fr x y w) & (so w y z)) ==> (fr x y z)"
X60: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((fr x y w) & (sr w y z)) ==> (sr x y z)"
X61: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((bo x y w) & (ri w y z)) ==> (ri x y z)"
X62: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((bo x y w) & (le w y z)) ==> (le x y z)"
X63: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((bo x y w) & (ba w y z)) ==> (ba x y z)"
X64: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((bo x y w) & (fr w y z)) ==> ((fr x y z) | (bo x y z) | (so x y z))"
X65: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((bo x y w) & (bo w y z)) ==> (bo x y z)"
X66: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((bo x y w) & (so w y z)) ==> (bo x y z)"
X67: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((bo x y w) & (sr w y z)) ==> (sr x y z)"
X68: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((so x y w) & (ri w y z)) ==> (ri x y z)"
X69: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((so x y w) & (le w y z)) ==> (le x y z)"
X70: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((so x y w) & (ba w y z)) ==> (ba x y z)"
X71: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((so x y w) & (fr w y z)) ==> (fr x y z)"
X72: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((so x y w) & (bo w y z)) ==> (bo x y z)"
X73: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((so x y w) & (so w y z)) ==> (so x y z)"
X74: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((so x y w) & (sr w y z)) ==> (sr x y z)"
X75: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((sr x y w) & (ri w y z)) ==> False"
X76: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((sr x y w) & (le w y z)) ==> False"
X77: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((sr x y w) & (ba w y z)) ==> False"
X78: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((sr x y w) & (fr w y z)) ==> False"
X79: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((sr x y w) & (bo w y z)) ==> False"
X80: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((sr x y w) & (so w y z)) ==> False"
X81: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((sr x y w) & (sr w y z)) ==> False"
X82: "!! x :: Point . !! y :: Point . !! z :: Point . (tri x y z) = (x = y & y = z)"
X83: "!! x :: Point . !! y :: Point . !! z :: Point . (dou x y z) = (x = y & (Not (y = z)))"
X84: "!! x :: Point . tri x x x"
X85: "!! x :: Point . !! y :: Point . !! z :: Point . tri x y z = tri y x z"
X86: "!! x :: Point . !! y :: Point . !! z :: Point . tri x y z = tri x z y"
X87: "!! x :: Point . !! y :: Point . !! z :: Point . tri x y z = tri y z x"
X88: "!! x :: Point . !! y :: Point . !! z :: Point . tri x y z = tri z x y"
X89: "!! x :: Point . !! y :: Point . !! z :: Point . tri x y z = tri z y x"
X90: "!! x :: Point . !! y :: Point . !! z :: Point . dou x y z = dou y x z"
X91: "!! x :: Point . !! y :: Point . !! z :: Point . dou x y z = so x z y"
X92: "!! x :: Point . !! y :: Point . !! z :: Point . dou x y z = so y z x"
X93: "!! x :: Point . !! y :: Point . !! z :: Point . dou x y z = sr z x y"
X94: "!! x :: Point . !! y :: Point . !! z :: Point . dou x y z = sr z y x"
X95: "!! x :: Point . !! y :: Point . !! z :: Point . so x y z = dou x z y"
X96: "!! x :: Point . !! y :: Point . !! z :: Point . so x y z = dou z x y"
X97: "!! x :: Point . !! y :: Point . !! z :: Point . sr x y z = dou y z x"
X98: "!! x :: Point . !! y :: Point . !! z :: Point . sr x y z = dou z y x"
X99: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((ri x y w) & (dou w y z)) ==> False"
X100: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((ri x y w) & (tri w y z)) ==> False"
X101: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((le x y w) & (dou w y z)) ==> False"
X102: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((le x y w) & (tri w y z)) ==> False"
X103: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((ba x y w) & (dou w y z)) ==> False"
X104: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((ba x y w) & (tri w y z)) ==> False"
X105: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((fr x y w) & (dou w y z)) ==> False"
X106: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((fr x y w) & (tri w y z)) ==> False"
X107: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((bo x y w) & (dou w y z)) ==> False"
X108: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((bo x y w) & (tri w y z)) ==> False"
X109: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((so x y w) & (dou w y z)) ==> False"
X110: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((so x y w) & (tri w y z)) ==> False"
X111: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((sr x y w) & (dou w y z)) ==> ((ri x y z) | (le x y z) | (ba x y z) | (fr x y z) | (bo x y z) | (so x y z))"
X112: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((sr x y w) & (tri w y z)) ==> (sr x y z)"
X113: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((dou x y w) & (ri w y z)) ==> (dou x y z)"
X114: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((dou x y w) & (le w y z)) ==> (dou x y z)"
X115: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((dou x y w) & (ba w y z)) ==> (dou x y z)"
X116: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((dou x y w) & (fr w y z)) ==> (dou x y z)"
X117: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((dou x y w) & (bo w y z)) ==> (dou x y z)"
X118: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((dou x y w) & (so w y z)) ==> (dou x y z)"
X119: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((dou x y w) & (sr w y z)) ==> (tri x y z)"
X120: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((dou x y w) & (dou w y z)) ==> False"
X121: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((dou x y w) & (tri w y z)) ==> False"
X122: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((tri x y w) & (ri w y z)) ==> False"
X123: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((tri x y w) & (le w y z)) ==> False"
X124: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((tri x y w) & (ba w y z)) ==> False"
X125: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((tri x y w) & (fr w y z)) ==> False"
X126: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((tri x y w) & (bo w y z)) ==> False"
X127: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((tri x y w) & (so w y z)) ==> False"
X128: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((tri x y w) & (sr w y z)) ==> False"
X129: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((tri x y w) & (dou w y z)) ==> (dou x y z)"
X130: "!! x :: Point . !! y :: Point . !! z :: Point . !! w :: Point . ((tri x y w) & (tri w y z)) ==> (tri x y z)"

X131: "!! x :: Point . !! y :: Point . !! z :: Point . (ri x y z) ==> (Not (le x y z))"
X132: "!! x :: Point . !! y :: Point . !! z :: Point . (ri x y z) ==> (Not (ba x y z))"
X133: "!! x :: Point . !! y :: Point . !! z :: Point . (ri x y z) ==> (Not (fr x y z))"
X134: "!! x :: Point . !! y :: Point . !! z :: Point . (ri x y z) ==> (Not (bo x y z))"
X135: "!! x :: Point . !! y :: Point . !! z :: Point . (ri x y z) ==> (Not (so x y z))"
X136: "!! x :: Point . !! y :: Point . !! z :: Point . (ri x y z) ==> (Not (sr x y z))"
X137: "!! x :: Point . !! y :: Point . !! z :: Point . (ri x y z) ==> (Not (dou x y z))"
X138: "!! x :: Point . !! y :: Point . !! z :: Point . (ri x y z) ==> (Not (tri x y z))"
X139: "!! x :: Point . !! y :: Point . !! z :: Point . (le x y z) ==> (Not (ba x y z))"
X140: "!! x :: Point . !! y :: Point . !! z :: Point . (le x y z) ==> (Not (fr x y z))"
X141: "!! x :: Point . !! y :: Point . !! z :: Point . (le x y z) ==> (Not (bo x y z))"
X142: "!! x :: Point . !! y :: Point . !! z :: Point . (le x y z) ==> (Not (so x y z))"
X143: "!! x :: Point . !! y :: Point . !! z :: Point . (le x y z) ==> (Not (sr x y z))"
X144: "!! x :: Point . !! y :: Point . !! z :: Point . (le x y z) ==> (Not (dou x y z))"
X145: "!! x :: Point . !! y :: Point . !! z :: Point . (le x y z) ==> (Not (tri x y z))"
X146: "!! x :: Point . !! y :: Point . !! z :: Point . (ba x y z) ==> (Not (fr x y z))"
X147: "!! x :: Point . !! y :: Point . !! z :: Point . (ba x y z) ==> (Not (bo x y z))"
X148: "!! x :: Point . !! y :: Point . !! z :: Point . (ba x y z) ==> (Not (so x y z))"
X149: "!! x :: Point . !! y :: Point . !! z :: Point . (ba x y z) ==> (Not (sr x y z))"
X150: "!! x :: Point . !! y :: Point . !! z :: Point . (ba x y z) ==> (Not (dou x y z))"
X151: "!! x :: Point . !! y :: Point . !! z :: Point . (ba x y z) ==> (Not (tri x y z))"
X152: "!! x :: Point . !! y :: Point . !! z :: Point . (fr x y z) ==> (Not (bo x y z))"
X153: "!! x :: Point . !! y :: Point . !! z :: Point . (fr x y z) ==> (Not (so x y z))"
X154: "!! x :: Point . !! y :: Point . !! z :: Point . (fr x y z) ==> (Not (sr x y z))"
X155: "!! x :: Point . !! y :: Point . !! z :: Point . (fr x y z) ==> (Not (dou x y z))"
X156: "!! x :: Point . !! y :: Point . !! z :: Point . (fr x y z) ==> (Not (tri x y z))"
X157: "!! x :: Point . !! y :: Point . !! z :: Point . (bo x y z) ==> (Not (so x y z))"
X158: "!! x :: Point . !! y :: Point . !! z :: Point . (bo x y z) ==> (Not (sr x y z))"
X159: "!! x :: Point . !! y :: Point . !! z :: Point . (bo x y z) ==> (Not (dou x y z))"
X160: "!! x :: Point . !! y :: Point . !! z :: Point . (bo x y z) ==> (Not (tri x y z))"
X161: "!! x :: Point . !! y :: Point . !! z :: Point . (so x y z) ==> (Not (sr x y z))"
X162: "!! x :: Point . !! y :: Point . !! z :: Point . (so x y z) ==> (Not (dou x y z))"
X163: "!! x :: Point . !! y :: Point . !! z :: Point . (so x y z) ==> (Not (tri x y z))"
X164: "!! x :: Point . !! y :: Point . !! z :: Point . (sr x y z) ==> (Not (dou x y z))"
X165: "!! x :: Point . !! y :: Point . !! z :: Point . (sr x y z) ==> (Not (tri x y z))"



declare X18 [simp]

theorem "tri x y z --> tri x y z"
proof
  assume a1: "tri x y z"
  show "tri x y z" by (rule a1) 
qed

theorem "tri x y z --> tri y x z"
proof
  assume a1: "tri x y z"
  with X85 show "tri y x z" by (simp)
qed

theorem "ba x y z --> bo y x z"
proof
  assume "ba x y z"
  thus "bo y x z" by (simp) --"add : X18)"
qed


theorem "le p1 p2 p3 & ba p3 p2 p4 --> ri p1 p2 p4"
proof
  assume a1: "le p1 p2 p3 & ba p3 p2 p4"
  from a1 show "ri p1 p2 p4" by (rule X42)
qed


theorem "(le p1 p2 p3 & ba p3 p2 p4) | (bo p1 p3 p4) ==> (ri p1 p2 p4 | bo p1 p3 p4)"
proof -
  assume "(le p1 p2 p3 & ba p3 p2 p4) | (bo p1 p3 p4)"
  with X42 show "(ri p1 p2 p4) | (bo p1 p3 p4)" by (auto)
qed


declare X85 [simp del]
declare X18 [simp del]
declare X42 [simp del]

theorem assumes an: "((sr p11 p12 p21 & so p11 p12 p22) & (sr p21 p22 p11 & so p21 p22 p12)) & ((le p21 p22 p31 & le p21 p22 p32) & (le p31 p32 p21 & le p31 p32 p22))" shows "(ri p11 p12 p31 & ri p11 p12 p32) & (le p31 p32 p11 & le p31 p32 p12)"
proof
  have an1: "(sr p11 p12 p21 & so p11 p12 p22) & (sr p21 p22 p11 & so p21 p22 p12)" by (rule conjE)
  then have an11: "sr p11 p12 p21 & so p11 p12 p22" ..
  then have a1: "sr p11 p12 p21" ..
  from an11 have a2: "so p11 p12 p22" .. 

  from an1  have an12: "sr p21 p22 p11 & so p21 p22 p12" ..
  then have a3: "sr p21 p22 p11" ..
  from an12 have a4: "so p21 p22 p12" ..
 
  from an have an2: "(le p21 p22 p31 & le p21 p22 p32) & (le p31 p32 p21 & le p31 p32 p22)" ..
  then have an21: "le p21 p22 p31 & le p21 p22 p32" ..
  then have a5: "le p21 p22 p31" ..
  from an21 have a6: "le p21 p22 p32" ..
  
  from an2  have an22: "le p31 p32 p21 & le p31 p32 p22" ..
  then have a7: "le p31 p32 p21" ..
  from an22 have a8: "le p31 p32 p22" ..


  from a3 have b1 : "so p11 p21 p22" by (simp (no_asm) add : X3)
  from a4 have b2 : "so p12 p22 p21" by (simp add : X4)
  from a5 have b3 : "ri p22 p21 p31" by (simp (no_asm) add : X8)
  
  from b1 b3 have "so p11 p21 p22 & ri p22 p21 p31" by (rule conjI)
  then have c1 : "ri p11 p21 p31" by (rule X68)
  from b2 a6 have "so p12 p22 p21 & le p21 p22 p32" by (rule conjI)
  then have c2 : "le p12 p22 p32" by (rule X69)
  
  from c1 have d1 : "ri p31 p11 p21" by (simp add : X11 )
  from c2 have d2 : "le p32 p12 p22" by (simp add : X16 )
  from a1 have d3 : "so p21 p11 p12" by (simp add : X7 )
  from a2 have d4 : "so p22 p12 p11" by (simp add : X4 )
  
  from d1 d3 have "ri p31 p11 p21 & so p21 p11 p12" by (rule conjI)
  then have "ri p31 p11 p12" by (rule X38)
  then have z1: "ri p11 p12 p31" by (simp add : X10 )
  from d2 d4 have "le p32 p12 p22 & so p22 p12 p11" by (rule conjI)
  then have "le p32 p12 p11" by (rule X45)
  then have z2 : "ri p11 p12 p32" by (simp add : X17 )
  
  from c1 have d5 : "le p31 p21 p11" by (simp add : X12 )
  from c2 have d6 : "ri p32 p22 p12" by (simp add : X17 )
  from a1 have d7 : "sr p11 p21 p12" by (simp add : X6 )
  from a2 have d8 : "sr p12 p22 p11" by (simp add : X3 )
  from d5 d7 have "le p31 p21 p11 & sr p11 p21 p12" by (rule conjI)
  then have "sr p31 p21 p12" by (rule X46 )
  then have e1 : "so p12 p31 p21" by (simp add : X7 )
  from d6 d8 have "ri p32 p22 p12 & sr p12 p22 p11" by (rule conjI)
  then have "sr p32 p22 p11" by (rule X39 )
  then have e2 : "so p11 p32 p22" by (simp add : X7 )    
  from a7 have e3 : "le p21 p31 p32" by (simp add : X16 )
  from a8 have e4 : "ri p22 p32 p31" by (simp add : X17 )
  from e1 e3 have "so p12 p31 p21 & le p21 p31 p32" by (rule conjI)
  then have "le p12 p31 p32" by (rule X69 )
  then have z3 : "le p31 p32 p12" by (simp add : X16 )
  from e2 e4 have "so p11 p32 p22 & ri p22 p32 p31" by (rule conjI)
  then have "ri p11 p32 p31" by (rule X68 )
  then have z4 : "le p31 p32 p11" by (simp add : X12)

  from z1 z2 show "ri p11 p12 p31 & ri p11 p12 p32" ..
  from z4 z3 show "le p31 p32 p11 & le p31 p32 p12" ..
qed --"eses cmps llll = rrll"

theorem assumes an: "((ba p11 p12 p21 & le p11 p12 p22) & (le p21 p22 p11 & le p21 p22 p12)) & ((ba p21 p22 p31 & ba p21 p22 p32) & (bo p31 p32 p21 & bo p31 p32 p22))" shows "(le p11 p12 p31 & le p11 p12 p32) & (le p31 p32 p11 & le p31 p32 p12)"
proof
 have an1: "(ba p11 p12 p21 & le p11 p12 p22) & (le p21 p22 p11 & le p21 p22 p12)" by (rule conjE)
  then have an11: "ba p11 p12 p21 & le p11 p12 p22" ..
  then have a1: "ba p11 p12 p21" ..
  from an11 have a2: "le p11 p12 p22" .. 

  from an1  have an12: "le p21 p22 p11 & le p21 p22 p12" ..
  then have a3: "le p21 p22 p11" ..
  from an12 have a4: "le p21 p22 p12" ..
 
  from an have an2: "(ba p21 p22 p31 & ba p21 p22 p32) & (bo p31 p32 p21 & bo p31 p32 p22)" ..
  then have an21: "ba p21 p22 p31 & ba p21 p22 p32" ..
  then have a5: "ba p21 p22 p31" ..
  from an21 have a6: "ba p21 p22 p32" ..
  
  from an2  have an22: "bo p31 p32 p21 & bo p31 p32 p22" ..
  then have a7: "bo p31 p32 p21" ..
  from an22 have a8: "bo p31 p32 p22" ..  

  from a3 have b1 : "le p11 p21 p22" by (simp add : X16)
  from a4 have b2 : "ri p12 p22 p21" by (simp add : X17)
  from a5 have b3 : "bo p22 p21 p31" by (simp add : X18)
 
  from b1 b3 have "le p11 p21 p22 & bo p22 p21 p31" by (rule conjI)
  then have c1 : "le p11 p21 p31" by (rule X44)
  from b2 a6 have "ri p12 p22 p21 & ba p21 p22 p32" by (rule conjI)
  then have c2 : "le p12 p22 p32" by (rule X35)
  
  from c1 have d1 : "le p31 p11 p21" by (simp add : X16 )
  from c2 have d2 : "le p32 p12 p22" by (simp add : X16 )
  from a1 have d3 : "fr p21 p11 p12" by (simp add : X21 )
  from a2 have d4 : "ri p22 p12 p11" by (simp add : X17 )
  
  from d1 d3 have "le p31 p11 p21 & fr p21 p11 p12" by (rule conjI)
  then have "le p31 p11 p12" by (rule X43)
  then have z1: "le p11 p12 p31" by (simp add : X15 )
  from d2 d4 have "le p32 p12 p22 & ri p22 p12 p11" by (rule conjI)
  then have "(ri p32 p12 p11) | (le p32 p12 p11) | (fr p32 p12 p11) | (bo p32 p12 p11) | (so p32 p12 p11)" by (rule X40)
  -- "then have z2 : p11 p12 p32 by (simp add : X )"

  from c1 have d11 : "ri p11 p31 p21" by (simp add : X14 )
  from c2 have d12 : "ri p12 p32 p22" by (simp add : X14 )
  from a7 have d13 : "ba p21 p31 p32" by (simp add : X31 )
  from a8 have d14 : "fr p22 p32 p31" by (simp add : X32 )

  from d11 d13 have "ri p11 p31 p21 & ba p21 p31 p32" by (rule conjI)
  then have "le p11 p31 p32" by (rule X35)
  then have z13: "le p31 p32 p11" by (simp add : X16)
  from d12 d14 have "ri p12 p32 p22 & fr p22 p32 p31" by (rule conjI)
  then have "ri p12 p32 p31" by (rule X36)
  then have z14 : "le p31 p32 p12" by (simp add : X12 )
  
  from c1 have d5 : "ri p31 p21 p11" by (simp add : X17 )
  from c2 have d6 : "ri p32 p22 p12" by (simp add : X17 )
  from a1 have d7 : "fr p11 p21 p12" by (simp add : X19 )
  from a2 have d8 : "le p12 p22 p11" by (simp add : X16 )
  from d5 d7 have "ri p31 p21 p11 & fr p11 p21 p12" by (rule conjI)
  then have "ri p31 p21 p12" by (rule X36 )
  then have e1 : "ri p12 p31 p21" by (simp add : X11 )
  from d6 d8 have "ri p32 p22 p12 & le p12 p22 p11" by (rule conjI)
  then have "(ri p32 p22 p11) | (le p32 p22 p11) | (fr p32 p22 p11) | (bo p32 p22 p11) | (so p32 p22 p11)" by (rule X34 )
  -- "then have e2 :  p11 p32 p22 by (simp add : X )"    
  from a7 have e3 : "ba p21 p31 p32" by (simp add : X31 )
  from a8 have e4 : "fr p22 p32 p31" by (simp add : X32 )
  from e1 e3 have "ri p12 p31 p21 & ba p21 p31 p32" by (rule conjI)
  then have "le p12 p31 p32" by (rule X35)
  then have z4 : "le p31 p32 p12" by (simp add : X16 )
  -- "from e2 e4 have  p11 p32 p22 &  p22 p32 p31 by (rule conjI)"
  -- "then have  p11 p32 p31 by (rule X )"
  -- "then have z3 :  p31 p32 p11 by (simp add : X )"

  from a7 have d17: "bo p31 p21 p32" by (simp add : X29 )
  from a8 have d18: "fr p32 p22 p31" by (simp add : X30 )
  from c1 d17 have "le p11 p21 p31 & bo p31 p21 p32" ..
  then have "le p11 p21 p32" by (rule X44 )
  then have e11: "le p32 p11 p21" by (simp add : X16 )
  from c2 d18 have "le p12 p22 p32 & fr p32 p22 p31" ..
  then have "le p12 p22 p31" by (rule X43 )
  then have e12: "le p31 p12 p22" by (simp add : X16 )
  from a1 have e13: "fr p21 p11 p12" by (simp add : X21 )
  from a2 have e14: "ri p22 p12 p11" by (simp add : X17 )
  from e11 e13 have "le p32 p11 p21 & fr p21 p11 p12" by (rule conjI)
  then have "le p32 p11 p12" by (rule X43 )
  then have z12: "le p11 p12 p32" by (simp add : X15 )
  from e12 e14 have "le p31 p12 p22 & ri p22 p12 p11" by (rule conjI)
  -- "then have  p31 p12 p11 by (rule X )"
  -- "then have z11:  p11 p12 p31 by (simp add : X )"

  from z1 z12 show "le p11 p12 p31 & le p11 p12 p32" ..
  from z13 z14 show "le p31 p32 p11 & le p31 p32 p12" ..
qed -- "flll cmps ffbb = llll"


theorem assumes an: "((ba p11 p12 p21 & ri p11 p12 p22) & (ri p21 p22 p11 & ri p21 p22 p12)) & ((ba p21 p22 p31 & ba p21 p22 p32) & (bo p31 p32 p21 & bo p31 p32 p22))" shows "(ri p11 p12 p31 & ri p11 p12 p32) & (ri p31 p32 p11 & ri p31 p32 p12)"
proof
 have an1: "(ba p11 p12 p21 & ri p11 p12 p22) & (ri p21 p22 p11 & ri p21 p22 p12)" by (rule conjE)
  then have an11: "ba p11 p12 p21 & ri p11 p12 p22" ..
  then have a1: "ba p11 p12 p21" ..
  from an11 have a2: "ri p11 p12 p22" .. 

  from an1  have an12: "ri p21 p22 p11 & ri p21 p22 p12" ..
  then have a3: "ri p21 p22 p11" ..
  from an12 have a4: "ri p21 p22 p12" ..
 
  from an have an2: "(ba p21 p22 p31 & ba p21 p22 p32) & (bo p31 p32 p21 & bo p31 p32 p22)" ..
  then have an21: "ba p21 p22 p31 & ba p21 p22 p32" ..
  then have a5: "ba p21 p22 p31" ..
  from an21 have a6: "ba p21 p22 p32" ..
  
  from an2  have an22: "bo p31 p32 p21 & bo p31 p32 p22" ..
  then have a7: "bo p31 p32 p21" ..
  from an22 have a8: "bo p31 p32 p22" ..  

  from a3 have b1 : "ri p11 p21 p22" by (simp add : X11)
  from a4 have b2 : "le p12 p22 p21" by (simp add : X12)
  from a5 have b3 : "bo p22 p21 p31" by (simp add : X18)
 
  from b1 b3 have "ri p11 p21 p22 & bo p22 p21 p31" by (rule conjI)
  then have c1 : "ri p11 p21 p31" by (rule X37)
  from b2 a6 have "le p12 p22 p21 & ba p21 p22 p32" by (rule conjI)
  then have c2 : "ri p12 p22 p32" by (rule X42)
  
  from c1 have d1 : "ri p31 p11 p21" by (simp add : X11 )
  from c2 have d2 : "ri p32 p12 p22" by (simp add : X11 )
  from a1 have d3 : "fr p21 p11 p12" by (simp add : X21 )
  from a2 have d4 : "le p22 p12 p11" by (simp add : X12 )
  
  from d1 d3 have "ri p31 p11 p21 & fr p21 p11 p12" by (rule conjI)
  then have "ri p31 p11 p12" by (rule X36)
  then have z1: "ri p11 p12 p31" by (simp add : X10 )
  from d2 d4 have "ri p32 p12 p22 & le p22 p12 p11" by (rule conjI)
  then have "(ri p32 p12 p11) | (le p32 p12 p11) | (fr p32 p12 p11) | (bo p32 p12 p11) | (so p32 p12 p11)" by (rule X34)
  -- "then have z2 : p11 p12 p32 by (simp add : X )"

  from c1 have d11 : "le p11 p31 p21" by (simp add : X9 )
  from c2 have d12 : "le p12 p32 p22" by (simp add : X9 )
  from a7 have d13 : "ba p21 p31 p32" by (simp add : X31 )
  from a8 have d14 : "fr p22 p32 p31" by (simp add : X32 )

  from d11 d13 have "le p11 p31 p21 & ba p21 p31 p32" by (rule conjI)
  then have "ri p11 p31 p32" by (rule X42)
  then have z13: "ri p31 p32 p11" by (simp add : X11)
  from d12 d14 have "le p12 p32 p22 & fr p22 p32 p31" by (rule conjI)
  then have "le p12 p32 p31" by (rule X43)
  then have z14 : "ri p31 p32 p12" by (simp add : X17 )
  
  from a7 have d17: "bo p31 p21 p32" by (simp add : X29 )
  from a8 have d18: "fr p32 p22 p31" by (simp add : X30 )
  from c1 d17 have "ri p11 p21 p31 & bo p31 p21 p32" ..
  then have "ri p11 p21 p32" by (rule X37 )
  then have e11: "ri p32 p11 p21" by (simp add : X11 )
  from c2 d18 have "ri p12 p22 p32 & fr p32 p22 p31" ..
  then have "ri p12 p22 p31" by (rule X36 )
  then have e12: "ri p31 p12 p22" by (simp add : X11 )
  from a1 have e13: "fr p21 p11 p12" by (simp add : X21 )
  from a2 have e14: "le p22 p12 p11" by (simp add : X12 )
  from e11 e13 have "ri p32 p11 p21 & fr p21 p11 p12" by (rule conjI)
  then have "ri p32 p11 p12" by (rule X36 )
  then have z12: "ri p11 p12 p32" by (simp add : X10 )
  from e12 e14 have "ri p31 p12 p22 & le p22 p12 p11" by (rule conjI)
  -- "then have  p31 p12 p11 by (rule X )"
  -- "then have z11:  p11 p12 p31 by (simp add : X )"

  from z1 z12 show "ri p11 p12 p31 & ri p11 p12 p32" ..
  from z13 z14 show "ri p31 p32 p11 & ri p31 p32 p12" ..
qed -- "flll cmps ffbb = llll"


theorem assumes an: "((sr p11 p12 p21 & so p11 p12 p22) & (sr p21 p22 p11 & so p21 p22 p12)) & ((ri p21 p22 p31 & ri p21 p22 p32) & (ri p31 p32 p21 & ri p31 p32 p22))" shows "(le p11 p12 p31 & le p11 p12 p32) & (ri p31 p32 p11 & ri p31 p32 p12)"
proof 
  have an1: "(sr p11 p12 p21 & so p11 p12 p22) & (sr p21 p22 p11 & so p21 p22 p12)" by (rule conjE)
  then have an11: "sr p11 p12 p21 & so p11 p12 p22" ..
  then have a1: "sr p11 p12 p21" ..
  from an11 have a2: "so p11 p12 p22" .. 

  from an1  have an12: "sr p21 p22 p11 & so p21 p22 p12" ..
  then have a3: "sr p21 p22 p11" ..
  from an12 have a4: "so p21 p22 p12" ..
 
  from an have an2: "(ri p21 p22 p31 & ri p21 p22 p32) & (ri p31 p32 p21 & ri p31 p32 p22)" ..
  then have an21: "ri p21 p22 p31 & ri p21 p22 p32" ..
  then have a5: "ri p21 p22 p31" ..
  from an21 have a6: "ri p21 p22 p32" ..
  
  from an2  have an22: "ri p31 p32 p21 & ri p31 p32 p22" ..
  then have a7: "ri p31 p32 p21" ..
  from an22 have a8: "ri p31 p32 p22" ..

  from a3 have b1 : "so p11 p21 p22" by (simp add : X7) -- "trans312"
  from a4 have b2 : "so p12 p22 p21" by (simp add : X4) -- "trans321"
  from a5 have b3 : "le p22 p21 p31" by (simp add : X8) -- "trans213"
 
  from b1 b3 have "so p11 p21 p22 & le p22 p21 p31" by (rule conjI)
  then have c1 : "le p11 p21 p31" by (rule X69)
  from b2 a6 have "so p12 p22 p21 & ri p21 p22 p32" by (rule conjI)
  then have c2 : "ri p12 p22 p32" by (rule X68)
  
  -- "z1 z2 kurzer Weg ueber a1 a2" 
  from c1 have d1 : "le p31 p11 p21" by (simp add : X16 ) -- "trans312"
  from c2 have d2 : "ri p32 p12 p22" by (simp add : X11 ) -- "trans312"
  from a1 have d3 : "so p21 p11 p12" by (simp add : X7 ) -- "trans312"
  from a2 have d4 : "so p22 p12 p11" by (simp add : X4 ) -- "trans321"
  
  from d1 d3 have "le p31 p11 p21 & so p21 p11 p12" by (rule conjI)
  then have "le p31 p11 p12" by (rule X45)
  then have z1: "le p11 p12 p31" by (simp add : X15 ) -- "trans231"
  from d2 d4 have "ri p32 p12 p22 & so p22 p12 p11" by (rule conjI)
  then have "ri p32 p12 p11" by (rule X38)
  then have z2: "le p11 p12 p32" by (simp add : X12 ) -- "trans321"

  -- "z13 z14 langer Weg ueber a1 a2 und a7 a8"
  from c1 have d15 : "ri p31 p21 p11" by (simp add : X17 ) -- "trans321"
  from c2 have d16 : "le p32 p22 p12" by (simp add : X12 ) -- "trans321"
  from a1 have d17 : "sr p11 p21 p12" by (simp add : X6 ) -- "trans132"
  from a2 have d18 : "sr p12 p22 p11" by (simp add : X3 ) -- "trans231"
  from d15 d17 have "ri p31 p21 p11 & sr p11 p21 p12" by (rule conjI)
  then have "sr p31 p21 p12" by (rule X39)
  then have e5 : "so p12 p31 p21" by (simp add : X7) -- "trans312"
  from d16 d18 have "le p32 p22 p12 & sr p12 p22 p11" by (rule conjI)
  then have "sr p32 p22 p11" by (rule X46)
  then have e6 : "so p11 p32 p22" by (simp add : X7 ) -- "trans312"
  from a7 have e7 : "ri p21 p31 p32" by (simp add : X11 ) -- "trans312"
  from a8 have e8 : "le p22 p32 p31" by (simp add : X12 ) -- "trans321"
  from e5 e7 have "so p12 p31 p21 & ri p21 p31 p32" by (rule conjI)
  then have "ri p12 p31 p32" by (rule X68 )
  then have z14: "ri p31 p32 p12" by (simp add : X11 ) -- "trans231"
  from e6 e8 have "so p11 p32 p22 & le p22 p32 p31" by (rule conjI)
  then have "le p11 p32 p31" by (rule X69 )
  then have z13: "ri p31 p32 p11" by (simp add : X17 ) -- "trans321"


  from z1 z2 show "le p11 p12 p31 & le p11 p12 p32" ..
  from z13 z14 show "ri p31 p32 p11 & ri p31 p32 p12" ..
qed -- "eses cmps rrrr = llrr"

theorem assumes an: "ba p11 p12 p21 & ba p11 p12 p22 & bo p21 p22 p11 & bo p21 p22 p12 & ba p21 p22 p31 & ba p21 p22 p32 & bo p31 p32 p21 & bo p31 p32 p22" (is "?a1 & ?a2 & ?a3 & ?a4 &?a5 & ?a6 & ?a7 & ?a8") shows "ba p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12"
proof -
  -- "Annahme zerlegen:"
  from an have a1: "?a1" by (auto)
  from an have a2: "?a2" by (auto) 
  from an have a3: "?a3" by (auto)
  from an have a4: "?a4" by (auto)
  from an have a5: "?a5" by (auto)
  from an have a6: "?a6" by (auto)
  from an have a7: "?a7" by (auto)
  from an have a8: "?a8" by (auto)

  -- "Komposition a3a5 und a4a6"  
  from a3 have b1 : "ba p11 p21 p22" by (simp add : X31) -- "trans312"
  from a4 have b2 : "fr p12 p22 p21" by (simp add : X32) -- "trans321"
  from a5 have b3 : "bo p22 p21 p31" by (simp add : X18) -- "trans213"
 
  from b1 b3 have c1: "ba p11 p21 p31" by (rule X51 [OF conjI])
  from b2 a6 have c2: "ba p12 p22 p32" by (rule X56 [OF conjI])
  
  -- "z1 z2 kurzer Weg ueber a1 a2" 
  from c1 have d1 : "fr p31 p11 p21" by (simp add : X21 ) -- "trans312"
  from c2 have d2 : "fr p32 p12 p22" by (simp add : X21 ) -- "trans312"
  from a1 have d3 : "fr p21 p11 p12" by (simp add : X21 ) -- "trans312"
  from a2 have d4 : "ba p22 p12 p11" by (simp add : X22 ) -- "trans321"
  
  from d1 d3 have "fr p31 p11 p12" by (rule X57 [OF conjI])
  then have z1: "ba p11 p12 p31" by (simp add : X25 ) -- "trans231"

  from d2 d4 have "ba p32 p12 p11" by (rule X56 [OF conjI])
  then have z2: "ba p11 p12 p32" by (simp add : X22 ) -- "trans321"

  -- "z3 z4 kurzer Weg ueber a7 a8"
  from c1 have d5 : "fr p11 p31 p21" by (simp add : X19 ) -- "trans132"
  from c2 have d6 : "fr p12 p32 p22" by (simp add : X19 ) -- "trans132"
  from a7 have d7 : "ba p21 p31 p32" by (simp add : X31 ) -- "trans312"
  from a8 have d8 : "fr p22 p32 p31" by (simp add : X32 ) -- "trans321"

  from d5 d7 have "ba p11 p31 p32" by (rule X56 [OF conjI])
  then have z3: "bo p31 p32 p11" by (simp add : X20 ) -- "trans231"

  from d6 d8 have "fr p12 p32 p31" by (rule X57 [OF conjI])
  then have z4: "bo p31 p32 p12" by (simp add : X27 ) -- "trans321"

  from z1 z2 z3 z4 show "ba p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12" by (auto)

qed -- "ffbb cmps ffbb = ffbb"

theorem assumes an: "ba p11 p12 p21 & ba p11 p12 p22 & bo p21 p22 p11 & bo p21 p22 p12 & sr p21 p22 p31 & ba p21 p22 p32 & bo p31 p32 p21 & so p31 p32 p22" (is "?a1 & ?a2 & ?a3 & ?a4 &?a5 & ?a6 & ?a7 & ?a8") shows "ba p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12"
proof -
  -- "Annahme zerlegen:"
  from an have a1: "?a1" by (auto)
  from an have a2: "?a2" by (auto) 
  from an have a3: "?a3" by (auto)
  from an have a4: "?a4" by (auto)
  from an have a5: "?a5" by (auto)
  from an have a6: "?a6" by (auto)
  from an have a7: "?a7" by (auto)
  from an have a8: "?a8" by (auto)

  -- "Komposition a3a5 und a4a6"  
  from a3 have b1: "ba p11 p21 p22" by (simp add : X31) -- "trans312"
  from a4 have b2: "fr p12 p22 p21" by (simp add : X32) -- "trans321"
  from a5 have b3: "so p22 p21 p31" by (simp add : X5) -- "trans213"
 
  from b1 b3 have c1: "ba p11 p21 p31" by (rule X52 [OF conjI])
  from b2 a6 have c2: "ba p12 p22 p32" by (rule X56 [OF conjI]) 
  
  -- "z1 z2 kurzer Weg ueber a1 a2" 
  from c1 have d1 : " fr p31 p11 p21" by (simp add : X21 ) -- "trans312"
  from c2 have d2 : " fr p32 p12 p22" by (simp add : X21 ) -- "trans312"
  from a1 have d3 : " fr p21 p11 p12" by (simp add : X21 ) -- "trans312"
  from a2 have d4 : " ba p22 p12 p11" by (simp add : X22 ) -- "trans321"
  
  from d1 d3 have "fr p31 p11 p12" by (rule X57 [OF conjI])
  then have z1: "ba p11 p12 p31" by (simp add : X25 ) -- "trans231"
  
  from d2 d4 have "ba p32 p12 p11" by (rule X56 [OF conjI])
  then have z2: "ba p11 p12 p32" by (simp add : X22 ) -- "trans321"

  -- "z3 z4 kurzer Weg ueber a7 a8"
  from c1 have d5 : "fr p11 p31 p21" by (simp add : X19 ) -- "trans132"
  from c2 have d6 : "fr p12 p32 p22" by (simp add : X19 ) -- "trans132"
  from a7 have d7 : "ba p21 p31 p32" by (simp add : X31 ) -- "trans312"
  from a8 have d8 : "so p22 p32 p31" by (simp add : X4 ) -- "trans321"

  from d5 d7 have "ba p11 p31 p32" by (rule X56 [OF conjI])
  then have z3: "bo p31 p32 p11" by (simp add : X20 ) -- "trans231"

  from d6 d8 have "fr p12 p32 p31" by (rule X59 [OF conjI])
  then have z4: "bo p31 p32 p12" by (simp add : X27 ) -- "trans321"

  from z1 z2 z3 z4 show ?thesis by (auto)

qed --"ffbb cmps efbs ffbb"

 
theorem assumes an: "ba p11 p12 p21 & ba p11 p12 p22 & bo p21 p22 p11 & bo p21 p22 p12 & bo p21 p22 p31 & ba p21 p22 p32 & fr p31 p32 p21 & fr p31 p32 p22" 
(is "?a1 & ?a2 & ?a3 & ?a4 &?a5 & ?a6 & ?a7 & ?a8") 
shows "((ba p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) |
  (fr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12) |
  (sr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
  (bo p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) | 
  (so p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12))"

proof -
  -- "Annahme zerlegen:"
  from an have a1: "?a1" by (auto)
  from an have a2: "?a2" by (auto) 
  from an have a3: "?a3" by (auto)
  from an have a4: "?a4" by (auto)
  from an have a5: "?a5" by (auto)
  from an have a6: "?a6" by (auto)
  from an have a7: "?a7" by (auto)
  from an have a8: "?a8" by (auto)

  -- "Komposition a3a5 und a4a6"  
  from a3 have b1: "ba p11 p21 p22" by (simp add : X31) -- "trans312"
  from a4 have b2: "fr p12 p22 p21" by (simp add : X32) -- "trans321"
  from a5 have b3: "ba p22 p21 p31" by (simp add : X28) -- "trans213"
 
  from b1 b3 have c1: "fr p11 p21 p31 | bo p11 p21 p31 | so p11 p21 p31" by (rule X49 [OF conjI])
  from b2 a6 have c2: "ba p12 p22 p32" by (rule X56 [OF conjI]) 

  -- "z1 z2 kurzer Weg ueber a1 a2" 
  from c1 have "bo p31 p11 p21 | bo p11 p21 p31 | so p11 p21 p31" by (simp add : X26 ) -- "trans312"
  then have "bo p31 p11 p21 | ba p31 p11 p21 | so p11 p21 p31" by (simp add : X31 )
  then have d1: "bo p31 p11 p21 | ba p31 p11 p21 | dou p31 p11 p21" by (simp add : X96 )

  from c2 have d2 : "fr p32 p12 p22" by (simp add : X21 ) -- "trans312"
  from a1 have d3 : "fr p21 p11 p12" by (simp add : X21 ) -- "trans312"
  from a2 have d4 : "ba p22 p12 p11" by (simp add : X22 ) -- "trans321"
  
  from d2 d4 have "ba p32 p12 p11" by (rule X56 [OF conjI])
  then have z2: "ba p11 p12 p32" by (simp add : X22 ) -- "trans321"

  from d1 d3 have "(bo p31 p11 p21 | ba p31 p11 p21 | dou p31 p11 p21) & fr p21 p11 p12" ..
  then have "(bo p31 p11 p21 & fr p21 p11 p12) | (ba p31 p11 p21 & fr p21 p11 p12) | (dou p31 p11 p21 & fr p21 p11 p12)" by (auto)
  with X64 have "(fr p31 p11 p12 | bo p31 p11 p12 | so p31 p11 p12) | (ba p31 p11 p21 & fr p21 p11 p12) | (dou p31 p11 p21 & fr p21 p11 p12)" by (auto)
  with X50 have "(fr p31 p11 p12 | bo p31 p11 p12 | so p31 p11 p12) | (ba p31 p11 p12) | (dou p31 p11 p21 & fr p21 p11 p12)" by (auto)
  with X116 have "(fr p31 p11 p12 | bo p31 p11 p12 | so p31 p11 p12) | (ba p31 p11 p12) | (dou p31 p11 p12)" by (auto)
  then have "((ba p11 p12 p31 | bo p31 p11 p12) | so p31 p11 p12) | (ba p31 p11 p12) | (dou p31 p11 p12)" by (simp add : X25 ) -- "trans231"
  then have "((ba p11 p12 p31 | fr p11 p12 p31) | so p31 p11 p12) | (ba p31 p11 p12) | (dou p31 p11 p12)" by (simp add : X30 ) -- "trans231"
  then have "((ba p11 p12 p31 | fr p11 p12 p31) | sr p11 p12 p31) | (ba p31 p11 p12) | (dou p31 p11 p12)" by (simp add : X3 ) -- "trans231"
  then have "((ba p11 p12 p31 | fr p11 p12 p31) | sr p11 p12 p31) | (bo p11 p12 p31) | (dou p31 p11 p12)" by (simp add : X20 ) -- "trans231"
  then have z1: "(ba p11 p12 p31) | (fr p11 p12 p31) | (sr p11 p12 p31) | (bo p11 p12 p31) | (so p11 p12 p31)" by (simp add : X92 ) -- "trans231"
  
  -- "z3 z4 kurzer Weg ueber a7 a8"
  from c1 have "ba p11 p31 p21 | bo p11 p21 p31 | so p11 p21 p31" by (simp add : X24 ) -- "trans132"
  then have "ba p11 p31 p21 | bo p11 p31 p21 | so p11 p21 p31" by (simp add : X29 ) -- "trans132"
  then have d5: "ba p11 p31 p21 | bo p11 p31 p21 | dou p11 p31 p21" by (simp add : X95 ) -- "trans132"
  
  from c2 have d6 : "fr p12 p32 p22" by (simp add : X19 ) -- "trans132"
  from a7 have d7 : "bo p21 p31 p32" by (simp add : X26 ) -- "trans312"
  from a8 have d8 : "bo p22 p32 p31" by (simp add : X27 ) -- "trans321"

  from d5 d7 have "(ba p11 p31 p21 | bo p11 p31 p21 | dou p11 p31 p21) & (bo p21 p31 p32)" by (rule conjI)
  then have "(ba p11 p31 p21 & bo p21 p31 p32) | (bo p11 p31 p21 & bo p21 p31 p32) | (dou p11 p31 p21 & bo p21 p31 p32)" by (auto)

  with X51 have "(ba p11 p31 p32) | (bo p11 p31 p21 & bo p21 p31 p32) | (dou p11 p31 p21 & bo p21 p31 p32)" by (auto)
  with X117 have "(ba p11 p31 p32) | (bo p11 p31 p21 & bo p21 p31 p32) | (dou p11 p31 p32)" by (auto)
  with X65 have "(ba p11 p31 p32) | (bo p11 p31 p32) | (dou p11 p31 p32)" sorry -- "hangs up here"

  then have "bo p31 p32 p11 | (bo p11 p31 p32) | (dou p11 p31 p32)" by (simp add : X20 ) -- "trans231"
  then have "bo p31 p32 p11 | (fr p31 p32 p11) | (dou p11 p31 p32)" by (simp add : X30 ) -- "trans231"
  then have z3: "bo p31 p32 p11 | fr p31 p32 p11 | so p31 p32 p11" by (simp add : X92 ) -- "trans231"

  from d6 d8 have "fr p12 p32 p31 | bo p12 p32 p31 | so p12 p32 p31" by (rule X58 [OF conjI])
  then have "bo p31 p32 p12 | bo p12 p32 p31 | so p12 p32 p31" by (simp add : X27 ) -- "trans321"
  then have "bo p31 p32 p12 | fr p31 p32 p12 | so p12 p32 p31" by (simp add : X32 ) -- "trans321"
  then have z4: "bo p31 p32 p12 | fr p31 p32 p12 | so p31 p32 p12" by (simp add : X4 ) -- "trans321"

-- "z11 z12 langer Weg ueber a7 a8 und a1 a2"
  from a7 have d11: "ba p31 p21 p32" by (simp add : X24 ) -- "trans132"
  from a8 have d12: "ba p32 p22 p31" by (simp add : X25 ) -- "trans231"
  from c1 d11 have "(fr p11 p21 p31 | bo p11 p21 p31 | so p11 p21 p31) & (ba p31 p21 p32)" ..
  then have "(fr p11 p21 p31 & ba p31 p21 p32) | (bo p11 p21 p31 & ba p31 p21 p32) | (so p11 p21 p31 & ba p31 p21 p32)" by (auto)
  with X56 have "ba p11 p21 p32 | (bo p11 p21 p31 & ba p31 p21 p32) | (so p11 p21 p31 & ba p31 p21 p32)" by (auto)
  with X63 have "ba p11 p21 p32 | ba p11 p21 p32 | (so p11 p21 p31 & ba p31 p21 p32)" by (auto)
  with X70 have "ba p11 p21 p32 | ba p11 p21 p32 | ba p11 p21 p32" by (auto)
  then have "ba p11 p21 p32" by (auto)
  then have e1: "fr p32 p11 p21" by (simp add : X21 ) -- "trans312"
  from c2 d12 have "fr p12 p22 p31 | bo p12 p22 p31 | so p12 p22 p31" by (rule X49 [OF conjI])
  then have "bo p31 p12 p22 | bo p12 p22 p31 | so p12 p22 p31" by (simp add : X26 ) -- "trans312"
  then have "bo p31 p12 p22 | ba p31 p12 p22 | so p12 p22 p31" by (simp add : X31 ) -- "trans312"
  then have e2: "bo p31 p12 p22 | ba p31 p12 p22 | dou p31 p12 p22" by (simp add : X96 ) -- "trans312"
  from a1 have e3: "fr p21 p11 p12" by (simp add : X21 ) -- "trans312"
  from a2 have e4: "ba p22 p12 p11" by (simp add : X22 ) -- "trans321"
  from e1 e3 have "fr p32 p11 p12" by (rule X57 [OF conjI])
  then have z12: "ba p11 p12 p32" by (simp add : X25 ) -- "trans231"
  from e2 e4 have "(bo p31 p12 p22 | ba p31 p12 p22 | dou p31 p12 p22) & (ba p22 p12 p11)" ..
  then have "(bo p31 p12 p22 & ba p22 p12 p11) | (ba p31 p12 p22 & ba p22 p12 p11) | (dou p31 p12 p22 & ba p22 p12 p11)" by (auto)
  with X63 have "ba p31 p12 p11 | (ba p31 p12 p22 & ba p22 p12 p11) | (dou p31 p12 p22 & ba p22 p12 p11)" by (auto)
  with X49 have "ba p31 p12 p11 | (fr p31 p12 p11 | bo p31 p12 p11 | so p31 p12 p11) | (dou p31 p12 p22 & ba p22 p12 p11)" by (auto)
  with X115 have "ba p31 p12 p11 | (fr p31 p12 p11 | bo p31 p12 p11 | so p31 p12 p11) | dou p31 p12 p11" by (auto)
  then have "ba p11 p12 p31 | (fr p31 p12 p11 | bo p31 p12 p11 | so p31 p12 p11) | dou p31 p12 p11" by (simp add : X22 ) -- "trans321"
  then have "ba p11 p12 p31 | (bo p11 p12 p31 | bo p31 p12 p11 | so p31 p12 p11) | dou p31 p12 p11" by (simp add : X27 ) -- "trans321"
  then have "ba p11 p12 p31 | (bo p11 p12 p31 | fr p11 p12 p31 | so p31 p12 p11) | dou p31 p12 p11" by (simp add : X32 ) -- "trans321"
  then have "ba p11 p12 p31 | (bo p11 p12 p31 | fr p11 p12 p31 | so p11 p12 p31) | dou p31 p12 p11" by (simp add : X4 ) -- "trans321"
  then have "ba p11 p12 p31 | (bo p11 p12 p31 | fr p11 p12 p31 | so p11 p12 p31) | sr p11 p12 p31" by (simp add : X94 ) -- "trans321"
  then have z11: "ba p11 p12 p31 | bo p11 p12 p31 | fr p11 p12 p31 | so p11 p12 p31 | sr p11 p12 p31" by (auto)

  -- "z13 z14 langer Weg ueber a1 a2 und a7 a8"
  from c1 have "bo p31 p21 p11 | bo p11 p21 p31 | so p11 p21 p31" by (simp add : X27 ) -- "trans321"
  then have "bo p31 p21 p11 | fr p31 p21 p11 | so p11 p21 p31" by (simp add : X32 ) -- "trans321"
  then have d15: "bo p31 p21 p11 | fr p31 p21 p11 | so p31 p21 p11" by (simp add : X4 ) -- "trans321"
  from c2 have d16 : "ba p32 p22 p12" by (simp add : X22 ) -- "trans321"
  from a1 have d17 : "fr p11 p21 p12" by (simp add : X19 ) -- "trans132"
  from a2 have d18 : "bo p12 p22 p11" by (simp add : X20 ) -- "trans231"
  from d15 d17 have "(bo p31 p21 p11 | fr p31 p21 p11 | so p31 p21 p11) & (fr p11 p21 p12)" ..
  then have "(bo p31 p21 p11 & fr p11 p21 p12) | (fr p31 p21 p11 & fr p11 p21 p12) | (so p31 p21 p11 & fr p11 p21 p12)" by (auto)
  with X64 have "(fr p31 p21 p12 | bo p31 p21 p12 | so p31 p21 p12) | (fr p31 p21 p11 & fr p11 p21 p12) | (so p31 p21 p11 & fr p11 p21 p12)" by (auto)
  with X71 have "(fr p31 p21 p12 | bo p31 p21 p12 | so p31 p21 p12) | (fr p31 p21 p11 & fr p11 p21 p12) | (fr p31 p21 p12)" by (auto)
  with X57 have "(fr p31 p21 p12 | bo p31 p21 p12 | so p31 p21 p12) | (fr p31 p21 p12) | (fr p31 p21 p12)" sorry
  then have "fr p31 p21 p12 | bo p31 p21 p12 | so p31 p21 p12" by (auto)
  then have "bo p12 p31 p21 | bo p31 p21 p12 | so p31 p21 p12" by (simp add : X26 ) -- "trans312"
  then have "bo p12 p31 p21 | ba p12 p31 p21 | so p31 p21 p12" by (simp add : X31 ) -- "trans312"
  then have e5: "bo p12 p31 p21 | ba p12 p31 p21 | dou p12 p31 p21" by (simp add : X96 ) -- "trans312"

  from d16 d18 have "ba p32 p22 p11" by (rule X51 [OF conjI])
  then have e6 : "fr p11 p32 p22" by (simp add : X21 ) -- "trans312"
  from a7 have e7 : "bo p21 p31 p32" by (simp add : X26 ) -- "trans312"
  from a8 have e8 : "bo p22 p32 p31" by (simp add : X27 ) -- "trans321"
  from e5 e7 have "(bo p12 p31 p21 | ba p12 p31 p21 | dou p12 p31 p21) & (bo p21 p31 p32)" .. 
  then have "(bo p12 p31 p21 & bo p21 p31 p32) | (ba p12 p31 p21 & bo p21 p31 p32) | (dou p12 p31 p21 & bo p21 p31 p32)" by (auto)
  with X65 have "(bo p12 p31 p32) | (ba p12 p31 p21 & bo p21 p31 p32) | (dou p12 p31 p21 & bo p21 p31 p32)" sorry
  with X51 have "(bo p12 p31 p32) | (ba p12 p31 p32) | (dou p12 p31 p21 & bo p21 p31 p32)" by (auto)
  with X117 have "(bo p12 p31 p32) | (ba p12 p31 p32) | (dou p12 p31 p32)" by (auto)
  then have "(fr p31 p32 p12) | (ba p12 p31 p32) | (dou p12 p31 p32)" by (simp add : X30 ) -- "trans231"
  then have "(fr p31 p32 p12) | (bo p31 p32 p12) | (dou p12 p31 p32)" by (simp add : X20 ) -- "trans231"
  then have z14: "(fr p31 p32 p12) | (bo p31 p32 p12) | (so p31 p32 p12)" by (simp add : X92 ) -- "trans231"
  from e6 e8 have "(fr p11 p32 p31 | bo p11 p32 p31 | so p11 p32 p31)" by (rule X58 [OF conjI])
  then have "(bo p31 p32 p11 | bo p11 p32 p31 | so p11 p32 p31)" by (simp add : X27 ) -- "trans321"
  then have "(bo p31 p32 p11 | fr p31 p32 p11 | so p11 p32 p31)" by (simp add : X32 ) -- "trans321"
  then have z13: " bo p31 p32 p11 | fr p31 p32 p11 | so p31 p32 p11" by (simp add : X4 ) -- "trans321"
  
  -- "Zusammenfasung"
  from z1 z2 have "((ba p11 p12 p31) | (fr p11 p12 p31) | (sr p11 p12 p31) | (bo p11 p12 p31) | (so p11 p12 p31)) & (ba p11 p12 p32)" ..
  then have q1: "(ba p11 p12 p31 & ba p11 p12 p32) | (fr p11 p12 p31 & ba p11 p12 p32) | (sr p11 p12 p31 & ba p11 p12 p32) | (bo p11 p12 p31 & ba p11 p12 p32) | (so p11 p12 p31 & ba p11 p12 p32)" by (auto)
  from z3 z4 have "(bo p31 p32 p11 | fr p31 p32 p11 | so p31 p32 p11) & (bo p31 p32 p12 | fr p31 p32 p12 | so p31 p32 p12)" by (auto)
  then have q2: "(bo p31 p32 p11 & bo p31 p32 p12) | (bo p31 p32 p11 & fr p31 p32 p12) | (bo p31 p32 p11 & so p31 p32 p12) | (fr p31 p32 p11 & bo p31 p32 p12) | (fr p31 p32 p11 & fr p31 p32 p12) | (fr p31 p32 p11 & so p31 p32 p12) | (so p31 p32 p11 & bo p31 p32 p12) | (so p31 p32 p11 & fr p31 p32 p12) | (so p31 p32 p11 & so p31 p32 p12)" by (auto)
  from q1 q2 have "((ba p11 p12 p31 & ba p11 p12 p32) | (fr p11 p12 p31 & ba p11 p12 p32) | (sr p11 p12 p31 & ba p11 p12 p32) | (bo p11 p12 p31 & ba p11 p12 p32) | (so p11 p12 p31 & ba p11 p12 p32)) & 
((bo p31 p32 p11 & bo p31 p32 p12) | (bo p31 p32 p11 & fr p31 p32 p12) | (bo p31 p32 p11 & so p31 p32 p12) | (fr p31 p32 p11 & bo p31 p32 p12) | (fr p31 p32 p11 & fr p31 p32 p12) | (fr p31 p32 p11 & so p31 p32 p12) | (so p31 p32 p11 & bo p31 p32 p12) | (so p31 p32 p11 & fr p31 p32 p12) | (so p31 p32 p11 & so p31 p32 p12))" by (auto)
  then have "((ba p11 p12 p31 & ba p11 p12 p32) & ((bo p31 p32 p11 & bo p31 p32 p12) | (bo p31 p32 p11 & fr p31 p32 p12) | (bo p31 p32 p11 & so p31 p32 p12) | (fr p31 p32 p11 & bo p31 p32 p12) | (fr p31 p32 p11 & fr p31 p32 p12) | (fr p31 p32 p11 & so p31 p32 p12) | (so p31 p32 p11 & bo p31 p32 p12) | (so p31 p32 p11 & fr p31 p32 p12) | (so p31 p32 p11 & so p31 p32 p12))) | 
((fr p11 p12 p31 & ba p11 p12 p32) & ((bo p31 p32 p11 & bo p31 p32 p12) | (bo p31 p32 p11 & fr p31 p32 p12) | (bo p31 p32 p11 & so p31 p32 p12) | (fr p31 p32 p11 & bo p31 p32 p12) | (fr p31 p32 p11 & fr p31 p32 p12) | (fr p31 p32 p11 & so p31 p32 p12) | (so p31 p32 p11 & bo p31 p32 p12) | (so p31 p32 p11 & fr p31 p32 p12) | (so p31 p32 p11 & so p31 p32 p12))) | 
((sr p11 p12 p31 & ba p11 p12 p32) & ((bo p31 p32 p11 & bo p31 p32 p12) | (bo p31 p32 p11 & fr p31 p32 p12) | (bo p31 p32 p11 & so p31 p32 p12) | (fr p31 p32 p11 & bo p31 p32 p12) | (fr p31 p32 p11 & fr p31 p32 p12) | (fr p31 p32 p11 & so p31 p32 p12) | (so p31 p32 p11 & bo p31 p32 p12) | (so p31 p32 p11 & fr p31 p32 p12) | (so p31 p32 p11 & so p31 p32 p12))) | 
((bo p11 p12 p31 & ba p11 p12 p32) & ((bo p31 p32 p11 & bo p31 p32 p12) | (bo p31 p32 p11 & fr p31 p32 p12) | (bo p31 p32 p11 & so p31 p32 p12) | (fr p31 p32 p11 & bo p31 p32 p12) | (fr p31 p32 p11 & fr p31 p32 p12) | (fr p31 p32 p11 & so p31 p32 p12) | (so p31 p32 p11 & bo p31 p32 p12) | (so p31 p32 p11 & fr p31 p32 p12) | (so p31 p32 p11 & so p31 p32 p12))) | 
((so p11 p12 p31 & ba p11 p12 p32) & ((bo p31 p32 p11 & bo p31 p32 p12) | (bo p31 p32 p11 & fr p31 p32 p12) | (bo p31 p32 p11 & so p31 p32 p12) | (fr p31 p32 p11 & bo p31 p32 p12) | (fr p31 p32 p11 & fr p31 p32 p12) | (fr p31 p32 p11 & so p31 p32 p12) | (so p31 p32 p11 & bo p31 p32 p12) | (so p31 p32 p11 & fr p31 p32 p12) | (so p31 p32 p11 & so p31 p32 p12)))" by (auto)
  then have "((ba p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) | 
    (ba p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12) | 
    (ba p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & bo p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & so p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & bo p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & so p31 p32 p12)) | 
((fr p11 p12 p31 & ba p11 p12 p32) & ((bo p31 p32 p11 & bo p31 p32 p12) | (bo p31 p32 p11 & fr p31 p32 p12) | (bo p31 p32 p11 & so p31 p32 p12) | (fr p31 p32 p11 & bo p31 p32 p12) | (fr p31 p32 p11 & fr p31 p32 p12) | (fr p31 p32 p11 & so p31 p32 p12) | (so p31 p32 p11 & bo p31 p32 p12) | (so p31 p32 p11 & fr p31 p32 p12) | (so p31 p32 p11 & so p31 p32 p12))) | 
((sr p11 p12 p31 & ba p11 p12 p32) & ((bo p31 p32 p11 & bo p31 p32 p12) | (bo p31 p32 p11 & fr p31 p32 p12) | (bo p31 p32 p11 & so p31 p32 p12) | (fr p31 p32 p11 & bo p31 p32 p12) | (fr p31 p32 p11 & fr p31 p32 p12) | (fr p31 p32 p11 & so p31 p32 p12) | (so p31 p32 p11 & bo p31 p32 p12) | (so p31 p32 p11 & fr p31 p32 p12) | (so p31 p32 p11 & so p31 p32 p12))) | 
((bo p11 p12 p31 & ba p11 p12 p32) & ((bo p31 p32 p11 & bo p31 p32 p12) | (bo p31 p32 p11 & fr p31 p32 p12) | (bo p31 p32 p11 & so p31 p32 p12) | (fr p31 p32 p11 & bo p31 p32 p12) | (fr p31 p32 p11 & fr p31 p32 p12) | (fr p31 p32 p11 & so p31 p32 p12) | (so p31 p32 p11 & bo p31 p32 p12) | (so p31 p32 p11 & fr p31 p32 p12) | (so p31 p32 p11 & so p31 p32 p12))) | 
((so p11 p12 p31 & ba p11 p12 p32) & ((bo p31 p32 p11 & bo p31 p32 p12) | (bo p31 p32 p11 & fr p31 p32 p12) | (bo p31 p32 p11 & so p31 p32 p12) | (fr p31 p32 p11 & bo p31 p32 p12) | (fr p31 p32 p11 & fr p31 p32 p12) | (fr p31 p32 p11 & so p31 p32 p12) | (so p31 p32 p11 & bo p31 p32 p12) | (so p31 p32 p11 & fr p31 p32 p12) | (so p31 p32 p11 & so p31 p32 p12)))" by (auto)
  
  then have "(ba p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) | 
    (ba p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12) | 
    (ba p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & bo p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & so p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & bo p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & so p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & bo p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & so p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & bo p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & so p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & bo p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & so p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & bo p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & so p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & bo p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & so p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & bo p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & so p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & bo p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & so p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & bo p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & so p31 p32 p12)" sorry

  then have "((ba p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12)) |
 
    ((ba p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & bo p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & so p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & bo p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & so p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & bo p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & so p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & bo p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & so p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & bo p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & so p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & bo p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & so p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & bo p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & so p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & bo p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & so p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & bo p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & so p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & bo p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & so p31 p32 p12))" by (auto)
  then have "(ba p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12)"  
  proof (rule disjE)
    assume "(ba p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12)" show ?thesis . 
  next
    assume "(ba p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & bo p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & so p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & bo p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & so p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & bo p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & so p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & bo p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & so p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & bo p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & so p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & bo p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & so p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & bo p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & so p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & bo p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & so p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & bo p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & so p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & bo p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & so p31 p32 p12)" show ?thesis
    proof (rule disjE)
      assume as1: "ba p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12" show ?thesis
	proof -
	  from as1 have False 
	    proof
	      from as1 have "ba p11 p12 p31" by (auto)
	      then have as11: "~ (fr p11 p12 p31)" by (rule X146) -- "pairwise disjunct!"
	      from as1 have as12: "bo p31 p32 p11 & fr p31 p32 p12" by (auto)
	      then have "ba p11 p31 p32 & fr p31 p32 p12" by (simp add : X31) --"trans312"
	      then have "ba p11 p31 p32 & fr p32 p31 p12" by (simp add : X23) --"trans213"
	      then have "ba p11 p31 p12" by (rule X50)
	      then have "fr p11 p12 p31" by (simp add : X19) --"trans132"
	      with as11 show ?thesis by (auto)
	      qed
	  then show ?thesis by (rule ccontr) 
	qed
      next
	assume as2: "(ba p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & bo p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & so p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & bo p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12) |
    (ba p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & so p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & bo p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & so p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & bo p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12) |
    (fr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & so p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & bo p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & so p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & bo p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12) |
    (sr p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & so p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & bo p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & so p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & bo p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & fr p31 p32 p12) |
    (bo p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & so p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & bo p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & fr p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & bo p31 p32 p11 & so p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & bo p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & fr p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & fr p31 p32 p11 & so p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & bo p31 p32 p12) |
    (so p11 p12 p31 & ba p11 p12 p32 & so p31 p32 p11 & so p31 p32 p12)" show ?thesis sorry
    qed
  qed
  then show ?thesis .
qed -- "ffbb cmps bfii = efbs ifbi bfii sfsi ffbb"

theorem assumes an: "ri p11 p12 p21 & ri p11 p12 p22 & ri p21 p22 p11 & ri p21 p22 p12 & ri p21 p22 p31 & ri p21 p22 p32 & ri p31 p32 p21 & ri p31 p32 p22" 
(is "?a1 & ?a2 & ?a3 & ?a4 &?a5 & ?a6 & ?a7 & ?a8") 
shows "((ri p11 p12 p31 & ri p11 p12 p32 & ri p31 p32 p11 & ri p31 p32 p12) |
  (ri p11 p12 p31 & ri p11 p12 p32 & ri p31 p32 p11 & le p31 p32 p12) |
  (ri p11 p12 p31 & ri p11 p12 p32 & le p31 p32 p11 & ri p31 p32 p12) |
  (ri p11 p12 p31 & ri p11 p12 p32 & le p31 p32 p11 & le p31 p32 p12) | 
  (ri p11 p12 p31 & le p11 p12 p32 & ri p31 p32 p11 & ri p31 p32 p12) | 
  (ri p11 p12 p31 & le p11 p12 p32 & le p31 p32 p11 & ri p31 p32 p12) | 
  (ri p11 p12 p31 & le p11 p12 p32 & le p31 p32 p11 & le p31 p32 p12) | 
  (le p11 p12 p31 & ri p11 p12 p32 & ri p31 p32 p11 & ri p31 p32 p12) | 
  (le p11 p12 p31 & ri p11 p12 p32 & ri p31 p32 p11 & le p31 p32 p12) | 
  (le p11 p12 p31 & ri p11 p12 p32 & le p31 p32 p11 & le p31 p32 p12) | 
  (le p11 p12 p31 & le p11 p12 p32 & ri p31 p32 p11 & ri p31 p32 p12) | 
  (le p11 p12 p31 & le p11 p12 p32 & ri p31 p32 p11 & le p31 p32 p12) | 
  (le p11 p12 p31 & le p11 p12 p32 & le p31 p32 p11 & ri p31 p32 p12) | 
  (le p11 p12 p31 & le p11 p12 p32 & le p31 p32 p11 & le p31 p32 p12))" 
  -- {* alle 14 realisierbaren r*l Kombinationen und noch weitere ...*}

proof
  -- "Annahme zerlegen:"
  from an have a1: "?a1" by (auto)
  from an have a2: "?a2" by (auto) 
  from an have a3: "?a3" by (auto)
  from an have a4: "?a4" by (auto)
  from an have a5: "?a5" by (auto)
  from an have a6: "?a6" by (auto)
  from an have a7: "?a7" by (auto)
  from an have a8: "?a8" by (auto)

  -- "Komposition a3a5 und a4a6"  
  from a3 have b1: "ri p11 p21 p22" by (simp add : X11) -- "trans312"
  from a4 have b2: "le p12 p22 p21" by (simp add : X12) -- "trans321"
  from a5 have b3: "le p22 p21 p31" by (simp add : X8) -- "trans213"
 
  from b1 b3 have c1: "ri p11 p21 p31 | le p11 p21 p31 | fr p11 p21 p31 | bo p11 p21 p31 | so p11 p21 p31" by (rule X34 [OF conjI])
  from b2 a6 have c2: "ri p12 p22 p32 | le p12 p22 p32 | fr p12 p22 p32 | bo p12 p22 p32 | so p12 p22 p32" by (rule X40 [OF conjI]) 
  
  -- "z1 z2 kurzer Weg ueber a1 a2" 
  from c1 have "ri p31 p11 p21 | le p11 p21 p31 | fr p11 p21 p31 | bo p11 p21 p31 | so p11 p21 p31" by (simp add : X11 ) -- "trans312"
  then have "ri p31 p11 p21 | le p31 p11 p21 | fr p11 p21 p31 | bo p11 p21 p31 | so p11 p21 p31" by (simp add : X16 ) -- "trans312"
  then have "ri p31 p11 p21 | le p31 p11 p21 | bo p31 p11 p21 | bo p11 p21 p31 | so p11 p21 p31" by (simp add : X26 ) -- "trans312"
  then have "ri p31 p11 p21 | le p31 p11 p21 | bo p31 p11 p21 | ba p31 p11 p21 | so p11 p21 p31" by (simp add : X31 ) -- "trans312"
  then have d1: "ri p31 p11 p21 | le p31 p11 p21 | bo p31 p11 p21 | ba p31 p11 p21 | dou p31 p11 p21" by (simp add : X96 ) -- "trans312"

  from c2 have "ri p32 p12 p22 | le p12 p22 p32 | fr p12 p22 p32 | bo p12 p22 p32 | so p12 p22 p32" by (simp add : X11 ) -- "trans312"
  then have "ri p32 p12 p22 | le p32 p12 p22 | fr p12 p22 p32 | bo p12 p22 p32 | so p12 p22 p32" by (simp add : X16 ) -- "trans312"
  then have "ri p32 p12 p22 | le p32 p12 p22 | bo p32 p12 p22 | bo p12 p22 p32 | so p12 p22 p32" by (simp add : X26 ) -- "trans312"
  then have "ri p32 p12 p22 | le p32 p12 p22 | bo p32 p12 p22 | ba p32 p12 p22 | so p12 p22 p32" by (simp add : X31 ) -- "trans312"
  then have d2: "ri p32 p12 p22 | le p32 p12 p22 | bo p32 p12 p22 | ba p32 p12 p22 | dou p32 p12 p22" by (simp add : X96 ) -- "trans312"

  from a1 have d3 : "ri p21 p11 p12" by (simp add : X11 ) -- "trans312"
  from a2 have d4 : "le p22 p12 p11" by (simp add : X12 ) -- "trans321"
  
  from d1 d3 have "(ri p31 p11 p21 | le p31 p11 p21 | bo p31 p11 p21 | ba p31 p11 p21 | dou p31 p11 p21) & (ri p21 p11 p12)" ..
  then have "(ri p31 p11 p21 & ri p21 p11 p12) | (le p31 p11 p21 & ri p21 p11 p12) | (bo p31 p11 p21 & ri p21 p11 p12) | (ba p31 p11 p21 & ri p21 p11 p12) | (dou p31 p11 p21 & ri p21 p11 p12)" by (auto)
  with X33 have "(ri p31 p11 p12 | le p31 p11 p12 | ba p31 p11 p12) | (le p31 p11 p21 & ri p21 p11 p12) | (bo p31 p11 p21 & ri p21 p11 p12) | (ba p31 p11 p21 & ri p21 p11 p12) | (dou p31 p11 p21 & ri p21 p11 p12)" by (auto)
  with X40 have "(ri p31 p11 p12 | le p31 p11 p12 | ba p31 p11 p12) | (ri p31 p11 p12 | le p31 p11 p12 | fr p31 p11 p12 | bo p31 p11 p12 | so p31 p11 p12) | (bo p31 p11 p21 & ri p21 p11 p12) | (ba p31 p11 p21 & ri p21 p11 p12) | (dou p31 p11 p21 & ri p21 p11 p12)" by (auto)
  then have "(ri p31 p11 p12 | le p31 p11 p12 | ba p31 p11 p12 | fr p31 p11 p12 | bo p31 p11 p12 | so p31 p11 p12) | (bo p31 p11 p21 & ri p21 p11 p12) | (ba p31 p11 p21 & ri p21 p11 p12) | (dou p31 p11 p21 & ri p21 p11 p12)" by (auto)
  with X61 have "(ri p31 p11 p12 | le p31 p11 p12 | ba p31 p11 p12 | fr p31 p11 p12 | bo p31 p11 p12 | so p31 p11 p12) | (ri p31 p11 p12) | (ba p31 p11 p21 & ri p21 p11 p12) | (dou p31 p11 p21 & ri p21 p11 p12)" by (auto)
  with X47 have "(ri p31 p11 p12 | le p31 p11 p12 | ba p31 p11 p12 | fr p31 p11 p12 | bo p31 p11 p12 | so p31 p11 p12) | (ri p31 p11 p12) | (le p31 p11 p12) | (dou p31 p11 p21 & ri p21 p11 p12)" by (auto)
  then have "(ri p31 p11 p12 | le p31 p11 p12 | ba p31 p11 p12 | fr p31 p11 p12 | bo p31 p11 p12 | so p31 p11 p12) | (dou p31 p11 p21 & ri p21 p11 p12)" by (auto)
  with X113 have "(ri p31 p11 p12 | le p31 p11 p12 | ba p31 p11 p12 | fr p31 p11 p12 | bo p31 p11 p12 | so p31 p11 p12) | (dou p31 p11 p12)" by (auto)
  then have "ri p11 p12 p31 | le p31 p11 p12 | ba p31 p11 p12 | fr p31 p11 p12 | bo p31 p11 p12 | so p31 p11 p12 | dou p31 p11 p12" by (simp add : X10 ) -- "trans231"
  then have "ri p11 p12 p31 | le p11 p12 p31 | ba p31 p11 p12 | fr p31 p11 p12 | bo p31 p11 p12 | so p31 p11 p12 | dou p31 p11 p12" by (simp add : X15 ) -- "trans231"
  then have "ri p11 p12 p31 | le p11 p12 p31 | bo p11 p12 p31 | fr p31 p11 p12 | bo p31 p11 p12 | so p31 p11 p12 | dou p31 p11 p12" by (simp add : X20 ) -- "trans231"
  then have "ri p11 p12 p31 | le p11 p12 p31 | bo p11 p12 p31 | ba p11 p12 p31 | bo p31 p11 p12 | so p31 p11 p12 | dou p31 p11 p12" by (simp add : X25 ) -- "trans231"
  then have "ri p11 p12 p31 | le p11 p12 p31 | bo p11 p12 p31 | ba p11 p12 p31 | fr p11 p12 p31 | so p31 p11 p12 | dou p31 p11 p12" by (simp add : X30 ) -- "trans231"
  then have "ri p11 p12 p31 | le p11 p12 p31 | bo p11 p12 p31 | ba p11 p12 p31 | fr p11 p12 p31 | sr p11 p12 p31 | dou p31 p11 p12" by (simp add : X3 ) -- "trans231"
  then have z1: "ri p11 p12 p31 | le p11 p12 p31 | bo p11 p12 p31 | ba p11 p12 p31 | fr p11 p12 p31 | sr p11 p12 p31 | so p11 p12 p31" by (simp add : X92 ) -- "trans231"
-- {* fuer die erste der vier Relationen sind also alle 7 Relationen moeglich, die auch in DRAf repraesentiert sind, was nach der kompositionstabelle auch notwendig ist. dou & tri sind jedoch ausgeschlossen. *}

  from d2 d4 have " p32 p12 p11" by (rule X [OF conjI])
  then have z2: " p11 p12 p32" by (simp add : X ) -- "trans321"

  -- "z3 z4 kurzer Weg ueber a7 a8"
  from c1 have d5 : " p11 p31 p21" by (simp add : X ) -- "trans132"
  from c2 have d6 : " p12 p32 p22" by (simp add : X ) -- "trans132"
  from a7 have d7 : " p21 p31 p32" by (simp add : X ) -- "trans312"
  from a8 have d8 : " p22 p32 p31" by (simp add : X ) -- "trans321"

  from d5 d7 have " p11 p31 p32" by (rule X [OF conjI])
  then have z3: " p31 p32 p11" by (simp add : X ) -- "trans231"

  from d6 d8 have " p12 p32 p31" by (rule X [OF conjI])
  then have z4: " p31 p32 p12" by (simp add : X ) -- "trans321"

  -- "z11 z12 langer Weg ueber a7 a8 und a1 a2"
  from a7 have d11: " p31 p21 p32" by (simp add : X ) -- "trans132"
  from a8 have d12: " p32 p22 p31" by (simp add : X ) -- "trans231"
  from c1 d11 have " p11 p21 p32" by (rule X [OF conjI])
  then have e1: " p32 p11 p21" by (simp add : X ) -- "trans312"
  from c2 d12 have " p12 p22 p31" by (rule X [OF conjI])
  then have e2: " p31 p12 p22" by (simp add : X ) -- "trans312"
  from a1 have e3: " p21 p11 p12" by (simp add : X ) -- "trans312"
  from a2 have e4: " p22 p12 p11" by (simp add : X ) -- "trans321"
  from e1 e3 have " p32 p11 p12" by (rule X [OF conjI])
  then have z12: " p11 p12 p32" by (simp add : X ) -- "trans231"
  from e2 e4 have " p31 p12 p11" by (rule X [OF conjI])
  then have z11: " p11 p12 p31" by (simp add : X ) -- "trans321"

  -- "z13 z14 langer Weg ueber a1 a2 und a7 a8"
  from c1 have d15 : " p31 p21 p11" by (simp add : X ) -- "trans321"
  from c2 have d16 : " p32 p22 p12" by (simp add : X ) -- "trans321"
  from a1 have d17 : " p11 p21 p12" by (simp add : X ) -- "trans132"
  from a2 have d18 : " p12 p22 p11" by (simp add : X ) -- "trans231"
  from d15 d17 have " p31 p21 p12" by (rule X [OF conjI])
  then have e5 : " p12 p31 p21" by (simp add : X ) -- "trans312"
  from d16 d18 have " p32 p22 p11" by (rule X [OF conjI])
  then have e6 : " p11 p32 p22" by (simp add : X ) -- "trans312"
  from a7 have e7 : " p21 p31 p32" by (simp add : X ) -- "trans312"
  from a8 have e8 : " p22 p32 p31" by (simp add : X ) -- "trans321"
  from e5 e7 have " p12 p31 p32" by (rule X [OF conjI])
  then have z14: " p31 p32 p12" by (simp add : X ) -- "trans231"
  from e6 e8 have " p11 p32 p31" by (rule X [OF conjI])
  then have z13: " p31 p32 p11" by (simp add : X ) -- "trans321"

  -- "Zusammenfasung"
  from z1(z11) z2(z12) z3(z13) z4(z14) show ?thesis by (auto) 
qed -- "rrrr cmps rrrr = ..."

end

-- {* Beweisschema *}
theorem assumes an: "( p11 p12 p21 &  p11 p12 p22 &  p21 p22 p11 &  p21 p22 p12 & ( p21 p22 p31 &  p21 p22 p32 &  p31 p32 p21 &  p31 p32 p22)" (is "?a1 & ?a2 & ?a3 & ?a4 &?a5 & ?a6 & ?a7 & ?a8") shows " p11 p12 p31 &  p11 p12 p32 &  p31 p32 p11 &  p31 p32 p12"
proof
  -- "Annahme zerlegen:"
  from an have a1: "?a1" by (auto)
  from an have a2: "?a2" by (auto) 
  from an have a3: "?a3" by (auto)
  from an have a4: "?a4" by (auto)
  from an have a5: "?a5" by (auto)
  from an have a6: "?a6" by (auto)
  from an have a7: "?a7" by (auto)
  from an have a8: "?a8" by (auto)

  - "Komposition a3a5 und a4a6"  
  from a3 have b1: " p11 p21 p22" by (simp add : X) -- "trans312"
  from a4 have b2: " p12 p22 p21" by (simp add : X) -- "trans321"
  from a5 have b3: " p22 p21 p31" by (simp add : X) -- "trans213"
 
  from b1 b3 have c1: " p11 p21 p31" by (rule X [OF conjI])
  from b2 a6 have c2: " p12 p22 p32" by (rule X [OF conjI]) 
  
  -- "z1 z2 kurzer Weg ueber a1 a2" 
  from c1 have d1 : " p31 p11 p21" by (simp add : X ) -- "trans312"
  from c2 have d2 : " p32 p12 p22" by (simp add : X ) -- "trans312"
  from a1 have d3 : " p21 p11 p12" by (simp add : X ) -- "trans312"
  from a2 have d4 : " p22 p12 p11" by (simp add : X ) -- "trans321"
  
  from d1 d3 have " p31 p11 p12" by (rule X [OF conjI])
  then have z1: " p11 p12 p31" by (simp add : X ) -- "trans231"
  
  from d2 d4 have " p32 p12 p11" by (rule X [OF conjI])
  then have z2: " p11 p12 p32" by (simp add : X ) -- "trans321"

  -- "z3 z4 kurzer Weg ueber a7 a8"
  from c1 have d5 : " p11 p31 p21" by (simp add : X ) -- "trans132"
  from c2 have d6 : " p12 p32 p22" by (simp add : X ) -- "trans132"
  from a7 have d7 : " p21 p31 p32" by (simp add : X ) -- "trans312"
  from a8 have d8 : " p22 p32 p31" by (simp add : X ) -- "trans321"

  from d5 d7 have " p11 p31 p32" by (rule X [OF conjI])
  then have z3: " p31 p32 p11" by (simp add : X ) -- "trans231"

  from d6 d8 have " p12 p32 p31" by (rule X [OF conjI])
  then have z4: " p31 p32 p12" by (simp add : X ) -- "trans321"

  -- "z11 z12 langer Weg ueber a7 a8 und a1 a2"
  from a7 have d11: " p31 p21 p32" by (simp add : X ) -- "trans132"
  from a8 have d12: " p32 p22 p31" by (simp add : X ) -- "trans231"
  from c1 d11 have " p11 p21 p32" by (rule X [OF conjI])
  then have e1: " p32 p11 p21" by (simp add : X ) -- "trans312"
  from c2 d12 have " p12 p22 p31" by (rule X [OF conjI])
  then have e2: " p31 p12 p22" by (simp add : X ) -- "trans312"
  from a1 have e3: " p21 p11 p12" by (simp add : X ) -- "trans312"
  from a2 have e4: " p22 p12 p11" by (simp add : X ) -- "trans321"
  from e1 e3 have " p32 p11 p12" by (rule X [OF conjI])
  then have z12: " p11 p12 p32" by (simp add : X ) -- "trans231"
  from e2 e4 have " p31 p12 p11" by (rule X [OF conjI])
  then have z11: " p11 p12 p31" by (simp add : X ) -- "trans321"

  -- "z13 z14 langer Weg ueber a1 a2 und a7 a8"
  from c1 have d15 : " p31 p21 p11" by (simp add : X ) -- "trans321"
  from c2 have d16 : " p32 p22 p12" by (simp add : X ) -- "trans321"
  from a1 have d17 : " p11 p21 p12" by (simp add : X ) -- "trans132"
  from a2 have d18 : " p12 p22 p11" by (simp add : X ) -- "trans231"
  from d15 d17 have " p31 p21 p12" by (rule X [OF conjI])
  then have e5 : " p12 p31 p21" by (simp add : X ) -- "trans312"
  from d16 d18 have " p32 p22 p11" by (rule X [OF conjI])
  then have e6 : " p11 p32 p22" by (simp add : X ) -- "trans312"
  from a7 have e7 : " p21 p31 p32" by (simp add : X ) -- "trans312"
  from a8 have e8 : " p22 p32 p31" by (simp add : X ) -- "trans321"
  from e5 e7 have " p12 p31 p32" by (rule X [OF conjI])
  then have z14: " p31 p32 p12" by (simp add : X ) -- "trans231"
  from e6 e8 have " p11 p32 p31" by (rule X [OF conjI])
  then have z13: " p31 p32 p11" by (simp add : X ) -- "trans321"

  -- "Zusammenfasung"
  from z1(z11) z2(z12) z3(z13) z4(z14) show ?thesis by (auto) 

qed

