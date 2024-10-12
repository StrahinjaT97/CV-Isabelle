theory GridGame
  imports Main
begin

text \<open>
  We define a grid game as a game where each grid is filled with a element of some set

  GridGame ::= (S, P, \<circ>) is an algebraic structure of signature (\<circ>) of arity 2 that maps \<circ> : S \<times> S \<longrightarrow> P, where
  S - is a number set representing a possible coordinate of a given field
  P - is a resulting set
  
  For example in a classic sudoku game:
  S = {1, 2, 3, 4, 5, 6, 7, 8, 9}
  P = {1, 2, 3, 4, 5, 6, 7, 8, 9}
  
  but in a 4x4 Star Battle game:
  S = {1, 2, 3, 4}
  P = {x, \<star>}
\<close>
locale GridGame = 
  fixes circ :: "'a \<times> 'a \<Rightarrow> 'b"  ("\<circ>")


text \<open>
  Lets add on our structure a grid game with regions

  RegionGridGame ::= (S, P, \<circ>, \<gg>) is an algebraic structure of signature (\<circ>, \<rr>) of arity (2, 2) that maps
  \<circ> : S \<times> S \<longrightarrow> P
  \<rr> \<subseteq> S \<times> S
  with axioms
  (RST) \<gg> is reflexive, symmetric and transitive
  
  For example a \<rr> in sudoku would group together a 3x3 region into grids
\<close>

locale RegionGridGame = GridGame +
  fixes region :: "'a \<Rightarrow> 'a \<Rightarrow> bool" ("\<rr>")

  assumes Reflexive_Region[intro, simp]:  "\<forall>x.(\<rr> x x)"
  assumes Symmetric_Region[intro, simp]:  "\<forall>x y.(\<rr> x y \<longrightarrow> \<rr> y x)"
  assumes Transitive_Region[intro, simp]: "\<forall>x y z.(\<rr> x y \<and> \<rr> y z \<longrightarrow> \<rr> x z)"

  

end