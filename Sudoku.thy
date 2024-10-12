theory Sudoku
  imports Main GridGame
begin

text \<open>
  Here we define a theory about Sudoku games. We first start of with an arbitrary nxn Sudoku game with
  arbitrary style of grids/regions and then further on we define special cases of Sudoku games like
  Killer Sudoku etc.
\<close>

text \<open>
  A classical Sudoku is just a RegionGridGame that has the rules that each row/column must have exactly one
  copy of each element of the Result set; that each grid can have at most (this is a sufficient condition)
  one copy of each element from the Result set along side one constraint - number set and resulting set are same.
\<close>

locale Sudoku = RegionGridGame +
  constrains circ :: "'a \<times> 'a \<Rightarrow> 'a"

  assumes At_Most_One_Per_Row:  "\<forall>x y1 y2.(\<circ> (x, y1) = \<circ> (x, y2) \<longrightarrow> y1 = y2)"
  assumes At_Most_One_Per_Col:  "\<forall>x1 x2 y.(\<circ> (x1, y) = \<circ> (x2, y) \<longrightarrow> x1 = x2)"
  assumes At_Least_One_Per_Row: "\<forall>x z.\<exists>y.(\<circ> (x, y) = z)"
  assumes At_Least_One_Per_Col: "\<forall>y z.\<exists>x.(\<circ> (x, y) = z)"
  
  assumes At_Most_One_Per_Grid: "\<forall>x1 x2 y1 y2.(\<rr> x1 x2 \<and> \<rr> y1 y2 \<and> \<circ> (x1, y1) = \<circ> (x2, y2) \<longrightarrow>
                                 x1 = x2 \<and> y1 = y2)"


begin

text \<open>
  We can now prove that the rule that each grid must have at least one copy of each element from the Result set
  is implied by the given axioms of Sudoku.
\<close>
lemma At_Least_One_Per_Grid: "\<forall>x y.(\<rr> x y \<longrightarrow> (\<exists>z.(\<circ> (x, y) = z)))"
  by blast

text \<open>
  Even tho blast made a short work out of the previous lemma, since this is an exemplary program to showcase
  my work, I provided a human written proof.
\<close>
lemma At_Least_One_Per_Grid_Alone: "\<forall>x y.(\<rr> x y \<longrightarrow> (\<exists>z.(\<circ> (x, y) = z)))"
proof
  fix x
  show "\<forall>y.(\<rr> x y \<longrightarrow> (\<exists>z.(\<circ> (x, y) = z)))"
  proof
    fix y
    show "\<rr> x y \<longrightarrow> (\<exists>z.(\<circ> (x, y) = z))"
    proof
      assume r: "\<rr> x y"
      show "\<exists>z.(\<circ> (x, y) = z)"
      proof (rule ccontr)
        assume "\<nexists>z.(\<circ> (x, y) = z)"
        then have "\<forall>z.(\<circ> (x, y) \<noteq> z)"
          by simp
        then have a:"\<forall>z.\<nexists>x.(\<circ> (x, y) = z)"
          by simp
        have "\<forall>z.\<exists>x.(\<circ> (x, y) = z)"
          using At_Least_One_Per_Col by simp
        then show False
          using a by simp
      qed
    qed
  qed
qed

end

text \<open>
  Proof of concept that a real life sudoku is indeed a model of the  previous algebraic structure.

  A Sudoku9 is nothing more than a model with added axiom for grid formation. Should have we used a 4x4
  sudoku (Sudoku4 if we wanted to have a consistent naming scheme), Const_Grid axiom would be something like:
  
  assume Const_Grid: "\<rr> one two \<and> \<rr> three four"
\<close>

datatype number = one ("\<one>") | two ("\<two>") | three ("\<three>") | four ("\<four>") | five ("\<five>") | six ("\<six>") | seven ("\<seven>") | eight ("\<eight>") | nine ("\<nine>")
type_synonym cell = "number \<times> number"

locale Sudoku9 = Sudoku +
  constrains circ :: "cell \<Rightarrow> number"
  constrains region :: "number \<Rightarrow> number \<Rightarrow> bool"

  assumes Const_Grid: "\<rr> \<one> \<two> \<and>
                       \<rr> \<two> \<three> \<and>
                       \<rr> \<four> \<five> \<and>
                       \<rr> \<five> \<six> \<and>
                       \<rr> \<seven> \<eight> \<and>
                       \<rr> \<eight> \<nine>"

begin
lemma "\<not>(
  s (\<one>, \<one>) = \<nine>   \<and> s (\<one>, \<two>) = x12 \<and> s (\<one>, \<three>) = x13 \<and> s (\<one>, \<four>) = x14 \<and> s (\<one>, \<five>) = \<five>   \<and> s (\<one>, \<six>) = x16 \<and> s (\<one>, \<seven>) = x17 \<and> s (\<one>, \<eight>) = \<four>   \<and> s (\<one>, \<nine>) = x19 \<and>
  s (\<two>, \<one>) = \<four>   \<and> s (\<two>, \<two>) = x22 \<and> s (\<two>, \<three>) = x23 \<and> s (\<two>, \<four>) = \<seven>   \<and> s (\<two>, \<five>) = x25 \<and> s (\<two>, \<six>) = \<three>   \<and> s (\<two>, \<seven>) = x27 \<and> s (\<two>, \<eight>) = x28 \<and> s (\<two>, \<nine>) = \<one>   \<and>
  s (\<three>, \<one>) = x31 \<and> s (\<three>, \<two>) = x32 \<and> s (\<three>, \<three>) = \<two>   \<and> s (\<three>, \<four>) = x34 \<and> s (\<three>, \<five>) = x35 \<and> s (\<three>, \<six>) = x36 \<and> s (\<three>, \<seven>) = \<six>   \<and> s (\<three>, \<eight>) = x38 \<and> s (\<three>, \<nine>) = x39 \<and>

  s (\<four>, \<one>) = x41 \<and> s (\<four>, \<two>) = x42 \<and> s (\<four>, \<three>) = \<nine>   \<and> s (\<four>, \<four>) = \<five>   \<and> s (\<four>, \<five>) = x45 \<and> s (\<four>, \<six>) = x46 \<and> s (\<four>, \<seven>) = x47 \<and> s (\<four>, \<eight>) = x48 \<and> s (\<four>, \<nine>) = \<seven>   \<and>
  s (\<five>, \<one>) = x51 \<and> s (\<five>, \<two>) = \<four>   \<and> s (\<five>, \<three>) = x53 \<and> s (\<five>, \<four>) = x54 \<and> s (\<five>, \<five>) = x55 \<and> s (\<five>, \<six>) = x56 \<and> s (\<five>, \<seven>) = x57 \<and> s (\<five>, \<eight>) = \<three>   \<and> s (\<five>, \<nine>) = x59 \<and>
  s (\<six>, \<one>) = \<two>   \<and> s (\<six>, \<two>) = x62 \<and> s (\<six>, \<three>) = x63 \<and> s (\<six>, \<four>) = x64 \<and> s (\<six>, \<five>) = x65 \<and> s (\<six>, \<six>) = \<nine>   \<and> s (\<six>, \<seven>) = \<one>   \<and> s (\<six>, \<eight>) = x68 \<and> s (\<six>, \<nine>) = x69 \<and>

  s (\<seven>, \<one>) = x71 \<and> s (\<seven>, \<two>) = x72 \<and> s (\<seven>, \<three>) = \<four>   \<and> s (\<seven>, \<four>) = x74 \<and> s (\<seven>, \<five>) = x75 \<and> s (\<seven>, \<six>) = x76 \<and> s (\<seven>, \<seven>) = \<three>   \<and> s (\<seven>, \<eight>) = x78 \<and> s (\<seven>, \<nine>) = x79 \<and>
  s (\<eight>, \<one>) = \<seven>   \<and> s (\<eight>, \<two>) = x82 \<and> s (\<eight>, \<three>) = x83 \<and> s (\<eight>, \<four>) = \<four>   \<and> s (\<eight>, \<five>) = x85 \<and> s (\<eight>, \<six>) = \<two>   \<and> s (\<eight>, \<seven>) = x87 \<and> s (\<eight>, \<eight>) = x88 \<and> s (\<eight>, \<nine>) = \<eight>   \<and>
  s (\<nine>, \<one>) = x91 \<and> s (\<nine>, \<two>) = \<nine>   \<and> s (\<nine>, \<three>) = x93 \<and> s (\<nine>, \<four>) = x94 \<and> s (\<nine>, \<five>) = \<eight>   \<and> s (\<nine>, \<six>) = x96 \<and> s (\<nine>, \<seven>) = x97 \<and> s (\<nine>, \<eight>) = x98 \<and> s (\<nine>, \<nine>) = \<six>
)"
  nitpick[expect=genuine]
  oops
end
  

text \<open>
  SudokuX is basically a normal sudoku with added constraint that both main and side diagonal is considered
  a grid. Here we had to introduce two new grids (\<mm> and \<ss>) since the central square (that would be
  square (5, 5) in Sudoku9) which is a part of both diagonals, would merge them into one big grid due
  to transitivity of both gird-diagonals.

  Const_Main_Diag: is just a fancy way to say that all squares in that diagonal are (i, i)

  Side_Diag_Symmetry1/2: is just a fancy way to say all squares in that diagonal are (i, n-i)
\<close>
locale SudokuX = Sudoku + 
  fixes mainDiag :: "('a \<times> 'a) \<Rightarrow> ('a \<times> 'a) \<Rightarrow> bool" ("\<mm>")
  fixes sideDiag :: "('a \<times> 'a) \<Rightarrow> ('a \<times> 'a) \<Rightarrow> bool" ("\<ss>")

  assumes Reflexive_Main_Diag:  "\<forall>x.(\<mm> x x)"
  assumes Symmetric_Main_Diag:  "\<forall>x y.(\<mm> x y \<longrightarrow> \<mm> y x)"
  assumes Transitive_Main_Diag: "\<forall>x y z.(m x y \<and> \<mm> y z \<longrightarrow> \<mm> x z)"

  assumes At_Most_One_Main_Diag: "\<forall>x1 y1 x2 y2::'a.(\<mm> (x1, y1) (x2, y2) \<and> \<circ> (x1, y1) = \<circ> (x2, y2) \<longrightarrow>
                                                  x1 = x2 \<and> y1 = y2)"

  assumes Const_Main_Diag: "\<forall>x1 y1 x2 y2::'a.(x1 \<noteq> y1 \<or> x2 \<noteq> y2 \<longrightarrow> \<not>\<mm> (x1, y1) (x2, y2))"

  assumes Reflexive_Side_Diag:  "\<forall>x.(\<ss> x x)"
  assumes Symmetric_Side_Diag:  "\<forall>x y.(\<ss> x y \<longrightarrow> \<ss> y x)"
  assumes Transitive_Side_Diag: "\<forall>x y z.(\<ss> x y \<and> \<ss> y z \<longrightarrow> \<ss> x z)"

  assumes At_Most_One_Side_Diag: "\<forall>x1 y1 x2 y2::'a.(\<ss> (x1, y1) (x2, y2) \<and> \<circ> (x1, y1) = \<circ> (x2, y2) \<longrightarrow>
                                                  x1 = x2 \<and> y1 = y2)"

  assumes Side_Diag_Symmetry1: "\<forall>x1 y1 x2 y2::'a.(\<ss> (x1, y1) (x2, y2) \<longrightarrow> \<ss> (y1, x1) (x2, y2))"
  assumes Side_Diag_Symmetry2: "\<forall>x1 y1 x2 y2::'a.(\<ss> (x1, y1) (x2, y2) \<longrightarrow> \<ss> (x1, y1) (y2, x2))"

begin

text \<open>
  As before, we prove that lemmas that at least one element from the Resulting set needs to be in either one
  of the fields in the diagonal.
  The proofs are identical for both diagonals and are very similar to the analogous lemma in Sudoku locale, so we
  shall not explicitly state them here. Instead we let our dear friend Isabelle do all the work for us.
\<close>
  
  lemma At_Least_One_Main_Diag: "\<forall>x1 y1 x2 y2::'a.(\<mm> (x1, y1) (x2, y2) \<longrightarrow> (\<exists>z.(\<circ> (x1, y1) = z \<or> \<circ> (x2, y2) = z)))"
    by blast

  lemma At_Least_One_Side_Diag: "\<forall>x1 y1 x2 y2::'a.(\<ss> (x1, y1) (x2, y2) \<longrightarrow> (\<exists>z.(\<circ> (x1, y1) = z \<or> \<circ> (x2, y2) = z)))"
    by blast

end

text \<open>
  Another proof of concept.
  
  We can say that Sudoku9X is a model for both a Sudoku9 and SudokuX structures, thus evading the need to
  write unnecessary constraints.

   We only need one constraint for one of the diagonals, since the other one
  will implicitly gain the same constraint.
  
  We make extra care not merge main and side diagonals!
\<close>
locale Sudoku9X = SudokuX + Sudoku9 +
  constrains mainDiag :: "cell \<Rightarrow> cell \<Rightarrow> bool"

  assumes Const_Main_Diag: "\<forall>x1 y1 x2 y2::number.(x1 \<noteq> y1 \<or> x2 \<noteq> y2 \<longrightarrow> \<not>\<mm> (x1, y1) (x2, y2))"
  assumes Const_Side_Diag: "\<ss> (\<one>, \<nine>) (\<two>, \<eight>) \<and>
                            \<ss> (\<two>, \<eight>) (\<three>, \<seven>) \<and>
                            \<ss> (\<three>, \<seven>) (\<four>, \<six>) \<and>
                            \<ss> (\<four>, \<six>) (\<five>, \<five>)"
  
begin

(*TODO: Give example*)

end


locale JigSawSudoku = Sudoku +
  constrains region :: "('a \<times> 'a) \<Rightarrow> ('a \<times> 'a) \<Rightarrow> bool"


locale KillerSudoku = Sudoku + 
  fixes cage :: "(('a \<times> 'a) list \<Rightarrow> number) \<Rightarrow> bool" ("\<cc>")


end