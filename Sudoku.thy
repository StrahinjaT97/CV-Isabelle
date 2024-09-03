theory Sudoku
  imports Main
begin

datatype number = one ("\<one>") | two ("\<two>") | three ("\<three>") | four ("\<four>") | five ("\<five>") | six ("\<six>") | seven ("\<seven>") | eight ("\<eight>") | nine ("\<nine>")


type_synonym cell = "number \<times> number"

locale Sudoku =
  fixes s :: "cell \<Rightarrow> number"

  assumes At_Most_One_Per_Row: "\<forall>x y1 y2::number.(s (x, y1) = s (x, y2) \<longrightarrow> y1 = y2)"
  assumes At_Most_One_Per_Col: "\<forall>y x1 x2::number.(s (x1, y) = s(x2, y) \<longrightarrow> x1 = x2)"
  assumes At_Least_One_Per_Row: "\<forall>x z::number.\<exists>y::number.(s (x, y) = z)"
  assumes At_Least_One_Per_Col: "\<forall>y z::number.\<exists>x::number.(s (x, y) = z)"

  fixes grid :: "number \<Rightarrow> number \<Rightarrow> bool"
  assumes Reflexive_Grid:  "\<forall>x::number.(grid x x)"
  assumes Symmetric_Grid:  "\<forall>x y::number.(grid x y \<longrightarrow> grid y x)"
  assumes Transitive_Grid: "\<forall>x y z::number.(grid x y \<and> grid y z \<longrightarrow> grid x z)"
  assumes At_Most_One_Per_Grid: "\<forall>x1 x2 y1 y2::number.(grid x1 y1 \<and> grid x2 y2 \<and> s (x1, x2) = s (y1, y2) \<longrightarrow>
                                 x1 = y1 \<and> x2 = y2)"

  assumes Const_Grid: "grid one two \<and>
                       grid two three \<and>
                       grid four five \<and>
                       grid five six \<and>
                       grid seven eight \<and>
                       grid eight nine"


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


end