theory StarBattle
  imports Main
begin

(*
This is only a proof of concept!

Automatic solver for Star Battle puzzle game.
Used to solve Star Battles on site:
https://www.puzzle-star-battle.com/

StarBattleOneStar - solves 1\<star> puzzles
*)


(*type_synonym cell = "nat \<times> nat"*)


datatype Five = one ("1") | two ("2") | three ("3") | four ("4") | five ("5")

fun addFive :: "Five \<Rightarrow> Five \<Rightarrow> Five" where
  "addFive _ five = five"
| "addFive _ four = five"
| "addFive one three = four"
| "addFive _ three = five"
| "addFive one two = three"
| "addFive two two = four"
| "addFive _ two = five"
| "addFive one one = two"
| "addFive two one = three"
| "addFive three one = four"
| "addFive _ one = five"

abbreviation add :: "Five \<Rightarrow> Five \<Rightarrow> Five" (infixl "[+]" 50) where
  "x [+] y \<equiv> addFive x y"


type_synonym cell = "Five \<times> Five"


fun check_if_neighbours :: "cell \<Rightarrow> cell \<Rightarrow> bool" where
   "check_if_neighbours c1 c2 = 
      (if c1 = c2 then True 
      else (
        if fst(c1) [+] one = fst(c2) \<and> snd(c1) [+] one = snd(c2) then True
        else (
          if fst(c1) = fst(c2) \<and> snd(c1) [+] one = snd(c2) then True
          else (
            if fst(c2) [+] one = fst(c1) \<and> snd(c1) [+] one = snd(c2) then True
            else (
              if fst(c1) [+] one = fst(c2) \<and> snd(c1) = snd(c2) then True
              else (
                if fst(c2) [+] one = fst(c1) \<and> snd(c1) = snd(c2) then True
                else (
                  if fst(c1) [+] one = fst(c2) \<and> snd(c2) [+] one = snd(c1) then True
                  else (
                    if fst(c1) = fst(c2) \<and> snd(c2) [+] one = snd(c1) then True
                    else (
                      if fst(c2) [+] one = fst(c1) \<and> snd(c2) [+] one = snd(c1) then True
                      else False
                    )
                  )
                )
              )
            )
          )
        )
      )
  )"




locale StarBattleOneStar = 
  fixes sb :: "cell \<Rightarrow> bool"

  assumes Exactly_One_Per_Row: "\<forall>x::Five.\<exists>!y::Five.(sb (x, y))"
  assumes Exactly_One_Per_Col: "\<forall>y::Five.\<exists>!x::Five.(sb (x, y))"

  fixes grid :: "cell \<Rightarrow> cell \<Rightarrow> bool"

  assumes Reflective_Grid:  "\<forall>c::cell.(grid c c)"
  assumes Symmetrical_Grid: "\<forall>c1 c2::cell.(grid c1 c2 \<longrightarrow> grid c2 c1)"
  assumes Transitive_Grid:  "\<forall>c1 c2 c3::cell.(grid c1 c2 \<and> grid c2 c3 \<longrightarrow> grid c1 c3)"

  assumes Exactly_One_Per_Grid: "\<forall>c1 c2::cell.(grid c1 c2 \<and> sb c1 \<and> sb c2 \<longrightarrow> c1 = c2)"

  assumes No_Adjacent_Stars: "\<forall>c1 c2::cell.(c1 \<noteq> c2 \<and> sb c1 \<and> check_if_neighbours c1 c2 \<longrightarrow> \<not>sb c2)"

begin

lemma test: "\<not>(
  sb (one, one) = x11 \<and> sb (one, two) = x12 \<and> sb (one, three) = x13 \<and> sb (one, four) = x14 \<and> sb (one, five) = x15 \<and>
  sb (two, one) = x21 \<and> sb (two, two) = x22 \<and> sb (two, three) = x23 \<and> sb (two, four) = x24 \<and> sb (two, five) = x25 \<and>
  sb (three, one) = x31 \<and> sb (three, two) = x32 \<and> sb (three, three) = x33 \<and> sb (three, four) = x34 \<and> sb (three, five) = x35 \<and>
  sb (four, one) = x41 \<and> sb (four, two) = x42 \<and> sb (four, three) = x43 \<and> sb (four, four) = x44 \<and> sb (four, five) = x45 \<and>
  sb (five, one) = x51 \<and> sb (five, two) = x52 \<and> sb (five, three) = x53 \<and> sb (five, four) = x54 \<and> sb (five, five) = x55 \<and>

  grid (one, one) (two, one) \<and> grid (two, one) (two, two) \<and> grid (two, two) (three, two) \<and> grid (three, two) (three, one) \<and> grid (three, one) (four,one) \<and> grid (four, one) (four, two) \<and> grid (four, two) (five, two) \<and> grid (five, two) (five, one) \<and>
  grid (one, two) (one, three) \<and> grid (one, three) (one, four) \<and> grid (one, four) (two, four) \<and> grid (two, four) (two, three) \<and>
  gird (three, three) (three, four) \<and> grid (three, three) (four, three) \<and> grid (four, three) (five, three) \<and>
  grid (four, four) (four, five) \<and> grid (four, five) (five, five) \<and> grid (five, five) (five, four) \<and>
  grid (one, five) (two, five) \<and> grid (two, five) (three, five)
)"          
 nitpick [expect=genuine]
  oops

end

end


