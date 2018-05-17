theory Exercises3_02
  imports Main
begin
(*---------------- Exercise 3.2----------------*)
(* palindrone function*)
inductive palindrome :: "'a list \<Rightarrow> bool" where
empty:      "palindrome []" |
singleton:  "palindrome [x]" |
general:    "palindrome xs \<Longrightarrow> palindrome ((a#xs)@[a])"

lemma reverse : "palindrome xs \<Longrightarrow> (rev xs = xs)"
  apply(induction rule: palindrome.induct)
  by (simp_all)

end