theory Exercises2_03
  imports Main
begin

(*---------------- Exercise 2.3----------------*)
(* count function *)
fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count x [] = 0" |
"count x (Cons y xs) = (if x=y  then Suc (count x xs) else (count x xs))"

theorem countlength : "(count x xs) \<le> List.length xs"
  apply(induction xs)
   apply(auto)
  done

end