theory Exercises2_05
  imports Main
begin

(*---------------- Exercise 2.5----------------*)
(* sum function *)
fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto (Suc n) = (Suc n) + sum_upto n"

theorem correct_sum : "sum_upto n = n * (n + 1) div 2"
  apply(induction n)
   apply(auto)
  done

end