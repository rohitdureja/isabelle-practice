theory Exercises2_09
  imports Main
begin

(*---------------- Exercise 2.9----------------*)
(* add function *)
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 y = y" |
"add (Suc x) y = Suc(add x y)"

(* tail recursive add function *)
fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 y = y" |
"itadd (Suc x) y = itadd x (Suc y)"

lemma suc_add : "add x (Suc y) = add (Suc x) y"
  apply(induction x)
   apply(auto)
  done

theorem itadd_add : "itadd x y = add x y"
  apply(induction x arbitrary: y)
  apply(auto)
   apply(simp add: suc_add)
  done



end