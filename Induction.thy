theory Induction
  imports Main
begin

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys" |
"itrev (Cons x xs) ys = itrev xs (Cons x ys)"

value "itrev [Suc 0, Suc 2, Suc 3] []"

lemma itrev_rev : "itrev xs ys = (rev xs)@ys"
  apply(induction xs arbitrary: ys)
   apply(auto)
  done

end