theory Exercises2_04
  imports Main
begin

(*---------------- Exercise 2.4----------------*)
(* snoc function -- reverse of cons *)
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc Nil a = (Cons a Nil)" |
"snoc (Cons x xs) a = (Cons x (snoc xs a))"

(* reverse function*)
fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse Nil = Nil" |
"reverse (Cons x xs) = snoc (reverse xs) x"

lemma snoc_reverse : "reverse(snoc xs a) = a # reverse xs"
  apply(induction xs)
   apply(auto)
  done


theorem double_rev : "reverse (reverse xs) = xs"
  apply(induction xs)
   apply(auto)
  apply(simp add: snoc_reverse)
  done

end