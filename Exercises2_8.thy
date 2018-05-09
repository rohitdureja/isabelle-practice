theory Exercises2_8
  imports Main
begin

(*---------------- Exercise 2.8----------------*)
(* intersperse function *)
fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a Nil = Nil" |
"intersperse a [x] = [x]" |
"intersperse a (Cons x xs) = [x,a]@(intersperse a xs)"

theorem map_intersperse : "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs rule: intersperse.induct)
  apply(auto)
  done

end