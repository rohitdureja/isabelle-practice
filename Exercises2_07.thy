theory Exercises2_07
  imports Main
begin

(*---------------- Exercise 2.7----------------*)
datatype 'a tree2 = Leaf 'a | Node "'a tree2" 'a "'a tree2"

(* mirror function *)
fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror (Leaf a) = Leaf a" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

(* pre-order function *)
fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Leaf a) = [a]" |
"pre_order (Node l a r) = [a]@(pre_order l)@(pre_order r)"

(* post-order function *)
fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Leaf a) = [a]" |
"post_order (Node l a r) = (post_order l)@(post_order r)@[a]"

theorem pre_post : "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
  apply(auto)
  done

end