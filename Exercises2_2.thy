theory Exercises2_2
  imports Main
begin

(*---------------- Exercise 2.6----------------*)
(* tree datatype *)
datatype 'a tree = None | Node "'a tree" 'a "'a tree"

(* collect function *)
fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents None = []" | 
"contents (Node l a r) = (Cons a (contents l))@(contents r)"

(* function to sum tree *)
fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree None = 0" |
"sum_tree (Node l a r) = (sum_tree l) + a + (sum_tree r)"

theorem sum : "sum_tree t = sum_list (contents t)"
  apply(induction t)
   apply(auto)
  done

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

(*---------------- Exercise 2.8----------------*)
(* intersperse function *)
fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a Nil = Nil" | 
"intersperse a [x] = [x]" |
"intersperse a (Cons x xs) = [x,a]@(intersperse a xs)"

value "intersperse 0 [(Suc 1),(Suc 2),(Suc 3),(Suc 4)]"

theorem map_intersperse : "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs rule: intersperse.induct)
  apply(auto)
  done

end
