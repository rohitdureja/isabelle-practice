theory Exercises2_06
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

end

