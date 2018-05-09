theory Exercises2_10
  imports Main
begin

(*---------------- Exercise 2.10----------------*)
(* binary tree datatype *)
datatype tree0 = Leaf | Node "tree0" "tree0"

(* function to count nodes *)
fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Leaf = (Suc 0)" |
"nodes (Node a b) = 1 + nodes a + nodes b"

(* explode function *)
fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

(* finding equation, for c = nodes t
n = 0, c
n = 1, 2*c + 1
n = 2, 4*c + 2 + 1
arbitrary n, 2^n*c + 2^{n-1} + 2^{n-2} + ... 2^{0}
            \<Rightarrow> 2^n*c + 2^n - 1 (sum of progression)
 *)
theorem explode_count : "nodes(explode n t) = 2^n*(nodes t + 1) - 1"
  apply(induction n arbitrary: t)
  apply(auto)
  apply(simp add: algebra_simps)
  done

end
