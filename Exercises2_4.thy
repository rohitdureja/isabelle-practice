theory Exercises2_4
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

(*---------------- Exercise 2.11----------------*)
(* expression datatype*)
datatype exp = Var | Const int | Add exp exp | Mult exp exp

(* eval function *)
(* evaluates an expression at a given value*)
fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var v = v" |
"eval (Const e) v = e" |
"eval (Add e f) v = (eval e v) + (eval f v)" |
"eval (Mult e f) v = (eval e v) * (eval f v)"

(* evalp function *)
(* evaluates a polynomial at a given value*)
fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] v = 0" |
"evalp (Cons x Nil) v = x" |
"evalp (Cons x xs) v = x + v * (evalp xs v)"

(* coeff function *)
(* transforms an expression to a polynomial*)
fun coeff :: "exp \<Rightarrow> int list" where
"coeff Var = [1]" |
"coeff (Const i) = [i]" |
"coeff (Add e f) = (coeff e)@(coeff f)" |
"coeff (Mult e f) = (coeff e)@(coeff f)"

end