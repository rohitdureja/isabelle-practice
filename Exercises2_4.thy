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

(* add coefficients for two lists
Examples: (addition is from the left)
[2,3,4] + [4,5] = [6,7,4]
[5,6] + [3,2,6] = [8,8,6] 
*)
fun add_coeff :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"add_coeff Nil ys = ys" |
"add_coeff xs Nil = xs" |
"add_coeff (x#xs) (y#ys) = (x+y)#(add_coeff xs ys)"


lemma evalp_add : "evalp (add_coeff xs ys) x = evalp xs x + evalp ys x"
  apply(induction xs) 
   apply(auto)

(* multiply all items in a list with a number
Example:
4 * [3,4,2] = [12,16,8]
*)
fun mult :: "int \<Rightarrow> int list \<Rightarrow> int list" where
"mult n Nil = Nil" |
"mult n (x#xs) = (n*x)#(mult n xs)"

(* multiply coefficients for two lists
Example:
[1,2,3]*[4,5] = [4,13,22,15]
[1,1,1]*[1,1] = [1,2,2,1]
*)
fun mult_coeff :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"mult_coeff xs Nil = Nil" |
"mult_coeff Nil ys = Nil" |
"mult_coeff (x#xs) ys = add_coeff (mult x ys) (0#(mult_coeff xs ys))"

(* coeff function *)
(* transforms an expression to a polynomial*)
fun coeff :: "exp \<Rightarrow> int list" where
"coeff Var = [0,1]" |
"coeff (Const i) = [i]" |
"coeff (Add e f) = add_coeff (coeff e) (coeff f)" |
"coeff (Mult e f) = mult_coeff (coeff e) (coeff f)"

theorem preservation : "evalp (coeff e) x = eval e x"
  apply(induction e arbitrary: x)
  apply(auto)

end