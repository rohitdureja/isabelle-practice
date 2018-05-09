theory Exercises2_11
  imports Main
begin

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
"evalp Nil v = 0" |
"evalp (Cons x xs) v = x + v * (evalp xs v)"

(* add coefficients for two lists
Examples: (addition is from the left)
[2,3,4] + [4,5] = [6,7,4]
[5,6] + [3,2,6] = [8,8,6]
*)
fun add_coeff :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"add_coeff Nil Nil = Nil" |
"add_coeff Nil ys = ys" |
"add_coeff xs Nil = xs" |
"add_coeff (x#xs) (y#ys) = (x+y)#(add_coeff xs ys)"

lemma evalp_add[simp] : "evalp (add_coeff xs ys) x = (evalp xs x) + (evalp ys x)"
  apply(induction xs rule: add_coeff.induct)
     apply(auto simp add: algebra_simps)
  done

(* multiply all items in a list with a number
Example:
4 * [3,4,2] = [12,16,8]
*)
fun mult :: "int \<Rightarrow> int list \<Rightarrow> int list" where
"mult n Nil = Nil" |
"mult n (x#xs) = (n*x)#(mult n xs)"

lemma evalp_mul[simp] : "evalp (mult n xs) v = n * (evalp xs v)"
  apply(induction xs)
   apply(auto simp add:algebra_simps)
  done

(* multiply coefficients for two lists
Example:
[1,2,3]*[4,5] = [4,13,22,15]
[1,1,1]*[1,1] = [1,2,2,1]
*)
fun mult_coeff :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"mult_coeff Nil ys = Nil" |
"mult_coeff (x#xs) ys = add_coeff (mult x ys) (0#(mult_coeff xs ys))"

lemma evalp_mult[simp] : "evalp (mult_coeff xs ys) x = (evalp xs x) * (evalp ys x)"
  apply(induction xs)
   apply(auto simp add: algebra_simps)
  done

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
  done

end