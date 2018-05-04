theory Exercises3_1
  imports Main
begin

(*---------------- Exercise 3.1----------------*)
(* tree datatype *)
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

(* return elements of tree in a set *)
fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}" |
"set (Node l a r) = {a} \<union> (set l) \<union> (set r)"

value "(Suc 3) < (Suc 6)"

fun ord_util :: "int tree \<Rightarrow> int \<Rightarrow> int"

(* check if tree is ordered *)
fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True" |
"ord (Node l a r) = "


end