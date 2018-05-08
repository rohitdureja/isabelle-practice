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

(* find max among two int options *)
fun max_opt :: "int option \<Rightarrow> int option \<Rightarrow> int option" where
"max_opt None None = None" |
"max_opt (Some a) None = Some a" |
"max_opt None (Some b) = Some b" |
"max_opt (Some a) (Some b) = Some(max a b)"

(* lemmas about max_opt*)
lemma max_opt_COMMUTATIVE : "max_opt a b = max_opt b a"
  apply(induction a; induction b)
     apply(auto)
  done

lemma max_opt_ASSOCIATIVE : "max_opt (max_opt a b) c = max_opt a (max_opt b c)"
  apply(induction a; induction b; induction c)
         apply(auto)
  done

(* find min among two int options *)
fun min_opt :: "int option \<Rightarrow> int option \<Rightarrow> int option" where
"min_opt None None = None" |
"min_opt (Some a) None = Some a" |
"min_opt None (Some b) = Some b" |
"min_opt (Some a) (Some b) = Some (min a b)"

(* check if int option in lesser than int*)
fun less_opt :: "int option \<Rightarrow> int \<Rightarrow> bool" where
"less_opt None _ = True" |
"less_opt (Some a) b = (a \<le> b)"

(* check if int option is greater than int*)
fun greater_opt :: "int option \<Rightarrow> int \<Rightarrow> bool" where
"greater_opt None _ = True" |
"greater_opt (Some a) b = (a \<ge> b)"

(* find max element in subtree *)
fun max_tree :: "int tree \<Rightarrow> int option" where
"max_tree Tip = None" |
"max_tree (Node l a r) = max_opt (Some a) (max_opt (max_tree l) (max_tree r))"

(* find min element in subtree*)
fun min_tree :: "int tree \<Rightarrow> int option" where
"min_tree Tip = None" |
"min_tree (Node l a r) = min_opt (Some a) (max_opt (min_tree l) (min_tree r))"

(* check if tree is ordered *)
fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True" |
"ord (Node l a r) = ((less_opt (max_tree l) a) \<and> (greater_opt (min_tree r) a) \<and> (ord l) \<and> (ord r))"

(* insert element in binary ordered tree
NOTE: element is always inserted as a leaf*)
fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins e Tip = (Node Tip e Tip)" |
"ins e (Node l a r) = (if (a=e) then (Node l a r) else (if (e < a) then (Node (ins e l) a r) else (Node l a (ins e r))))"

(* theorems for insertion correctness*)
(* theorem 1: correct addition of element *)
theorem insert_correctness : "set (ins x t) = {x} \<union> (set t)"
  apply(induction t)
   apply(auto)
  done

lemma max_insert : "max_tree (ins i t) = max_opt (Some i) (max_tree t)"
  apply(induction t)
  apply(auto)

(* theorem 2: preservation of order*)
theorem order_correctness : "ord t \<Longrightarrow> ord (ins i t)"
  apply(induction t)
   apply(auto)



end