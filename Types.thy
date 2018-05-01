theory Types
  imports Main
begin
declare [[names_short]]

(* Conjuct two booleans *)
fun conj :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"conj True True = True" |
"conj _ _ = False"
(* test cases *)
value "conj True False"
value "conj True True"
value "conj False False"
value "conj False True"

(* Add two natural numbers  *)
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"
(* test cases *)
value "add 2 3"
value "add 0 3"
value "add 2 0"
value "add 0 0"


lemma add_02: "add m 0 = m"
  apply(induction m)
  apply(auto)
  done

datatype 'a list = Nil | Cons 'a "'a list"

(* append list at the back of a list *)
fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys" | 
"app (Cons x xs) ys = Cons x (app xs ys)"

(* append list at the front of a list*)
fun appr :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"appr xs Nil = xs" |
"appr xs (Cons y ys) = Cons y (app xs ys)"

(* reverse a list *)
fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"

(* lemma for Nil appended to a list *)
lemma app_nil[simp] : "app xs Nil = xs"
  apply(induction xs)
   apply(auto)
  done

(* lemma for associativity of append *)
lemma app_ass[simp] : "app (app xs ys) zs = app xs (app ys zs)"
  apply(induction xs)
   apply(auto)
  done

(* lemma for theorem rev2 *)
lemma app_rev[simp] : "rev (app xs ys) = app (rev ys) (rev xs)"
  apply(induction xs)
  apply(auto)
  done

(* theorem double reverse is the list itself*)
theorem rev2[simp]: "rev (rev xs) = xs"
  apply(induction xs)
  apply(auto)
  done
end


