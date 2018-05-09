theory Exercises2_02
  imports Main
begin

(*---------------- Exercise 2.2----------------*)
(* add function *)
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add m 0 = m" |
"add m (Suc n) = Suc(add m n)"

(* prove associativity of add *)
theorem add_associative : "add x (add y z) = add (add x y) z"
  apply(induction z)
   apply(auto)
  done

(* prove commutativity of add *)
(* lemma 1*)
lemma add2zero : "add 0 x = x"
  apply(induction x)
   apply(auto)
  done

(* lemma 2 *)
lemma suc_add : "Suc (add y x) = add (Suc y) x"
  apply(induction x)
   apply(auto)
  done

theorem add_commutative : "add x y = add y x"
  apply(induction y)
   apply(auto)
  apply(simp add: add2zero)
  apply(simp add: suc_add)
  done

(* double function *)
fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc m) = 2 + (double m)"

theorem double_add : "double m = add m m"
  apply(induction m)
  apply(auto)
  apply(simp add: add_commutative)
  done

end