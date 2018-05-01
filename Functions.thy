theory Functions
  imports Main
begin

datatype 'a tree = Tip |
Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma mirror_mirror : "mirror (mirror t) = t"
  apply(induction t)
   apply(auto)
  done

fun lookup :: "('a * 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup [] x = None" |
"lookup ((a,b)#ps) x = (if x = a then Some b else lookup ps x)"

definition sq :: "nat \<Rightarrow> nat" where
"sq n = n * n"

abbreviation sq' :: "nat \<Rightarrow> nat" where
"sq' n == n * n"


end
