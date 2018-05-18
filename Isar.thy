theory Isar
  imports Main
begin
  
lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall>A. \<exists>a. A = f a" by (simp add: surj_def)
  from 1 have 2: "\<exists>a. {x. x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

lemma
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof-
  have "\<exists>a. {x. x \<notin> f x}  = f a" using s by (metis Cantors_paradox Pow_UNIV)
  thus "False" by blast
qed





end