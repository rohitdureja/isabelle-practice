theory Automation
  imports Main
begin

lemma "\<forall>x. \<exists>y. x = y"
  by auto

lemma "A \<subseteq> B \<inter> C \<Longrightarrow> A \<subseteq> B \<union> C"
  by auto

end