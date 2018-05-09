theory Automation
  imports Main
begin

lemma "\<forall>x. \<exists>y. x = y"
  by auto

lemma "A \<subseteq> B \<inter> C \<Longrightarrow> A \<subseteq> B \<union> C"
  by auto

lemma "\<lbrakk> \<forall>xs \<in> A. \<exists>ys. xs = ys @ ys; us \<in> A \<rbrakk> \<Longrightarrow> \<exists>n. length us = n + n"
  by fastforce

lemma "\<lbrakk> \<forall>x y. T x y \<or> T y x;
        \<forall>x y. A x y \<and> A y x \<longrightarrow> x = y;
        \<forall>x y. T x y \<longrightarrow> A x y\<rbrakk>
        \<Longrightarrow> \<forall>x y. A x y \<longrightarrow> T x y"
  by blast

lemma "\<lbrakk> xs @ ys = ys @ xs; length xs = length ys \<rbrakk> \<Longrightarrow> xs = ys"
  using append_eq_append_conv by blast

lemma "\<lbrakk> (a::nat) \<le> x + b; 2*x < c\<rbrakk> \<Longrightarrow> 2*a + 1 \<le> 2*b + c"
  by arith

lemma "\<lbrakk> (a::nat) \<le> b; b \<le> c; c \<le> d; d \<le> e\<rbrakk> \<Longrightarrow> a \<le> e"
  by (blast intro: le_trans)

end