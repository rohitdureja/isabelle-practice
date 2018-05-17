theory Inductiv
  imports Main
begin

inductive ev :: "nat \<Rightarrow> bool" where
ev0:  "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc (Suc n)) = evn n"

lemma "ev (Suc (Suc (Suc (Suc 0))))"
  apply(rule evSS)
  apply(rule evSS)
  apply(rule ev0)                                         
  done

lemma "ev m \<Longrightarrow> evn m"
  apply(induction rule: ev.induct)
   apply(simp_all)
  done

lemma "evn n \<Longrightarrow> ev n"
  apply(induction n rule: evn.induct)
    apply(simp_all add: ev0 evSS)
  done

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl:   "star r x x" |
step:   "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply(induction rule:star.induct)
   apply(assumption)
  by (simp add: star.step)
  

end