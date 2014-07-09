theory AEnv
imports Arity Vars "Env"
begin

type_synonym AEnv = "var \<Rightarrow> Arity\<^sub>\<bottom>"

definition AE_singleton :: "var \<Rightarrow> Arity\<^sub>\<bottom> \<rightarrow> AEnv"
  where "AE_singleton x = (\<Lambda> a. (\<lambda> y . (if x = y then a else \<bottom>)))"

lemma AE_singleton_bot[simp]: "AE_singleton x \<cdot> \<bottom> = \<bottom>"
  by (rule ext)(simp add: AE_singleton_def)

lemma AE_singleton_simps[simp]:
  "(AE_singleton x \<cdot> n) x = n"
  "x' \<noteq> x \<Longrightarrow> (AE_singleton x \<cdot> n) x' = \<bottom>"
  by (simp_all add: AE_singleton_def)

lemma up_zero_top[simp]: "x \<sqsubseteq> up\<cdot>(0::Arity)"
  by (cases x) auto

lemma AE_singleton_below_iff[simp]: "AE_singleton x \<cdot> a \<sqsubseteq> ae  \<longleftrightarrow> a \<sqsubseteq> ae x"
  by (auto simp add: fun_below_iff AE_singleton_def)

lemma edom_AE_singleton_up[simp]: "edom (AE_singleton x \<cdot> (up \<cdot> n)) = {x}"
  unfolding edom_def AE_singleton_def by auto

end
