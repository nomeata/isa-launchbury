theory ArityAnalysis
imports Terms AEnv "Arity-Nominal" "Nominal-HOLCF"  "Substitution"
begin

locale ArityAnalysis =
  fixes Aexp :: "exp \<Rightarrow> Arity \<rightarrow> AEnv"
begin

definition Aexp' :: "exp \<Rightarrow> Arity\<^sub>\<bottom> \<rightarrow> AEnv"
  where "Aexp' e = fup \<cdot> (Aexp e)"

lemma Aexp'_simps[simp]:
  "Aexp' e \<cdot> \<bottom> = \<bottom>"
  "Aexp' e \<cdot> (up\<cdot>n) = Aexp e \<cdot> n"
  unfolding Aexp'_def by simp_all

lemma env_restr_join:
  fixes m1 m2 :: "'a::type \<Rightarrow> 'b::{Finite_Join_cpo,pcpo}"
  shows "(m1 \<squnion> m2) f|` S = (m1 f|` S) \<squnion> (m2 f|` S )"
  by (auto simp add: env_restr_def)

lemma join_env_restr_UNIV:
  fixes m :: "'a::type \<Rightarrow> 'b::{Finite_Join_cpo,pcpo}"
  shows "S1 \<union> S2 = UNIV \<Longrightarrow> (m f|` S1) \<squnion> (m f|` S2) = m"
  by (fastforce simp add: env_restr_def)

definition inc_bot :: "Arity\<^sub>\<bottom> \<rightarrow> Arity\<^sub>\<bottom>" ("inc\<^sub>\<bottom>") where "inc_bot = fup\<cdot>(up oo inc)"

lemma inc_bot_simps[simp]:
  "inc\<^sub>\<bottom>\<cdot>\<bottom>=\<bottom>"
  "inc\<^sub>\<bottom>\<cdot>(up\<cdot>n)=up\<cdot>(inc\<cdot>n)"
  unfolding inc_bot_def by simp_all

end

lemma Aexp'_eqvt[eqvt]: "\<pi> \<bullet> (ArityAnalysis.Aexp' Aexp e) = ArityAnalysis.Aexp' (\<pi> \<bullet> Aexp) (\<pi> \<bullet> e)"
  unfolding ArityAnalysis.Aexp'_def
  by perm_simp rule

end
