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
