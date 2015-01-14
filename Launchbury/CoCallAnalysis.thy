theory CoCallAnalysis
imports Terms "Arity-Nominal" "CoCallGraph-Nominal" Substitution
begin

locale CoCallAnalysis =
  fixes ccExp :: "exp \<Rightarrow> Arity \<rightarrow> CoCalls"
begin

definition ccExp' :: "exp \<Rightarrow> Arity\<^sub>\<bottom> \<rightarrow> CoCalls"
  where "ccExp' e = fup \<cdot> (ccExp e)"

lemma ccExp'_simps[simp]:
  "ccExp' e \<cdot> \<bottom> = \<bottom>"
  "ccExp' e \<cdot> (up\<cdot>n) = ccExp e \<cdot> n"
  unfolding ccExp'_def by simp_all

end

lemma ccExp'_eqvt[eqvt]:
  "\<pi> \<bullet> (CoCallAnalysis.ccExp' ccexp e) = CoCallAnalysis.ccExp' (\<pi> \<bullet> ccexp) (\<pi> \<bullet> e)"
  unfolding CoCallAnalysis.ccExp'_def
  by perm_simp rule

lemma ccExp'_cong: 
  "cccexp1 e = cccexp2 e \<Longrightarrow> CoCallAnalysis.ccExp' cccexp1 e = CoCallAnalysis.ccExp' cccexp2 e"
  unfolding CoCallAnalysis.ccExp'_def by simp

locale CoCallAnalyisHeap = 
  fixes ccHeap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> CoCalls"

end
