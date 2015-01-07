theory ArityCorrect
imports ArityAnalysisAbinds (* "Vars-Nominal-HOLCF" *)
begin

locale EdomArityAnalysis = ArityAnalysis + 
  assumes Aexp_edom: "edom (Aexp e\<cdot>a) \<subseteq> fv e"
begin

  lemma Aexp'_edom: "edom (Aexp' e\<cdot>a) \<subseteq> fv e"
    by (cases a) (auto dest:set_mp[OF Aexp_edom])
  
  lemma Aexp_fresh_bot[simp]: assumes "atom v \<sharp> e" shows "(Aexp e\<cdot>a) v = \<bottom>"
  proof-
    from assms have "v \<notin> fv e" by (metis fv_not_fresh)
    with Aexp_edom have "v \<notin> edom (Aexp e\<cdot>a)" by auto
    thus ?thesis unfolding edom_def by simp
  qed

end

locale SubstArityAnalysis = EdomArityAnalysis + 
  assumes Aexp_subst: "Aexp (e[y::=x])\<cdot>a \<sqsubseteq> env_delete y ((Aexp e)\<cdot>a) \<squnion> esing x\<cdot>(up\<cdot>0)"
  assumes Aexp_subst_restr: "x \<notin> S \<Longrightarrow> y \<notin> S \<Longrightarrow> (Aexp e[x::=y] \<cdot> a) f|` S = (Aexp e\<cdot>a) f|` S"

locale CorrectArityAnalysis' = SubstArityAnalysis +
(*  assumes Aexp_eqvt: "\<pi> \<bullet> Aexp = Aexp" *)
  assumes Aexp_Var: "up \<cdot> n \<sqsubseteq> (Aexp (Var x)\<cdot>n) x"
  assumes Aexp_App: "Aexp e \<cdot>(inc\<cdot>n) \<squnion> esing x \<cdot> (up\<cdot>0) \<sqsubseteq>  Aexp (App e x) \<cdot> n"
  assumes Aexp_Lam: "env_delete y (Aexp e \<cdot>(pred\<cdot>n)) \<sqsubseteq> Aexp (Lam [y]. e) \<cdot> n"

locale CorrectArityAnalysisAheap' = CorrectArityAnalysis' + 
  fixes Aheap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> AEnv"
  assumes Aheap_eqvt[eqvt]: "\<pi> \<bullet> Aheap = Aheap"
  assumes edom_Aheap: "edom (Aheap \<Gamma> e\<cdot> a) \<subseteq> domA \<Gamma>"
  assumes Aheap_subst: "x \<notin> domA \<Gamma> \<Longrightarrow> y \<notin> domA \<Gamma> \<Longrightarrow> Aheap \<Gamma>[x::h=y] e[x ::=y]  = Aheap \<Gamma> e"

locale CorrectArityAnalysisLet' = CorrectArityAnalysisAheap' +
  assumes Aexp_Let: "ABinds \<Gamma>\<cdot>(Aheap \<Gamma> e\<cdot>a) \<squnion> Aexp e\<cdot>a \<sqsubseteq> Aheap \<Gamma> e\<cdot>a \<squnion> Aexp (Let \<Gamma> e)\<cdot>a"

locale CorrectArityAnalysisLetNoCard = CorrectArityAnalysisLet' +
  assumes Aheap_heap3: "x \<in> thunks \<Gamma> \<Longrightarrow> (Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0"

context EdomArityAnalysis
begin
lemma Aexp'_lookup_fresh: "atom v \<sharp> e \<Longrightarrow> (Aexp' e\<cdot>a) v = \<bottom>"
  by (cases a) auto

lemma edom_AnalBinds: "edom (ABinds \<Gamma>\<cdot>ae) \<subseteq> fv \<Gamma>"
  by (induction \<Gamma> rule: ABinds.induct)
     (auto simp del: fun_meet_simp dest: set_mp[OF Aexp'_edom] dest: set_mp[OF fv_delete_subset])
end 

context CorrectArityAnalysis'
begin

lemma Aexp_Var_singleton: "esing x \<cdot> (up\<cdot>n) \<sqsubseteq> Aexp (Var x) \<cdot> n"
  by (simp add: Aexp_Var)

lemma Aexp'_Var: "esing x \<cdot> n \<sqsubseteq> Aexp' (Var x) \<cdot> n"
  by (cases n) (simp_all add: Aexp_Var)

end



end
