theory ArityCorrect
imports ArityAnalysis Launchbury (* "Vars-Nominal-HOLCF" *)
begin

locale EdomArityAnalysis = ArityAnalysis + 
  assumes Aexp_edom: "edom (Aexp e\<cdot>a) \<subseteq> fv e"
begin

lemma Aexp'_edom: "edom (Aexp' e\<cdot>a) \<subseteq> fv e"
  by (cases a) (auto dest:set_mp[OF Aexp_edom])

end

locale CorrectArityAnalysis = EdomArityAnalysis +
  assumes Aexp_eqvt[eqvt]: "\<pi> \<bullet> Aexp = Aexp"
  assumes Aexp_Var: "up \<cdot> n \<sqsubseteq> (Aexp (Var x) \<cdot> n) x"
  assumes Aexp_subst_App_Lam: "Aexp (e[y::=x]) \<sqsubseteq> Aexp (App (Lam [y]. e) x)"
  assumes Aexp_Lam: "Aexp (Lam [y]. e) \<cdot> n = env_delete y (Aexp e \<cdot>(pred\<cdot>n))"
  assumes Aexp_App: "Aexp (App e x) \<cdot> n = Aexp e \<cdot>(inc\<cdot>n) \<squnion> AE_singleton x \<cdot> (up\<cdot>0)"
  assumes Aexp_subst_restr: "x \<notin> S \<Longrightarrow> y \<notin> S \<Longrightarrow> (Aexp e[x::=y] \<cdot> a) f|` S = (Aexp e\<cdot>a) f|` S"

locale CorrectArityAnalysisAheap = CorrectArityAnalysis + 
  fixes Aheap :: "heap \<Rightarrow> AEnv \<rightarrow> AEnv"
  assumes Aheap_eqvt[eqvt]: "\<pi> \<bullet> Aheap = Aheap"
  assumes edom_Aheap: "edom (Aheap \<Gamma> \<cdot> ae) \<subseteq> domA \<Gamma>"
  assumes Aheap_heap: "map_of \<Gamma> x = Some e' \<Longrightarrow> Aexp' e'\<cdot>((Aheap \<Gamma>\<cdot>ae) x) f|` domA \<Gamma> \<sqsubseteq> Aheap \<Gamma>\<cdot>ae"
  assumes Aheap_heap3: "map_of \<Gamma> x = Some e' \<Longrightarrow> \<not> isLam e' \<Longrightarrow> (Aheap \<Gamma>\<cdot>ae) x = up\<cdot>0"
  assumes Aheap_above_arg: "ae f|` domA \<Gamma> \<sqsubseteq> Aheap \<Gamma>\<cdot>ae"
  assumes Aheap_subst: "x \<notin> domA \<Gamma> \<Longrightarrow> y \<notin> domA \<Gamma> \<Longrightarrow> Aheap \<Gamma>[x::h=y] = Aheap \<Gamma>"
  assumes Aheap_cong: "ae f|` domA \<Gamma> = ae' f|` domA \<Gamma> \<Longrightarrow> Aheap \<Gamma>\<cdot>ae = Aheap \<Gamma>\<cdot>ae'"

locale CorrectArityAnalysisLet = CorrectArityAnalysisAheap +
  assumes Aheap_heap2: "map_of \<Gamma> x = Some e' \<Longrightarrow> Aexp' e'\<cdot>((Aheap \<Gamma>\<cdot>(Aexp e\<cdot>a)) x) f|` (- domA \<Gamma>) \<sqsubseteq>  Aexp (Let \<Gamma> e)\<cdot>a"
  assumes Aexp_Let_above: "Aexp e\<cdot>a f|` (- domA \<Gamma>) \<sqsubseteq> Aexp (Let \<Gamma> e)\<cdot>a"


context CorrectArityAnalysis
begin

lemma Aexp_Var_singleton: "AE_singleton x \<cdot> (up\<cdot>n) \<sqsubseteq> Aexp (Var x) \<cdot> n"
  by (simp add: Aexp_Var)

lemma Aexp'_Var: "AE_singleton x \<cdot> n \<sqsubseteq> Aexp' (Var x) \<cdot> n"
  by (cases n) (simp_all add: Aexp_Var)


lemma Aexp_lookup_fresh: "atom v \<sharp> e \<Longrightarrow> (Aexp e\<cdot>a) v = \<bottom>"
  using set_mp[OF Aexp_edom] unfolding edom_def by (auto simp add: fv_def fresh_def)

lemma Aexp'_lookup_fresh: "atom v \<sharp> e \<Longrightarrow> (Aexp' e\<cdot>a) v = \<bottom>"
  by (cases a) (auto simp add: Aexp_lookup_fresh)

end

end
