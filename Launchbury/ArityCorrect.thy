theory ArityCorrect
imports ArityAnalysis (* "Vars-Nominal-HOLCF" *)
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

locale CorrectArityAnalysisCong = CorrectArityAnalysisAheap +
  assumes Aexp_App_cong: "Aexp e\<cdot>(inc\<cdot>a) = Aexp e'\<cdot>(inc\<cdot>a) \<Longrightarrow> Aexp (App e x)\<cdot>a = Aexp (App e' x)\<cdot>a"
  assumes Aexp_Lam_cong: "Aexp e\<cdot>(pred\<cdot>n) = Aexp e'\<cdot>(pred\<cdot>n) \<Longrightarrow> Aexp (Lam [y]. e) \<cdot> n = Aexp (Lam [y]. e') \<cdot> n"
  assumes Aexp_Let_cong:
    "domA \<Gamma> = domA \<Gamma>' \<Longrightarrow>
     thunks \<Gamma> = thunks \<Gamma>' \<Longrightarrow>
     (\<And> x a. x \<in> domA \<Gamma> \<Longrightarrow> up\<cdot>a \<sqsubseteq> (Aheap \<Gamma>'\<cdot>(Aexp e\<cdot>a)) x \<Longrightarrow> Aexp (the (map_of \<Gamma> x))\<cdot>a = Aexp (the (map_of \<Gamma>' x))\<cdot>a) \<Longrightarrow>
     Aexp e\<cdot>a = Aexp e'\<cdot>a \<Longrightarrow>
     Aexp (Let \<Gamma> e)\<cdot>a = Aexp (Let \<Gamma>' e')\<cdot>a"
  assumes Aheap_cong2: "domA \<Gamma> = domA \<Gamma>' \<Longrightarrow>
    (\<And> x a. x \<in> domA \<Gamma> \<Longrightarrow> up\<cdot>a \<sqsubseteq> (Aheap \<Gamma>'\<cdot>ae) x \<Longrightarrow> Aexp (the (map_of \<Gamma> x))\<cdot>a = Aexp (the (map_of \<Gamma>' x))\<cdot>a) \<Longrightarrow>
    Aheap \<Gamma>\<cdot>ae = Aheap \<Gamma>'\<cdot>ae"


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
