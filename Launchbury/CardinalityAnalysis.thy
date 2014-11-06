theory CardinalityAnalysis
imports ArityCorrect "Cardinality-Domain" "SestoftConf" ConstOn
begin

locale CardinalityHeap = CorrectArityAnalysisLet' +
  fixes fHeap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> (var \<Rightarrow> two)"

  assumes fHeap[eqvt]: "\<pi> \<bullet> fHeap = fHeap"
  assumes Aheap_heap3: "x \<in> thunks \<Gamma> \<Longrightarrow> many \<sqsubseteq> (fHeap \<Gamma> e\<cdot>a) x \<Longrightarrow> (Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0"
  assumes edom_fHeap: "edom (fHeap \<Delta> e\<cdot>a) = edom (Aheap \<Delta> e\<cdot>a)"

locale CardinalityPrognosis = 
  fixes prognosis :: "AEnv \<Rightarrow> Arity \<Rightarrow> conf \<Rightarrow> (var \<Rightarrow> two)"

locale CardinalityPrognosisCorrect = CardinalityPrognosis +
  assumes prognosis_env_cong: "ae f|` domA \<Gamma> = ae' f|` domA \<Gamma> \<Longrightarrow> prognosis ae u (\<Gamma>, e, S) = prognosis ae' u (\<Gamma>, e, S)"
  assumes prognosis_ap: "const_on (prognosis ae a (\<Gamma>, e, S)) (ap S) many"

  assumes prognosis_App: "prognosis ae (inc\<cdot>a) (\<Gamma>, e, Arg x # S) \<sqsubseteq> prognosis ae a (\<Gamma>, App e x, S)"
  assumes prognosis_subst_Lam: "prognosis ae (pred\<cdot>a) (\<Gamma>, e[y::=x], S) \<sqsubseteq> prognosis ae a (\<Gamma>, Lam [y]. e, Arg x # S)"
  assumes prognosis_Var: "ae x = up\<cdot>u \<Longrightarrow> a \<sqsubseteq> u \<Longrightarrow> prognosis ae u (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> record_call x \<cdot> (prognosis ae a (\<Gamma>, Var x, S))"
  assumes prognosis_Var2: "ae x \<sqsubseteq> up\<cdot>a \<Longrightarrow> prognosis ae a ((x, e) # \<Gamma>, e, S) \<sqsubseteq> prognosis ae a (\<Gamma>, e, Upd x # S)"

locale CardinalityPrognosisCorrectLet = CardinalityPrognosisCorrect + CardinalityHeap +
  assumes prognosis_Let: "prognosis (Aheap \<Delta> e\<cdot>a \<squnion> ae) a (\<Delta> @ \<Gamma>, e, S) \<sqsubseteq> fHeap \<Delta> e\<cdot>a \<squnion> prognosis ae a (\<Gamma>, Terms.Let \<Delta> e, S)"

locale CardinalityPrognosisEdom = CardinalityPrognosis + CorrectArityAnalysisAheap' +
  assumes artiy_edom_prognosis: "edom (ABinds \<Gamma>\<cdot>ae \<squnion> Aexp e\<cdot>a) \<subseteq> edom (prognosis ae a (\<Gamma>, e, S))"


end
