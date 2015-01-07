theory CardinalityAnalysis
imports ArityCorrect "Cardinality-Domain" "SestoftConf" ConstOn
begin

locale CardinalityHeap = CorrectArityAnalysisLet' +
  fixes cHeap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> (var \<Rightarrow> two)"

(*   assumes cHeap: "\<pi> \<bullet> cHeap = cHeap" *)
  assumes Aheap_heap3: "x \<in> thunks \<Gamma> \<Longrightarrow> many \<sqsubseteq> (cHeap \<Gamma> e\<cdot>a) x \<Longrightarrow> (Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0"
  assumes edom_cHeap: "edom (cHeap \<Delta> e\<cdot>a) = edom (Aheap \<Delta> e\<cdot>a)"

locale CardinalityPrognosis = 
  fixes prognosis :: "AEnv \<Rightarrow> Arity \<Rightarrow> conf \<Rightarrow> (var \<Rightarrow> two)"

locale CardinalityPrognosisCorrect = CardinalityPrognosis +
  assumes prognosis_env_cong: "ae f|` domA \<Gamma> = ae' f|` domA \<Gamma> \<Longrightarrow> prognosis ae u (\<Gamma>, e, S) = prognosis ae' u (\<Gamma>, e, S)"
  assumes prognosis_reorder: "map_of \<Gamma> = map_of \<Delta>  \<Longrightarrow>  prognosis ae u (\<Gamma>, e, S) = prognosis ae u (\<Delta>, e, S)"
  assumes prognosis_delete: "prognosis ae u (delete x \<Gamma>, e, S) \<sqsubseteq> prognosis ae u (\<Gamma>, e, S)"
  assumes prognosis_ap: "const_on (prognosis ae a (\<Gamma>, e, S)) (ap S) many"
  assumes prognosis_upd: "prognosis ae u (\<Gamma>, e, S) \<sqsubseteq> prognosis ae u (\<Gamma>, e, Upd x # S)"


  assumes prognosis_App: "prognosis ae (inc\<cdot>a) (\<Gamma>, e, Arg x # S) \<sqsubseteq> prognosis ae a (\<Gamma>, App e x, S)"
  assumes prognosis_subst_Lam: "prognosis ae (pred\<cdot>a) (\<Gamma>, e[y::=x], S) \<sqsubseteq> prognosis ae a (\<Gamma>, Lam [y]. e, Arg x # S)"
  assumes prognosis_Var_lam: "map_of \<Gamma> x = Some e \<Longrightarrow> ae x = up\<cdot>u \<Longrightarrow> isLam e \<Longrightarrow> prognosis ae u (\<Gamma>, e, S) \<sqsubseteq> record_call x \<cdot> (prognosis ae a (\<Gamma>, Var x, S))"
  assumes prognosis_Var_thunk: "map_of \<Gamma> x = Some e \<Longrightarrow> ae x = up\<cdot>u \<Longrightarrow> \<not> isLam e \<Longrightarrow> prognosis ae u (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> record_call x \<cdot> (prognosis ae a (\<Gamma>, Var x, S))"
  assumes prognosis_Var2: "isLam e \<Longrightarrow> x \<notin> domA \<Gamma> \<Longrightarrow> prognosis ae 0 ((x, e) # \<Gamma>, e, S) \<sqsubseteq> prognosis ae 0 (\<Gamma>, e, Upd x # S)"

  assumes prognosis_not_called: "ae x = \<bottom> \<Longrightarrow> prognosis ae a (\<Gamma>, e, S) \<sqsubseteq> prognosis ae a (delete x \<Gamma>, e, S)"

  assumes prognosis_called: "once \<sqsubseteq> prognosis ae a (\<Gamma>, Var x, S) x"



locale CardinalityPrognosisCorrectLet = CardinalityPrognosisCorrect + CardinalityHeap +
  assumes prognosis_Let:
  "atom ` domA \<Delta> \<sharp>* \<Gamma> \<Longrightarrow> atom ` domA \<Delta> \<sharp>* S \<Longrightarrow> edom ae \<subseteq> domA \<Gamma> \<union> upds S \<Longrightarrow> prognosis (Aheap \<Delta> e\<cdot>a \<squnion> ae) a (\<Delta> @ \<Gamma>, e, S) \<sqsubseteq> cHeap \<Delta> e\<cdot>a \<squnion> prognosis ae a (\<Gamma>, Terms.Let \<Delta> e, S)"

locale CardinalityPrognosisEdom = CardinalityPrognosis + CorrectArityAnalysisAheap' +
  assumes edom_prognosis:
    "edom (prognosis ae a (\<Gamma>, e, S)) \<subseteq> fv \<Gamma> \<union> fv e \<union> fv S"


end
