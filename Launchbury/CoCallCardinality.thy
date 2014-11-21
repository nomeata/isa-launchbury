theory CoCallCardinality
imports FTreeCardinality CoCallAnalysis
begin

definition aeFtree :: "AEnv \<Rightarrow> var ftree"
  where "aeFtree ae = many_among (edom ae)"

lemma cont_aeFtree[THEN cont_compose, cont2cont, simp]:
  "cont aeFtree"
  sorry


lemma  valid_lists_downset_aux:
  "xs \<in> valid_lists CoCalls \<Longrightarrow> butlast xs \<in> valid_lists CoCalls"
  by (induction xs) (auto dest: in_set_butlastD)


lift_definition ccFTree :: "CoCalls \<Rightarrow> var ftree" is "\<lambda> G. valid_lists G" 
  by (auto intro: valid_lists_downset_aux)

lemma cont_ccFTree[THEN cont_compose, cont2cont, simp]:
  "cont ccFTree"
  sorry

locale CoCallCardinality = CoCallAnalysis + CoCallAnalyisHeap + CorrectArityAnalysisLet'
begin

definition Fexp :: "exp \<Rightarrow> Arity \<rightarrow> var ftree"
  where "Fexp e = (\<Lambda> a. ccFTree (ccExp e\<cdot>a) \<inter>\<inter> aeFtree (Aexp e\<cdot>a))"

lemma Fexp_simp: "Fexp e\<cdot>a = ccFTree (ccExp e\<cdot>a) \<inter>\<inter> aeFtree (Aexp e\<cdot>a)"
  unfolding Fexp_def by (rule beta_cfun) (intro cont2cont)

definition Fheap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> var ftree"
  where "Fheap \<Gamma> e = (\<Lambda> a. ccFTree (ccHeap \<Gamma> e\<cdot>a) \<inter>\<inter> aeFtree (Aheap \<Gamma> e\<cdot>a))"

lemma Fheap_simp: "Fheap \<Gamma> e\<cdot>a = ccFTree (ccHeap \<Gamma> e\<cdot>a) \<inter>\<inter> aeFtree (Aheap \<Gamma> e\<cdot>a)"
  unfolding Fheap_def by (rule beta_cfun) (intro cont2cont)

sublocale FutureAnalysis Fexp.

sublocale FutureAnalysisCarrier Fexp
  apply default
  sorry

sublocale FutureAnalysisCorrect Fexp
  apply default
  sorry


sublocale FutureAnalysisCardinalityHeap Fexp Aexp Aheap Fheap
  apply default
  sorry

end

