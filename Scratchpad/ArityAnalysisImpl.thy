theory ArityAnalysisImpl
imports ArityAnalysisFix ArityAnalysisPreImpl
begin

definition Real_Aexp where "Real_Aexp = ArityAnalysisPreImpl.Aexp ArityAnalysis.Afix"

lemma heap_exp_are_smaller:  "e \<in> snd ` set \<Gamma> \<Longrightarrow> size e \<le> size_list (\<lambda>p. size (snd p)) \<Gamma>"
  by (metis (mono_tags) imageE order_refl size_list_estimation')

interpretation ArityAnalysisPreImpl ArityAnalysis.Afix where "Aexp = ArityAnalysisImpl.Real_Aexp"
  unfolding Real_Aexp_def atomize_conj
  apply (rule conjI[OF _ refl])
  apply default
  apply (perm_simp, rule)
  apply (rule ArityAnalysisFix.Afix_cong)
  apply (metis heap_exp_are_smaller)
  apply assumption
  done

interpretation ArityAnalysis Aexp.

lemma Aexp_edom': "edom (Aexp e\<cdot>a) \<subseteq> fv e"
  by (nominal_induct arbitrary: a rule: exp_strong_induct) fastforce+

end
