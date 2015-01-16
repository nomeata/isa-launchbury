theory FTreeAnalysisSpec
imports FTreeAnalysisSig ArityAnalysisSpec CallFutureCardinality 
begin

hide_const Multiset.single

locale FTreeAnalysisCarrier = FTreeAnalysis + EdomArityAnalysis +
  assumes carrier_Fexp: "carrier (Fexp e\<cdot>a) = edom (Aexp e\<cdot>a)"

locale FTreeAnalysisCorrect = FTreeAnalysisCarrier +
  assumes Fexp_App: "many_calls x \<otimes>\<otimes> (Fexp e)\<cdot>(inc\<cdot>a) \<sqsubseteq> Fexp (App e x)\<cdot>a"
  assumes Fexp_Lam: "without y (Fexp e\<cdot>(pred\<cdot>n)) \<sqsubseteq> Fexp (Lam [y]. e) \<cdot> n"
  assumes Fexp_subst: "Fexp (e[y::=x])\<cdot>a \<sqsubseteq> many_calls x \<otimes>\<otimes> without y ((Fexp e)\<cdot>a)"
  assumes Fexp_Var: "single v \<sqsubseteq> Fexp (Var v)\<cdot>a"
  assumes Fun_repeatable: "isVal e \<Longrightarrow> repeatable (Fexp e\<cdot>0)"
  assumes Fexp_IfThenElse: "Fexp scrut\<cdot>0 \<otimes>\<otimes> (Fexp e1\<cdot>a \<oplus>\<oplus> Fexp e2\<cdot>a) \<sqsubseteq> Fexp (scrut ? e1 : e2)\<cdot>a"

locale FTreeAnalysisCardinalityHeap = 
  FTreeAnalysisCorrect + CorrectArityAnalysisLet + 
  fixes Fheap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> var ftree"
  assumes carrier_Fheap: "carrier (Fheap \<Gamma> e\<cdot>a) = edom (Aheap \<Gamma> e\<cdot>a)"
  assumes Fheap_thunk: "x \<in> thunks \<Gamma> \<Longrightarrow> p \<in> paths (Fheap \<Gamma> e\<cdot>a) \<Longrightarrow> \<not> one_call_in_path x p \<Longrightarrow> (Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0"
  assumes Fheap_substitute: "ftree_restr (domA \<Delta>) (substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Fexp e\<cdot>a)) \<sqsubseteq> Fheap \<Delta> e\<cdot>a"
  assumes Fexp_Let: "ftree_restr (- domA \<Delta>) (substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a))  (thunks \<Delta>) (Fexp e\<cdot>a)) \<sqsubseteq> Fexp (Terms.Let \<Delta> e)\<cdot>a"


end
