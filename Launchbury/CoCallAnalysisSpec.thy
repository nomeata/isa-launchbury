theory CoCallAnalysisSpec
imports CoCallAritySig ArityAnalysisSpec
begin

hide_const Multiset.single

locale CoCallArityEdom = CoCallArity + EdomArityAnalysis

locale CoCallArityCorrect = CoCallArity + CoCallAnalyisHeap + CorrectArityAnalysisLet +
  assumes ccExp_App: "ccExp e\<cdot>(inc\<cdot>a) \<squnion> ccProd {x} (insert x (fv e)) \<sqsubseteq> ccExp (App e x)\<cdot>a"
  assumes ccExp_Lam: "cc_restr (fv (Lam [y]. e)) (ccExp e\<cdot>(pred\<cdot>n)) \<sqsubseteq> ccExp (Lam [y]. e)\<cdot>n"
  assumes ccExp_subst: "x \<notin>  S \<Longrightarrow> y \<notin> S \<Longrightarrow> cc_restr S (ccExp e[y::=x]\<cdot>a) \<sqsubseteq> cc_restr S (ccExp e\<cdot>a)"
  assumes ccExp_pap: "isVal e \<Longrightarrow> ccExp e\<cdot>0 = ccSquare (fv e)"
  assumes ccExp_Let: "cc_restr (-domA \<Gamma>) (ccHeap \<Gamma> e\<cdot>a) \<sqsubseteq> ccExp (Let \<Gamma> e)\<cdot>a"

  assumes ccHeap_Exp: "ccExp e\<cdot>a \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
  assumes ccHeap_Heap: "map_of \<Delta> x = Some e' \<Longrightarrow> (Aheap \<Delta> e\<cdot>a) x= up\<cdot>a' \<Longrightarrow> ccExp e'\<cdot>a' \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
  assumes ccHeap_Extra_Edges:
    "map_of \<Delta> x = Some e' \<Longrightarrow> (Aheap \<Delta> e\<cdot>a) x = up\<cdot>a' \<Longrightarrow> ccProd (fv e') (ccNeighbors x (ccHeap \<Delta> e\<cdot>a) - {x} \<inter> thunks \<Delta>) \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"

  assumes aHeap_thunks_rec: " \<not> nonrec \<Gamma> \<Longrightarrow> x \<in> thunks \<Gamma> \<Longrightarrow> x \<in> edom (Aheap \<Gamma> e\<cdot>a) \<Longrightarrow> (Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0"
  assumes aHeap_thunks_nonrec: "nonrec \<Gamma> \<Longrightarrow> x \<in> thunks \<Gamma> \<Longrightarrow> x \<in> ccManyCalls (ccExp e\<cdot>a) \<Longrightarrow> (Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0"


end
