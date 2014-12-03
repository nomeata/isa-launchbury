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

locale CoCallAnalysis_ccField = CoCallAnalysis +
  assumes "ccField (ccExp e\<cdot>a) \<subseteq> fv e"

locale CoCallAnalyisHeap = 
  fixes ccHeap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> CoCalls"


locale CorrectCoCallAnalysis = CoCallAnalysis_ccField +
  assumes Aexp_eqvt[eqvt]: "\<pi> \<bullet> ccExp = ccExp"
  (* assumes Aexp_Var: "up \<cdot> n \<sqsubseteq> (ccExp (Var x) \<cdot> n) x" *) 
  (* assumes Aexp_subst_App_Lam: "ccExp (e[y::=x]) \<sqsubseteq> ccExp (App (Lam [y]. e) x)" *)
  assumes Aexp_Lam0: "ccExp (Lam [y]. e) \<cdot> 0 = cc_delete y (ccSquare (fv e))"
  assumes Aexp_Lam1: "ccExp (Lam [y]. e) \<cdot> (inc\<cdot>n) = cc_delete y (ccExp e \<cdot>n)"
  assumes Aexp_App: "ccExp (App e x)\<cdot>n = ccExp e \<cdot>(inc\<cdot>n) \<squnion> ccProd (fv e) {x}"
  (* assumes Aexp_subst_restr: "x \<notin> S \<Longrightarrow> y \<notin> S \<Longrightarrow> (ccExp e[x::=y] \<cdot> a) f|` S = (ccExp e\<cdot>a) f|` S" *)

end
