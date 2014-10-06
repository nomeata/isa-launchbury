theory CoCallAnalysis
imports Terms "Arity-Nominal" CoCallGraph
begin

locale CoCallAnalysis =
  fixes ccExp :: "exp \<Rightarrow> Arity \<rightarrow> CoCalls"
  assumes "ccField (ccExp e\<cdot>a) \<subseteq> fv e"


end
