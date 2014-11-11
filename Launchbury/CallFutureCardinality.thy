theory CallFutureCardinality
imports Vars "Cardinality-Domain"
begin

definition pathCard :: "var list  \<Rightarrow> (var \<Rightarrow> two)"
  where "pathCard f x = (if x \<notin> set f then none else (if length (filter (\<lambda> y. x = y) f) = 1 then once else many))"

definition pathsCard :: "var list set \<Rightarrow> (var \<Rightarrow> two)"
  where "pathsCard fs x = lub ((\<lambda> f. pathCard f x)` fs )"

lemma paths_Card_above:
  "f \<in> fs \<Longrightarrow> pathCard f \<sqsubseteq> pathsCard fs"
  sorry

end
