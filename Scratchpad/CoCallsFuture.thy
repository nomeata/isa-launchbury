theory CoCallsFuture
imports CoCallGraph CallFutures
begin

inductive_set any_future :: "var set \<Rightarrow> future set" for S
  where "domF f \<subseteq> S \<Longrightarrow> f \<in> any_future S"

definition conformsToCC :: "future \<Rightarrow> CoCalls \<Rightarrow> bool"
  where "conformsToCC f G \<longleftrightarrow> (\<forall>x y. (x--y\<notin>G) \<longrightarrow> possible x f \<longrightarrow>  \<not> possible y (after x f))"

definition ccFilterFuture  :: "future set \<Rightarrow> CoCalls \<Rightarrow> future set"
  where "ccFilterFuture S G = {f \<in> S . conformsToCC f G}"

lemma no_future_conforms[simp]:  "conformsToCC no_future G"
  unfolding conformsToCC_def by simp

end  
