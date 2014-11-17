theory "Set-Cpo"
imports HOLCF
begin

instantiation set :: (type) below
begin
  definition below_set where "op \<sqsubseteq> = op \<subseteq>"
instance..  
end

instance set :: (type) po
  by default (auto simp add: below_set_def)

lemma is_lub_set:
  "S <<| \<Union>S"
  by(auto simp add: is_lub_def below_set_def is_ub_def)

lemma lub_set: "lub S = \<Union>S"
  by (metis is_lub_set lub_eqI)
  
instance set  :: (type) cpo
  by default (rule exI, rule is_lub_set)

lemma minimal_set: "{} \<sqsubseteq> S"
  unfolding below_set_def by simp

instance set  :: (type) pcpo
  by default (rule+, rule minimal_set)

lemma set_contI:
  assumes  "\<And> Y. chain Y \<Longrightarrow> f (\<Squnion> i. Y i) = \<Union> (f ` range Y)"
  shows "cont f"
proof(rule contI)
  case (goal1 Y)
  hence "f (\<Squnion> i. Y i) = \<Union> (f ` range Y)" by (rule assms)
  also have "\<dots> = \<Union> (range (\<lambda>i. f (Y i)))" by simp
  finally
  show "range (\<lambda>i. f (Y i)) <<| f (\<Squnion> i. Y i)" using is_lub_set by metis
qed

lemma set_set_contI:
  assumes  "\<And> S. f (\<Union>S) = \<Union> (f ` S)"
  shows "cont f"
  by (metis set_contI assms is_lub_set  lub_eqI)

end
