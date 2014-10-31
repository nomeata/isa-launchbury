theory Set_Cpo
imports HOLCF
begin

instantiation set :: (type) below
begin
  definition below_set where "op \<sqsubseteq> = op \<subseteq>"
instance..  
end

instance set :: (type) po
  by default (auto simp add: below_set_def)

lemma is_lub_fun:
  "S <<| \<Union>S"
  by(auto simp add: is_lub_def below_set_def is_ub_def)
  
instance set  :: (type) cpo
  by default (rule exI, rule is_lub_fun)

lemma minimal_set: "{} \<sqsubseteq> S"
  unfolding below_set_def by simp

instance set  :: (type) pcpo
  by default (rule+, rule minimal_set)

lemma set_contI:
  assumes  "\<And> S. f (\<Union>S) = \<Union> (f ` S)"
  shows "cont f"
proof(rule contI)
  case (goal1 Y)
  have "f (\<Squnion> i. Y i) = \<Union> (range (\<lambda>i. f (Y i)))" 
    using assms by (metis Set_Cpo.is_lub_fun image_image lub_eqI)
  with is_lub_fun
  show "range (\<lambda>i. f (Y i)) <<| f (\<Squnion> i. Y i)" by metis
qed

end
