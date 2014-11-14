theory "FTree-HOLCF"
imports FTree "HOLCF-Utils" "Set-Cpo"
begin

instantiation ftree :: (type) below
begin
  lift_definition below_ftree :: "'a ftree \<Rightarrow> 'a ftree \<Rightarrow> bool" is "op \<subseteq>".
instance..
end

lemma paths_mono: "t \<sqsubseteq> t' \<Longrightarrow> paths t \<sqsubseteq> paths t'"
  by transfer (auto simp add: below_set_def)

lemma paths_mono_iff: "paths t \<sqsubseteq> paths t' \<longleftrightarrow> t \<sqsubseteq> t'"
  by transfer (auto simp add: below_set_def)

lemma paths_belowI: "(\<And> x xs. x#xs \<in> paths t \<Longrightarrow> x#xs \<in> paths t') \<Longrightarrow> t \<sqsubseteq> t'"
  apply transfer
  apply auto
  apply (case_tac x)
  apply auto
  done

instance ftree :: (type) po
 by default (transfer, simp)+

lemma is_lub_ftree:
  "S <<| Either S"
  unfolding is_lub_def is_ub_def
  by transfer auto

instance ftree :: (type) cpo
  by default (rule exI, rule is_lub_ftree)

lemma minimal_ftree: "empty \<sqsubseteq> S"
  by transfer simp

instance ftree :: (type) pcpo
  by default (rule+, rule minimal_ftree)

lemma empty_is_bottom: "empty = \<bottom>"
  by (metis below_bottom_iff minimal_ftree)

lemma both_above_arg1: "t \<sqsubseteq> both t t'"
  by transfer fastforce

lemma both_above_arg2: "t' \<sqsubseteq> both t t'"
  by transfer fastforce

lemma both_mono1':
  "t \<sqsubseteq> t' \<Longrightarrow> both t t'' \<sqsubseteq> both t' t''"
  using  both_mono1[folded below_set_def, unfolded paths_mono_iff].

lemma both_mono2':
  "t \<sqsubseteq> t' \<Longrightarrow> both t'' t \<sqsubseteq> both t'' t'"
  using  both_mono2[folded below_set_def, unfolded paths_mono_iff].

lemma substitute_mono1': "f \<sqsubseteq> f'\<Longrightarrow> substitute f t \<sqsubseteq> substitute f' t"
  using  substitute_mono1[folded below_set_def, unfolded paths_mono_iff] fun_belowD
  by metis

lemma substitute_mono2': "t \<sqsubseteq> t'\<Longrightarrow> substitute f t \<sqsubseteq> substitute f t'"
  using  substitute_mono2[folded below_set_def, unfolded paths_mono_iff].

lemma and_then_both_single': "and_then x t \<sqsubseteq> both (single x) t"
  using and_then_both_single[folded below_set_def, unfolded paths_mono_iff].

end
