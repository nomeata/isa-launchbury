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

lemma lub_is_either: "lub S = Either S"
  using is_lub_ftree by (rule lub_eqI)

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

lemma substitute_mono1': "f \<sqsubseteq> f'\<Longrightarrow> substitute f T t \<sqsubseteq> substitute f' T t"
  using  substitute_mono1[folded below_set_def, unfolded paths_mono_iff] fun_belowD
  by metis

lemma substitute_mono2': "t \<sqsubseteq> t'\<Longrightarrow> substitute f T t \<sqsubseteq> substitute f T t'"
  using  substitute_mono2[folded below_set_def, unfolded paths_mono_iff].

lemma and_then_both_single': "and_then x t \<sqsubseteq> both (single x) t"
  using and_then_both_single[folded below_set_def, unfolded paths_mono_iff].

lemma ftree_contI:
  assumes  "\<And> S. f (Either S) = Either (f ` S)"
  shows "cont f"
proof(rule contI)
  fix Y :: "nat \<Rightarrow> 'a ftree"  
  have "range (\<lambda>i. f (Y i)) = f ` range Y" by auto
  also have "Either \<dots> = f (Either (range Y))" unfolding assms(1)..
  also have "Either (range Y) = lub (range Y)" unfolding lub_is_either by simp
  finally 
  show "range (\<lambda>i. f (Y i)) <<| f (\<Squnion> i. Y i)" by (metis is_lub_ftree)
qed

lemma ftree_contI2:
  assumes  "\<And> x. paths (f x) = \<Union>(t ` paths x)"
  assumes "[] \<in> t []"
  shows "cont f"
proof(rule contI)
  fix Y :: "nat \<Rightarrow> 'a ftree"  
  have "paths (Either (range (\<lambda>i. f (Y i)))) = insert [] (\<Union>x. paths (f (Y x)))"
    by (simp add: paths_Either)
  also have "\<dots> = insert [] (\<Union>x. \<Union>(t ` paths (Y x)))"
    by (simp add: assms(1))
  also have "\<dots> = \<Union>(t ` insert [] (\<Union>x. paths (Y x)))"
    apply auto
    apply (rule exI[where x = 0])
    apply (rule bexI[where x = "[]"])
    apply (rule assms(2))
    apply simp
    done
  also have "\<dots> = \<Union>(t ` paths (Either (range Y)))"
    by (auto simp add: paths_Either)
  also have "\<dots> = paths (f (Either (range Y)))"
    by (simp add: assms(1))
  also have "\<dots> = paths (f (lub (range Y)))" unfolding lub_is_either by simp
  finally
  show "range (\<lambda>i. f (Y i)) <<| f (\<Squnion> i. Y i)" by (metis is_lub_ftree paths_inj)
qed

lemma cont_paths[THEN cont_compose, cont2cont, simp]:
  "cont paths"
  apply (rule set_contI)
  apply (thin_tac ?X)
  unfolding lub_is_either
  apply transfer
  apply auto
  done

lemma cont_substitute[THEN cont_compose, cont2cont, simp]:
  "cont (substitute f T)"
  apply (rule ftree_contI2)
  apply (rule paths_substitute_substitute'')
  apply (auto intro: substitute''.intros)
  done

lemma cont_both1:
  "cont (\<lambda> x. both x y)"
  apply (rule ftree_contI2[where t = "\<lambda>xs . {zs . \<exists>ys\<in>paths y. zs \<in> xs \<otimes> ys}"])
  apply (rule set_eqI)
  by (auto intro:  simp add: paths_both)

lemma cont_both2:
  "cont (\<lambda> x. both y x)"
  apply (rule ftree_contI2[where t = "\<lambda>ys . {zs . \<exists>xs\<in>paths y. zs \<in> xs \<otimes> ys}"])
  apply (rule set_eqI)
  by (auto intro:  simp add: paths_both)

lemma cont_both[cont2cont,simp]: "cont f \<Longrightarrow> cont g \<Longrightarrow> cont (\<lambda> x. f x \<otimes>\<otimes> g x)"
  by (rule cont_compose2[OF cont_both1 cont_both2])

lemma cont_intersect1:
  "cont (\<lambda> x. intersect x y)"
  by (rule ftree_contI2[where t = "\<lambda>xs . (if xs \<in> paths y then {xs} else {})"]) auto

lemma cont_intersect2:
  "cont (\<lambda> x. intersect y x)"
  by (rule ftree_contI2[where t = "\<lambda>xs . (if xs \<in> paths y then {xs} else {})"]) auto

lemma cont_intersect[cont2cont,simp]: "cont f \<Longrightarrow> cont g \<Longrightarrow> cont (\<lambda> x. f x \<inter>\<inter> g x)"
  by (rule cont_compose2[OF cont_intersect1 cont_intersect2])

lemma cont_without[THEN cont_compose, cont2cont,simp]: "cont (without x)"
  sorry

lemma paths_many_calls_subset:
  "t \<sqsubseteq> many_calls x \<otimes>\<otimes> without x t"
  by (metis (full_types) below_set_def paths_many_calls_subset paths_mono_iff)

lemma single_below:
  "[x] \<in> paths t \<Longrightarrow> single x \<sqsubseteq> t" by transfer auto

end
