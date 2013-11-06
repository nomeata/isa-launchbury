theory "FMap-Unused"
imports FMap
begin

  
subsection {* Induction over finite maps *}

lemma fmap_induct[case_names empty update, induct type: fmap]:
  assumes "P fempty"
  assumes "\<And> m x v. P m \<Longrightarrow> x \<notin> fdom m \<Longrightarrow> P (m(x f\<mapsto> v))"
  shows "P m"
proof-
  {
  fix m'
  have "finite (fdom m)" by simp
  hence "fdom m' = fdom m \<Longrightarrow> m' \<le> m \<Longrightarrow> P m'"
  proof(induction arbitrary: m' rule: finite_induct)
  case (empty m')
    hence "m' = fempty" by auto
    with assms(1) show ?case by auto
  next
  case (insert x d m')
    from `fdom m' = insert x d` `x \<notin> d`
    have "fdom (fmap_delete x m') = d" by auto
    moreover
    from `m' \<le> m`
    have "fmap_delete x m' \<le> m" by (metis (full_types) calculation fmap_delete_fmap_upd2 fmap_less_restrict fmap_restr_fmap_upd_other fmap_restr_less fmap_trans insert.hyps(2) order_refl)
    ultimately
    have "P (fmap_delete x m')" by (rule insert.IH)
    moreover
    have "x \<notin> fdom (fmap_delete x m')" using `fdom _ = d` `x \<notin> d` by simp
    ultimately
    have "P ((fmap_delete x m')(x f\<mapsto> m' f! x))" by (rule assms(2))
    with `fdom m' = insert x d` 
    show "P m'" by simp
  qed
  }
  thus "P m" by simp
qed
  
subsubsection {* Conversion to associative lists *}

lemma list_of_exists:
  "\<exists> l. fmap_of l = m"
proof(induction rule: fmap_induct)
case empty
  have "fmap_of [] = f\<emptyset>" by simp
  thus ?case..
next
case (update m x v)
  from `\<exists>l. fmap_of l = m`
  obtain l where "fmap_of l = m" ..
  hence "fmap_of ((x,v)#l) = m(x f\<mapsto> v)" by simp
  thus ?case..
qed

definition list_of :: "'a f\<rightharpoonup> 'b \<Rightarrow> ('a \<times> 'b) list" where
  "list_of m = (SOME l. fmap_of l = m)"

lemma fmap_of_list_of[simp]:
  "fmap_of (list_of m) = m"
  unfolding list_of_def
  by (rule someI_ex[OF list_of_exists])

lemma map_of_list_of[simp]:
  "map_of (list_of m) = lookup m"
  unfolding list_of_def
  by (rule someI2_ex[OF list_of_exists]) auto

lift_definition fran :: "'key f\<rightharpoonup> 'value \<Rightarrow> 'value set" is "ran" ..
lemma finite_fran[simp]: "finite (fran m)"
  by (transfer, rule finite_range)
lemma fran_fmap_restr_subset: "fran (fmap_restr S m) \<subseteq> fran m"
  by transfer (auto simp add: ran_def restrict_map_def)
lemma fran_fmap_delete_subset:
  "fran (fmap_delete x m) \<subseteq> fran m"
  by transfer (auto simp add: ran_def) 
lemma fran_fmap_upd[simp]:
  "fran (m(x f\<mapsto> v)) = insert v (fran (fmap_delete x m))"
by (transfer, auto simp add: ran_def)
lemma fran_fmap_add_subset: "fran (m1 f++ m2) \<subseteq> fran m1 \<union> fran m2"
  by (transfer, auto simp add: ran_def)
lemma fran_fmap_copy_subset:
  "fran (fmap_copy m x y) \<subseteq> fran m"
  by transfer (auto simp add: ran_def) 
lemma fmap_map_cong: "(\<And> x. x \<in> fran m \<Longrightarrow> f x = f' x) \<Longrightarrow> m = m' \<Longrightarrow> fmap_map f m = fmap_map f' m'"
  by transfer (fastforce simp add: ran_def Option.map_def split:option.split)


end
