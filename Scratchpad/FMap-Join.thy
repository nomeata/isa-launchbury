theory "FMap-Join"
imports "FMap-HOLCF" "HOLCF-Join"
begin

default_sort type

subsubsection {* Binary joins of finite maps *}

lemma fdom_join[simp]:
  "compatible m1 m2 \<Longrightarrow> fdom (m1 \<squnion> m2) = fdom m1"
  by (metis join_above1 fmap_below_dom)

lemma fdom_compatible:
  "compatible m1 m2 \<Longrightarrow> fdom m1 = fdom m2"
by (metis join_above1 join_above2 fmap_below_dom)

lemma the_lookup_compatible_and_join: 
  assumes "compatible m1 m2"
  assumes [simp]: "x \<in> fdom m1"
  shows "compatible (m1 f! x) (m2 f! x) \<and> (m1 f! x) \<squnion> (m2 f! x) = (m1 \<squnion> m2) f! x"
proof (rule is_join_and_compatible)
  show "m1 f! x \<sqsubseteq> (m1 \<squnion> m2) f! x"
    by (rule fmap_belowE[OF join_above1[OF `compatible m1 m2`]])
  show "m2 f! x \<sqsubseteq> (m1 \<squnion> m2) f! x"
    by (rule fmap_belowE[OF join_above2[OF `compatible m1 m2`]])
  fix a
  assume "m1 f! x \<sqsubseteq> a"
  assume "m2 f! x \<sqsubseteq> a"

  note fdom_compatible[OF `compatible m1 m2`, symmetric, simp]
  note fdom_join[OF `compatible m1 m2`, simp]

  have "m1 \<sqsubseteq> (m1 \<squnion> m2)(x f\<mapsto> a)"
    apply (rule fmap_upd_belowI2)
    apply auto[1]
    apply (rule fmap_belowE[OF join_above1[OF `compatible m1 m2`]])
    apply (rule `m1 f! x \<sqsubseteq> a`)
    done
  moreover
  have "m2 \<sqsubseteq> (m1 \<squnion> m2)(x f\<mapsto> a)"
    apply (rule fmap_upd_belowI2)
    apply auto[1]
    apply (rule fmap_belowE[OF join_above2[OF `compatible m1 m2`]])
    apply (rule `m2 f! x \<sqsubseteq> a`)
    done
  ultimately
  have "(m1 \<squnion> m2) \<sqsubseteq> (m1 \<squnion> m2)(x f\<mapsto> a)"
    by (rule join_below[OF `compatible m1 m2`])
  thus " m1 \<squnion> m2 f! x \<sqsubseteq> a"
    by (metis (full_types) fmap_belowE the.simps lookup_fmap_upd)
qed

lemma the_lookup_join[simp]: 
  assumes "compatible m1 m2"
  shows "(m1 \<squnion> m2) f! x = (m1 f! x) \<squnion> (m2 f! x)"
  apply (cases "x \<in> fdom m1")
  apply (metis assms the_lookup_compatible_and_join)
  apply (metis assms fdomIff fdom_compatible fdom_join join_self)
  done

lemma fmap_lookup_bot_join[simp]: 
  assumes "compatible m1 m2"
  shows "(m1 \<squnion> m2) f!\<^sub>\<bottom> x = (m1 f!\<^sub>\<bottom> x) \<squnion> (m2 f!\<^sub>\<bottom> x)"
  apply (cases "x \<in> fdom m1")
  apply (metis assms fdom_compatible fdom_join fmap_lookup_bot_simps(1) the_lookup_join)
  apply (metis assms fdom_compatible fdom_join fmap_lookup_bot_simps(3) join_bottom(2))
  done


lemma the_lookup_compatible:
  assumes "compatible m1 m2"
  shows "compatible (m1 f! x) (m2 f! x)" 
  apply (cases "x \<in> fdom m1")
  apply (metis assms the_lookup_compatible_and_join)
  apply (metis assms compatible_refl fdomIff fdom_compatible)
  done

lift_definition fmap_join :: "'a f\<rightharpoonup> 'b::cpo \<Rightarrow> 'a f\<rightharpoonup> 'b  \<Rightarrow> 'a f\<rightharpoonup> 'b"
is "\<lambda>m1 m2 x. (if x \<in> fdom m1 then Some ((m1 f! x) \<squnion> (m2 f! x)) else None)"
  by (auto simp add: dom_def)

lemma fdom_fmap_join'[simp]: "fdom (fmap_join m1 m2) = fdom m1"
  apply (subst fdom.rep_eq)
  apply (subst fmap_join.rep_eq)
  apply (auto, metis not_Some_eq)
  done

lemma the_lookup_fmap_join'[simp]: "x \<in> fdom m1 \<Longrightarrow> (fmap_join m1 m2) f! x = (m1 f! x) \<squnion> (m2 f! x)"
  apply (subst lookup.rep_eq)
  apply (subst fmap_join.rep_eq)
  apply simp
  done

lemma compatible_fmapI:
  assumes "\<And> x. \<lbrakk> x \<in> fdom m1 ; x \<in> fdom m2 \<rbrakk> \<Longrightarrow> compatible (m1 f! x) (m2 f! x)"
  assumes "fdom m1 = fdom m2"
  shows "compatible m1 m2"
proof (rule compatibleI)
  show "m1 \<sqsubseteq> fmap_join m1 m2"
    apply (rule fmap_belowI)
    apply simp
    apply simp
    by (metis "HOLCF-Join.join_above1" assms(1) assms(2))
  show "m2 \<sqsubseteq> fmap_join m1 m2"
    apply (rule fmap_belowI)
    apply (simp add: assms(2))
    apply (simp add: assms(2))
    by (metis "HOLCF-Join.join_above2" assms(1) assms(2))
  fix a
  assume "m1 \<sqsubseteq> a"
  assume "m2 \<sqsubseteq> a"
  show "fmap_join m1 m2 \<sqsubseteq> a"
    apply (rule fmap_belowI)
    apply (metis fdom_fmap_join' fmap_below_dom[OF `m1 \<sqsubseteq> a`])
    apply (metis fmap_belowE[OF `m1 \<sqsubseteq> a`] fmap_belowE[OF `m2 \<sqsubseteq> a`] assms(1) assms(2) fdom_fmap_join' join_below the_lookup_fmap_join')
    done
qed

lemma fmap_restr_join:
  assumes [simp]: "finite S"
  assumes [simp]:"compatible m1 m2"
  shows "fmap_restr S (m1 \<squnion> m2) = fmap_restr S m1 \<squnion> fmap_restr S m2"
proof-
  have [simp]: "compatible (fmap_restr S m1) (fmap_restr S m2)"
    by (auto intro!: compatible_fmapI simp add: the_lookup_compatible fdom_compatible[OF assms(2)])
  show ?thesis
    by (rule fmap_eqI, auto)
qed

lemma fmap_upd_join:
  assumes "S = insert x (fdom \<rho>1)"
  and "x \<notin> fdom \<rho>1"
  and "x \<notin> fdom \<rho>2"
  and compat1: "compatible (\<rho>1(x f\<mapsto> y)) (\<rho>2\<^bsub>[S]\<^esub>)"
  shows "(\<rho>1(x f\<mapsto> y)) \<squnion> (\<rho>2\<^bsub>[S]\<^esub>) = (\<rho>1 \<squnion> (\<rho>2\<^bsub>[S - {x}]\<^esub>))(x f\<mapsto> y)" (is "?L = ?R")
proof(rule fmap_eqI)
  have "finite S" using assms(1) by auto

  have *: "\<And> xa . xa \<in> S \<Longrightarrow> xa \<noteq> x \<Longrightarrow> \<rho>2\<^bsub>[S - {x}]\<^esub> f! xa = \<rho>2\<^bsub>[S]\<^esub> f! xa"
    using `finite S` by (case_tac "xa \<in> fdom \<rho>2", auto)

  have compat2: "compatible \<rho>1 (\<rho>2\<^bsub>[S - {x}]\<^esub>)"
    apply (rule compatible_fmapI)
    using compat1
    apply -
    apply (drule_tac x = xa in the_lookup_compatible)
    apply (subst *)
    using assms(1) apply simp
    apply (metis assms(2))

    apply (subst (asm) lookup_fmap_upd_other)
    apply (metis `x \<notin> fdom \<rho>1`)
    apply assumption
    using assms(2) assms(1)
    by auto

  show "fdom ?L = fdom ?R"
    using compat1 compat2 by auto
  fix y
  assume "y \<in> fdom ?L"
  hence "y \<in> S" by (metis assms(1) compat1 fdom_join fmap_upd_fdom)
  show "?L f! y = ?R f! y"
  proof(cases "y = x")
    case True
    thus ?thesis
      apply (subst the_lookup_join[OF compat1])
      apply (subst lookup_fmap_expand2[OF `finite S` `y\<in> S`])
      using `x \<notin> fdom \<rho>2` compat2  `y\<in> S`
      by auto
  next
    case False
    thus ?thesis
      apply simp
      apply (subst the_lookup_join[OF compat1], auto)
      apply (subst the_lookup_join[OF compat2])
      apply (case_tac "y \<in> fdom \<rho>2")
      using `finite S`  `y \<in> S`
      by auto
  qed
qed

lemma fmap_expand_join_disjunct:
  assumes "fdom m1 \<inter> fdom m2 = {}"
  shows "m1\<^bsub>[fdom m1 \<union> fdom m2]\<^esub> \<squnion> m2\<^bsub>[fdom m1 \<union> fdom m2]\<^esub> = m1 f++ m2"
proof-
  from assms(1) have disj: "\<And> x. x \<in> fdom m1 \<Longrightarrow> x \<notin> fdom m2" "\<And> x. x \<in> fdom m2 \<Longrightarrow> x \<notin> fdom m1" by auto
  have [simp]:"compatible (m1\<^bsub>[fdom m1 \<union> fdom m2]\<^esub>) (m2\<^bsub>[fdom m1 \<union> fdom m2]\<^esub>)"
    by (fastforce intro: compatible_fmapI simp add: disj)
  show ?thesis by (fastforce simp add: disj)
qed

subsubsection {* Finite maps have greatest lowest bounds *}

instance fmap :: (type, Nonempty_Meet_cpo) Bounded_Nonempty_Meet_cpo
apply default
proof-
  fix S :: "('a f\<rightharpoonup> 'b) set"
  assume "S \<noteq> {}" and "\<exists>z. S >| z"
  then obtain b where "\<And> m. m\<in>S \<Longrightarrow> b \<sqsubseteq> m" by (metis is_lbD)
  hence [simp]:"\<And> m. m \<in> S \<Longrightarrow> fdom m = fdom b" by (metis fmap_below_dom)
  
  obtain f where f: "\<And> x. x \<in> fdom b \<Longrightarrow> (\<lambda>m . m f! x) ` S >>| f x "
  proof-
    {
    fix x
    assume "x \<in> fdom b"
    have "(\<lambda>m . m f! x) ` S \<noteq> {}" using `S \<noteq> {}` by auto
    then obtain l where  "(\<lambda>m . m f! x) ` S >>| l" by (metis nonempty_meet_exists)
    hence "(\<lambda>m . m f! x) ` S >>| (SOME l. (\<lambda>m . m f! x) ` S >>| l)"
      by (rule someI)
    }
    thus ?thesis by (rule that)
  qed 

  let ?zm = "\<lambda> x. if x \<in> fdom b then Some (f x) else None"
  have "dom ?zm = fdom b" by (auto simp add: dom_def)

  obtain z where [simp]: "fdom z = fdom b" and z: "\<And> x m . x \<in> fdom b \<Longrightarrow> (\<lambda>m . m f! x) ` S >>| (z f! x)"
  proof-
    show ?thesis  
      apply (rule that[of "Abs_fmap ?zm"])
      apply (subst fdom.rep_eq)
      apply (subst  Abs_fmap_inverse)
      prefer 3
      apply (subst (2) lookup.rep_eq)
      apply (subst  Abs_fmap_inverse)
      apply (auto simp add: dom_def)
      apply (erule f)
      done
  qed

  have "S >>| z"
    apply (rule is_glbI)
    apply (rule is_lbI)
    apply (rule fmap_belowI)
    apply simp
    apply (rule is_lbD)
    apply (rule is_glbD1)
    apply (rule z, simp)
    apply auto
    apply (rule fmap_belowI)
    apply (metis `S \<noteq> {}` `\<And>m. m \<in> S \<Longrightarrow> fdom m = fdom b` `fdom z = fdom b` all_not_in_conv fmap_below_dom is_lbD)
    apply (rule is_glbD2)
    apply (rule z, simp)
    apply (rule is_lbI)
    apply (erule imageE)
    apply (erule ssubst)
    apply (rule fmap_belowE)
    apply (erule (1) is_lbD)
    done
  thus "\<exists> z. S >>| z" by auto
qed


lemma fmap_empty_join[simp]: "fdom f = S \<Longrightarrow> f\<emptyset>\<^bsub>[S]\<^esub> \<squnion> f = f"
  by (metis fmap_bottom_below larger_is_join2)

lemma bottom_of_fdom[simp]: "finite S \<Longrightarrow> bottom_of {y. fdom y = S} = f\<emptyset>\<^bsub>[S]\<^esub>"
  using bottom_of_cone_above[where x = "f\<emptyset>\<^bsub>[S]\<^esub>"]
  by simp
end

