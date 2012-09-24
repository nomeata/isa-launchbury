theory "HOLCF-Set-Nominal"
imports "HOLCF-Set" "Nominal-HOLCF"
begin

lemma subpcpo_eqvt[eqvt, simp]:
  fixes S :: "('a::cont_pt) set"
  assumes "subpcpo S"
  shows "subpcpo (\<pi> \<bullet> S)"
proof-
  interpret subpcpo S by fact
  { fix Y :: "nat \<Rightarrow> 'a"
    assume "chain Y"
    hence "chain (-\<pi> \<bullet> Y)" by (rule chain_eqvt)
    moreover
    assume "\<And> i. Y i \<in> \<pi> \<bullet> S"
    hence "\<And> i. -\<pi> \<bullet> (Y i) \<in> S" by (metis mem_permute_iff permute_minus_cancel(1))
    hence "\<And> i. (-\<pi> \<bullet> Y) i \<in> S" by (metis eqvt_apply permute_pure)
    ultimately
    have "(\<Squnion> i. (-\<pi> \<bullet> Y) i) \<in> S" using pcpo by metis
    hence "- \<pi> \<bullet> (\<Squnion> i. Y i) \<in> S"
      using `chain Y`
      apply (subst Lub_eqvt[OF cpo[OF `chain Y`]])
      apply perm_simp.
    hence "(\<Squnion> i. Y i) \<in> \<pi> \<bullet> S" by (metis mem_permute_iff permute_minus_cancel(1))
  }
  moreover
  have  "\<pi> \<bullet> bottom_of S \<in> \<pi> \<bullet> S" by (metis bottom_of_there mem_permute_iff)
  moreover    
  have "\<forall>y\<in>\<pi> \<bullet> S. \<pi> \<bullet> bottom_of S \<sqsubseteq> y"
  proof
    fix y
    assume "y \<in> \<pi> \<bullet> S" then obtain z where "z\<in> S" and "y = \<pi> \<bullet> z" by (auto simp add: permute_set_def)
    thus "\<pi> \<bullet> bottom_of S \<sqsubseteq> y" by (simp add: mem_permute_iff bottom_of_minimal)
  qed
  ultimately
  show "subpcpo (\<pi> \<bullet> S)"
    unfolding subpcpo_def by auto
qed

lemma bottom_of_eqvt:
  fixes S :: "'a::cont_pt set"
  assumes "subpcpo S"
  shows "\<pi> \<bullet> bottom_of S = bottom_of (\<pi> \<bullet> S)"
proof-
  interpret subpcpo S by fact
  interpret ps!: subpcpo "(\<pi> \<bullet> S)" by (rule subpcpo_eqvt[OF assms])

  have "bottom_of (\<pi> \<bullet> S) \<in> \<pi> \<bullet> S" by (metis ps.bottom_of_there)
  hence a: "- \<pi> \<bullet> bottom_of (\<pi> \<bullet> S) \<in> S" unfolding permute_set_def by auto
  { fix z
    assume "z\<in>S"
    hence "\<pi> \<bullet> z \<in> \<pi> \<bullet> S" by (metis mem_permute_iff)
    hence "bottom_of (\<pi> \<bullet> S) \<sqsubseteq> \<pi> \<bullet> z" by (metis ps.bottom_of_minimal)
    hence "-\<pi> \<bullet> bottom_of (\<pi> \<bullet> S) \<sqsubseteq> z" by (metis (full_types) eqvt_bound perm_cont_simp unpermute_def) 
  } note b = this

  have "bottom_of S = -\<pi> \<bullet> bottom_of (\<pi> \<bullet> S)"
    apply (subst bottom_of_def)
    apply (rule the_equality)
    apply (metis a b)
    apply (metis below_antisym a b)
    done
  thus "\<pi> \<bullet> bottom_of S = bottom_of (\<pi> \<bullet> S)" by (metis permute_minus_cancel(1))
qed


lemma fix_on_eqvt[eqvt]:
  "\<pi> \<bullet> fix_on' (S :: ('a::cont_pt) set) b F = fix_on' (\<pi> \<bullet> S) (\<pi> \<bullet> b) (\<pi> \<bullet> F)"
proof-
  let "?P S b F" = "chain (\<lambda>i. (F ^^ i) (bottom_of S)) \<and> subpcpo S \<and> b = bottom_of S"
  {
    fix \<pi> S b F
    assume a: "?P S b F"
    hence "subpcpo S" by auto
    hence "subpcpo (\<pi> \<bullet> S)" by (metis subpcpo_eqvt)
    moreover
    from a have "chain (\<lambda>i. (F ^^ i) (bottom_of S))" by auto
    hence "chain (\<lambda>i. ((\<pi> \<bullet> F) ^^ i) (bottom_of (\<pi> \<bullet> S)))"
      apply -
      apply (drule chain_eqvt[where \<pi> = \<pi>])
      apply (subst (asm) eqvt_lambda)
      apply (subst (asm) permute_fun_app_eq) back
      apply (subst (asm) bottom_of_eqvt[OF `subpcpo S`])
      apply perm_simp.
    moreover
    from a have "b = bottom_of S" by auto
    hence "\<pi> \<bullet> b = bottom_of (\<pi> \<bullet> S)" by (simp add: bottom_of_eqvt[OF `subpcpo S`])
    ultimately
    have "?P (\<pi> \<bullet> S) (\<pi> \<bullet> b) (\<pi> \<bullet> F)" by auto
  } note i = this

show ?thesis
proof(cases "?P S b F")
  case True
  hence "subpcpo S" by auto

  from True have "?P (\<pi> \<bullet> S) (\<pi> \<bullet> b) (\<pi> \<bullet> F)" by (rule i)
  moreover
  have "\<exists>z. range (\<lambda>i. (F ^^ i) (bottom_of S))  <<| z"
    by (metis Pcpo.cpo_class.cpo True)
  ultimately
  show ?thesis using True
    apply (simp add: fix_on_def if_P Lub_eqvt del:lub_eqvt)
    apply (subst permute_fun_app_eq) back
    apply (subst funpow_eqvt[simplified permute_pure])
    apply (subst bottom_of_eqvt[OF `subpcpo S`])
    ..
next
  case False
  moreover
  hence "\<not> (chain (\<lambda>i. ((\<pi> \<bullet> F) ^^ i) (bottom_of (\<pi> \<bullet> S))) \<and> subpcpo (\<pi> \<bullet> S) \<and> \<pi> \<bullet> b = bottom_of (\<pi> \<bullet> S))"
    apply (rule contrapos_nn)
    apply (drule i[of _ _ _ "-\<pi>"])
    by simp
  ultimately
  show ?thesis
    by (simp add: fix_on_def if_not_P Lub_eqvt del:lub_eqvt)
qed
qed

end

