theory "HSem-Equivalences"
imports HSem HSemUpd
begin
lemma disjoint_join_is_update:
  assumes "fdom \<rho>1 = d1"
  assumes "fdom \<rho>2 = d2"
  assumes "d1 \<inter> d2 = {}"
  shows "\<rho>1\<^bsub>[d1 \<union> d2]\<^esub> \<squnion> \<rho>2\<^bsub>[d1 \<union> d2]\<^esub> = \<rho>1 f++ \<rho>2"
proof-
  have disjoint: "fdom \<rho>1 \<inter> fdom \<rho>2 = {}" using assms by auto

  have compat[simp]: "compatible (\<rho>1\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub>) (\<rho>2\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub>)"
  proof (rule compatible_fmapI)
    show "fdom (\<rho>1\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub>) = fdom (\<rho>2\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub>)"
      by simp
    fix x
    assume "x \<in> fdom (\<rho>1\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub>)"
    hence "(x \<in> fdom \<rho>1 \<and> x \<notin> fdom \<rho>2) \<or> (x \<in> fdom \<rho>2 \<and> x \<notin> fdom \<rho>1)" using disjoint by auto
    thus "compatible (\<rho>1\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub> f! x) (\<rho>2\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub> f! x)"
      by auto
  qed
  
  have "\<rho>1 f++ \<rho>2 = \<rho>1\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub> \<squnion> \<rho>2\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub>"
  proof
    show "fdom (\<rho>1 f++ \<rho>2) = fdom (\<rho>1\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub> \<squnion> \<rho>2\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub>)"
      by simp
  next
    fix x
    assume "x \<in> fdom (\<rho>1 f++ \<rho>2)"
    hence "(x \<in> fdom \<rho>1 \<and> x \<notin> fdom \<rho>2) \<or> (x \<in> fdom \<rho>2 \<and> x \<notin> fdom \<rho>1)" using disjoint by auto
    thus "\<rho>1 f++ \<rho>2 f! x = \<rho>1\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub> \<squnion> \<rho>2\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub> f! x"
      by auto
  qed
  thus ?thesis using assms by simp
qed
   
theorem heap_update_join:
  assumes disjoint: "fdom \<rho> \<inter> heapVars \<Gamma> = {}"
  assumes cont1: "\<And> e. cont (ESem1 e)"
  assumes cont2: "\<And> e. cont (ESem2 e)"
  assumes exp_eq: "\<And> e \<rho>. e \<in> snd ` set \<Gamma> \<Longrightarrow> ESem1 e \<rho> = ESem2 e \<rho>"
  shows "HSemUpd.has_ESem.UHSem ESem1 \<Gamma> \<rho> = HSem.has_ESem.HSem ESem2 \<Gamma> \<rho>"
proof-
  interpret Upd: has_cont_ESem ESem1 by default fact
  interpret HSem:has_cont_ESem ESem2 by default fact

  have cond: "fix_join_cond (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars \<Gamma>]\<^esub>) 
                        (\<lambda> \<rho>' . heapToEnv \<Gamma> (\<lambda>e. ESem2 e \<rho>')\<^bsub>[fdom \<rho> \<union> heapVars \<Gamma>]\<^esub>)"
    by (rule HSem.disjoint_is_HSem_cond[OF disjoint])

  have heapToEnv_eq: "\<And> \<rho>. heapToEnv \<Gamma> (\<lambda>e. ESem1 e \<rho>) = heapToEnv \<Gamma> (\<lambda>e. ESem2 e \<rho>)"
    by (rule heapToEnv_cong[OF refl exp_eq])

  show ?thesis
    unfolding Upd.UHSem_def' HSem.HSem_def'[OF cond]
    apply (simp add: bottom_of_fjc to_bot_fmap_def)
    apply (rule fix_on_cong[OF Upd.fix_on_cond_UHSem])
    apply (simp add: heapToEnv_eq)
    apply (rule disjoint_join_is_update[OF refl _ disjoint, symmetric])
    apply simp
    done
qed


context has_cont_ESem
begin
  lemma replace_upd: "UHSem \<Gamma> \<rho> = HSem \<Gamma> (\<rho> f|` (- heapVars \<Gamma>))"
  proof-
    have "UHSem \<Gamma> \<rho> = UHSem \<Gamma> (\<rho> f|` (- heapVars \<Gamma>))"
      by (metis UHSem_Nil UHSem_restr Un_iff all_not_in_conv diff_eq fdom_UHSem fdom_fmap_restr fmap_restr_UHSem_noop fmap_restr_fmap_restr inf_bot_right)
    also have "\<dots> = HSem \<Gamma> (\<rho> f|` (- heapVars \<Gamma>))"
      by (rule heap_update_join[OF _ ESem_cont ESem_cont refl]) auto
    finally
    show ?thesis.
  qed

  lemmas iterative_HSem'_cond_join = iterative_UHSem'_cond[unfolded replace_upd]
  thm trans[OF iterative_UHSem iterative_UHSem', unfolded replace_upd]
  thm iterative_UHSem [unfolded replace_upd]
  lemmas iterative_HSem_join       = iterative_UHSem [unfolded replace_upd]
  lemmas iterative_HSem'_join      = iterative_UHSem'[unfolded replace_upd]
end

end
