theory "Denotational-Related"
imports "Denotational" "Resourced-Denotational-Props" ValueSimilarity
begin

theorem
  assumes "\<rho> f\<triangleleft>\<triangleright> \<sigma>"
  shows denotational_semantics_similar: "\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>(C\<^sup>\<infinity>)"
  and "\<And> x. x \<in> heapVars (asToHeap as) \<Longrightarrow>  \<lbrakk>the (map_of (asToHeap as) x)\<rbrakk>\<^bsub>\<rho>\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk>the (map_of (asToHeap as) x)\<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>C\<^sup>\<infinity>"
using assms
proof(nominal_induct e and as avoiding: \<rho> \<sigma> rule:exp_assn.strong_induct)
  case (Var v)
  show ?case
  proof (cases "v \<in> fdom \<rho>")
    case False
    with Var have "v \<notin> fdom \<sigma>" by cases auto
    thus ?thesis using False by simp
  next
    case True
    with Var have "\<rho> f!\<^sub>\<bottom> v \<triangleleft>\<triangleright> (\<sigma> f!\<^sub>\<bottom> v)\<cdot>C\<^sup>\<infinity>" by cases auto
    thus ?thesis by simp
  qed
next
  case (Lam v e)
  { fix x y
    assume "x \<triangleleft>\<triangleright> y\<cdot>C\<^sup>\<infinity>"
    with `\<rho> f\<triangleleft>\<triangleright> \<sigma>`
    have "\<rho>(v f\<mapsto> x) f\<triangleleft>\<triangleright> \<sigma>(v f\<mapsto> y)"
      by (fastforce simp add: lookup_fmap_upd_eq)
    hence "\<lbrakk>e\<rbrakk>\<^bsub>\<rho>(v f\<mapsto> x)\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<sigma>(v f\<mapsto> y)\<^esub>)\<cdot>C\<^sup>\<infinity>"
      by (rule Lam.hyps)
  }
  with Lam(1,2)
  show ?case by auto
next
  case (App e v \<rho> \<sigma>)
  hence App': "\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>C\<^sup>\<infinity>" by auto
  thus ?case
  proof (cases rule: slimilar_bot_cases)
    case bot thus ?thesis by auto
  next
    case (Fn f g)
    from `\<rho> f\<triangleleft>\<triangleright> \<sigma>`
    have "\<rho> f!\<^sub>\<bottom> v \<triangleleft>\<triangleright> (\<sigma> f!\<^sub>\<bottom> v)\<cdot>C\<^sup>\<infinity>"  by auto
    thus ?thesis using Fn App' by auto
  qed
next
  case (Let as e \<rho> \<sigma>)
  have "fdom \<rho> = fdom \<sigma>" using Let(5) by auto
  have disj1: "fdom \<rho> \<inter> heapVars (asToHeap as) = {}"
    by (metis Let.hyps(1) disjoint_iff_not_equal sharp_star_Env)
  have disj2: "fdom \<sigma> \<inter> heapVars (asToHeap as) = {}"
    by (metis Let.hyps(2) disjoint_iff_not_equal sharp_star_Env)

  have "\<lbrace>asToHeap as\<rbrace>\<rho> f\<triangleleft>\<triangleright> \<N>\<lbrace>asToHeap as\<rbrace>\<sigma>"
  proof (rule parallel_HSem_ind_different_ESem_disjoint
                [OF "Denotational.ESem_cont"
                    "Resourced-Denotational-Props.ESem_cont"
                    disj1 disj2 fmap_similar_adm
                  ])
    case goal1 show ?case by (simp add: `fdom \<rho> = fdom \<sigma>`)
  next
    case (goal2 \<rho>' \<sigma>')
    show ?case
    proof(rule fmap_lift_relI)
      case goal1 show ?case by (simp add:  `fdom \<rho> = fdom \<sigma>`)
    next
      case (goal2 x)
      hence "x \<in> fdom \<rho> \<and> x \<notin> heapVars (asToHeap as) \<or> x \<in> heapVars (asToHeap as)" by auto
      thus ?case using `\<rho>' f\<triangleleft>\<triangleright> \<sigma>'` `\<rho> f\<triangleleft>\<triangleright> \<sigma>`
        by (auto simp add: lookupHeapToEnv elim: Let(3) )
    qed
  qed
  with Let(4)
  have "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>asToHeap as\<rbrace>\<sigma>\<^esub>)\<cdot>C\<^sup>\<infinity>" by blast
  thus ?case using Let(1,2) by simp
qed auto

theorem heaps_similar: "\<lbrace>\<Gamma>\<rbrace> f\<triangleleft>\<triangleright> \<N>\<lbrace>\<Gamma>\<rbrace>"
  by (rule parallel_HSem_ind_different_ESem_disjoint
                [OF "Denotational.ESem_cont"
                    "Resourced-Denotational-Props.ESem_cont"
                     _ _ fmap_similar_adm
                  ])
     (auto simp add: lookupHeapToEnv denotational_semantics_similar)

end
