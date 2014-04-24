theory "Denotational-Related"
imports "Denotational" "ResourcedDenotational" ValueSimilarity
begin

theorem denotational_semantics_similar: 
  assumes "\<rho> f\<triangleleft>\<triangleright> \<sigma>"
  shows "\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>C\<^sup>\<infinity>"
using assms
proof(induct e arbitrary: \<rho> \<sigma> rule:exp_induct)
  case (Var v)
  hence "\<rho> v \<triangleleft>\<triangleright> (\<sigma> v)\<cdot>C\<^sup>\<infinity>" by cases auto
  thus ?case by simp
next
  case (Lam v e)
  { fix x y
    assume "x \<triangleleft>\<triangleright> y\<cdot>C\<^sup>\<infinity>"
    with `\<rho> f\<triangleleft>\<triangleright> \<sigma>`
    have "\<rho>(v := x) f\<triangleleft>\<triangleright> \<sigma>(v := y)"
      by (auto 1 4)
    hence "\<lbrakk>e\<rbrakk>\<^bsub>\<rho>(v := x)\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<sigma>(v := y)\<^esub>)\<cdot>C\<^sup>\<infinity>"
      by (rule Lam.hyps)
  }
  thus ?case by auto
next
  case (App e v \<rho> \<sigma>)
  hence App': "\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>C\<^sup>\<infinity>" by auto
  thus ?case
  proof (cases rule: slimilar_bot_cases)
    case bot thus ?thesis by auto
  next
    case (Fn f g)
    from `\<rho> f\<triangleleft>\<triangleright> \<sigma>`
    have "\<rho> v \<triangleleft>\<triangleright> (\<sigma> v)\<cdot>C\<^sup>\<infinity>"  by auto
    thus ?thesis using Fn App' by auto
  qed
next
  case (Let as e \<rho> \<sigma>)
  have "\<lbrace>asToHeap as\<rbrace>\<rho> f\<triangleleft>\<triangleright> \<N>\<lbrace>asToHeap as\<rbrace>\<sigma>"
  proof (rule parallel_HSem_ind_different_ESem[OF fmap_similar_adm fmap_similar_fmap_bottom])
    case (goal1 \<rho>' \<sigma>')
    show ?case
    proof(rule pointwiseI)
      case (goal1 x)
      show ?case using `\<rho> f\<triangleleft>\<triangleright> \<sigma>`
        by (auto simp add: lookup_fun_merge_eq lookupHeapToEnv elim: Let(1)[OF _  `\<rho>' f\<triangleleft>\<triangleright> \<sigma>'`] )
    qed
  qed
  with Let(2)
  have "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>asToHeap as\<rbrace>\<sigma>\<^esub>)\<cdot>C\<^sup>\<infinity>" by blast
  thus ?case by simp
qed

theorem heaps_similar: "\<lbrace>\<Gamma>\<rbrace> f\<triangleleft>\<triangleright> \<N>\<lbrace>\<Gamma>\<rbrace>"
  by (rule parallel_HSem_ind_different_ESem[OF fmap_similar_adm])
     (auto simp add: lookup_fmap_restr_eq lookupHeapToEnv denotational_semantics_similar simp del: app_strict)

end
