theory HSemUpd
  imports "HeapToEnv" "DistinctVars-Nominal" "HOLCF-Set" "HOLCF-Down-Closed"
begin


lemma sharp_star_Env': "atom ` heapVars \<Gamma> \<sharp>* (\<rho> :: 'var::{cont_pt,at_base} f\<rightharpoonup> 'value::{pure_cpo,Nonempty_Meet_cpo,pcpo}) \<longleftrightarrow> heapVars \<Gamma> \<inter> fdom \<rho> = {}"
  by(induct \<Gamma>, auto simp add: fresh_star_def sharp_Env)

locale has_ESem =
  fixes ESem :: "'exp::pt \<Rightarrow> 'var::{cont_pt,at_base} f\<rightharpoonup> 'value \<Rightarrow> 'value::{pure_cpo,Nonempty_Meet_cpo,pcpo}" ("\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60)
begin

definition HSem :: "('var \<times> 'exp) list \<Rightarrow> 'var f\<rightharpoonup> 'value \<Rightarrow> 'var f\<rightharpoonup> 'value" ("\<lbrace>_\<rbrace>_"  [60,60] 60)
  where
  "\<lbrace>h\<rbrace>\<rho> = 
    (if (\<forall> e \<in> snd `set h. cont (ESem e))
     then  fix_on' (fmap_bottom (fdom \<rho> \<union> heapVars h)) (\<lambda> \<rho>'. \<rho> f++ heapToEnv h (\<lambda> e. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>))
     else (fmap_bottom (fdom \<rho> \<union> heapVars h)))"

lemma HSem_def'':
  assumes "\<And> e. e \<in> snd ` set h \<Longrightarrow> cont (ESem e)"
  shows "\<lbrace>h\<rbrace>\<rho> = fix_on' (fmap_bottom (fdom \<rho> \<union> heapVars h)) (\<lambda> \<rho>'. \<rho> f++ heapToEnv h (\<lambda> e. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>))"
  unfolding HSem_def using assms by metis

lemma fix_on_cond_HSem':
  assumes cont: "\<And> e. e \<in> snd ` set h \<Longrightarrow> cont (ESem e)"
  shows "fix_on_cond {x. fmap_bottom (fdom \<rho> \<union> heapVars h) \<sqsubseteq> x}
          (fmap_bottom (fdom \<rho> \<union> heapVars h)) (\<lambda>\<rho>'. \<rho> f++ heapToEnv h (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>))"
  apply (rule fix_on_condI)
  apply (rule subpcpo_cone_above)
  apply (rule bottom_of_cone_above)
  apply (rule closed_onI, simp)
  apply (rule cont_onI)
  apply (rule contE[OF fmap_add_cont2cont[OF cont_const cont2cont_heapToEnv[OF assms]] chain_on_is_chain])
    apply assumption+
  done

lemma HSem_monofun'':
  assumes cont: "\<And> e. e \<in> snd ` set h \<Longrightarrow> cont (ESem e)"
  assumes "\<rho> \<sqsubseteq> \<rho>'"
  shows "\<lbrace>h\<rbrace>\<rho> \<sqsubseteq> \<lbrace>h\<rbrace>\<rho>'"
  apply (subst (1 2) HSem_def'')
  apply (erule cont)
  apply (rule fix_on_mono2[OF fix_on_cond_HSem'[OF cont] fix_on_cond_HSem'[OF cont]])
    apply assumption+
  apply (metis assms(2) below.r_refl fmap_below_dom)
  apply (rule fmap_add_mono[OF `\<rho> \<sqsubseteq> \<rho>'`])
  by (rule cont2monofunE[OF cont2cont_heapToEnv[OF cont]])

lemma HSem_cont'':
  assumes cont: "\<And> e. e \<in> snd ` set h \<Longrightarrow> cont (ESem e)"
  assumes "chain Y"
  shows "\<lbrace>h\<rbrace>(\<Squnion> i. Y  i) = (\<Squnion> i. \<lbrace>h\<rbrace>(Y i))"
proof-
  have fdoms:"\<And> i. fdom (Y i) = fdom (\<Squnion> i. Y i)" (is "\<And> _ .(_ = ?d)") by (metis chain_fdom `chain Y`) 
  show ?thesis
    apply (subst (1 2) HSem_def'')
    apply (erule cont)+
    unfolding fdoms
    proof (rule fix_on_cont[OF `chain Y`, where S = "{x . fmap_bottom (fdom (\<Squnion> i. Y i) \<union> heapVars h) \<sqsubseteq> x}"])
      show "cont (\<lambda>a b. a f++ heapToEnv h (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>b\<^esub>))"
        by (rule cont2cont_lambda[OF fmap_add_cont1])
      fix i
        from fix_on_cond_HSem'[OF cont, where \<rho> = "Y i", unfolded fdoms]
        show "fix_on_cond {x. fmap_bottom (fdom (\<Squnion> i. Y i) \<union> heapVars h) \<sqsubseteq> x}
               (fmap_bottom (fdom (Lub Y) \<union> heapVars h)) (\<lambda>a. Y i f++ heapToEnv h (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>a\<^esub>))"
           by metis
    qed
qed

end


locale has_cont_ESem = has_ESem +
  assumes ESem_cont: "\<And> e. cont (ESem e)"
begin

  lemma HSem_def':
    shows "\<lbrace>h\<rbrace>\<rho> = fix_on' (fmap_bottom (fdom \<rho> \<union> heapVars h)) (\<lambda> \<rho>'. \<rho> f++ heapToEnv h (\<lambda> e. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>))"
    unfolding HSem_def using ESem_cont by metis

  lemma fix_on_cond_HSem:
    shows "fix_on_cond {x. fmap_bottom (fdom \<rho> \<union> heapVars h) \<sqsubseteq> x}
            (fmap_bottom (fdom \<rho> \<union> heapVars h)) (\<lambda>\<rho>'. \<rho> f++ heapToEnv h (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>))"
    apply (rule fix_on_cond_HSem') using ESem_cont by metis

  lemma HSem_ind:
    assumes "adm P"
    assumes "P (fmap_bottom (fdom \<rho> \<union> heapVars h))"
    assumes step: "\<And> y. fdom y = fdom \<rho> \<union> heapVars h \<Longrightarrow>
          P y \<Longrightarrow>  P (\<rho> f++ (heapToEnv h (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>y\<^esub>)))"
    shows "P (\<lbrace>h\<rbrace>\<rho>)"
    unfolding HSem_def'
    apply (rule fix_on_ind[OF fix_on_cond_HSem])
    apply (rule adm_is_adm_on[OF `adm P`])
    apply fact
    apply (rule step)
    apply simp
    apply assumption
    done
  
  lemma parallel_HSem_ind:
    assumes "adm (\<lambda>\<rho>'. P (fst \<rho>') (snd \<rho>'))"
    assumes "P (fmap_bottom (fdom \<rho> \<union> heapVars h)) (fmap_bottom (fdom \<rho>2 \<union> heapVars h2))"
    assumes step: "\<And>y z. fdom y = fdom \<rho> \<union> heapVars h \<Longrightarrow>
            fdom z = fdom \<rho>2 \<union> heapVars h2 \<Longrightarrow>
            P y z \<Longrightarrow>
            P (\<rho> f++ (heapToEnv h (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>y\<^esub>))) (\<rho>2 f++ (heapToEnv h2 (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>z\<^esub>)))"
    shows "P (\<lbrace>h\<rbrace>\<rho>) (\<lbrace>h2\<rbrace>\<rho>2)"
    unfolding HSem_def'
    apply (rule parallel_fix_on_ind[OF fix_on_cond_HSem fix_on_cond_HSem])
    apply (rule adm_is_adm_on[OF `adm _`])
    apply fact
    apply (rule step)
    apply simp+
    done
  
  lemma HSem_eq:
    shows "\<lbrace>h\<rbrace>\<rho> = \<rho> f++ (heapToEnv h (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>h\<rbrace>\<rho>\<^esub>))"
    unfolding HSem_def'
    by (rule fix_on_eq[OF fix_on_cond_HSem])  
  
  lemma the_lookup_HSem_other:
    assumes "y \<notin> heapVars h"
    shows "(\<lbrace>h\<rbrace>\<rho>) f! y = \<rho> f! y"
    apply (subst HSem_eq)
    using assms by simp
  
  lemma the_lookup_HSem_heap:
    assumes "y \<in> heapVars h"
    shows "(\<lbrace>h\<rbrace>\<rho>) f! y = \<lbrakk> the (map_of h y) \<rbrakk>\<^bsub>\<lbrace>h\<rbrace>\<rho>\<^esub>"
    apply (subst HSem_eq)
    using assms by (simp add: lookupHeapToEnv)

  lemma fdom_HSem[simp]:
    "fdom (\<lbrace>h\<rbrace>\<rho>) = fdom \<rho> \<union> heapVars h"
    by (subst HSem_eq, simp)

  lemma fmap_restr_fmap_addI:"finite S \<Longrightarrow> fdom \<rho>1 - fdom \<rho>2 \<subseteq> S \<Longrightarrow> fmap_restr S \<rho>1 f++ \<rho>2 = \<rho>1 f++ \<rho>2"
    apply (rule fmap_eqI)
    apply auto[1]
    apply auto
    by (metis lookup_fmap_add1 lookup_fmap_add2 lookup_fmap_restr)

  lemma HSem_restr:
    "\<lbrace>h\<rbrace>(fmap_restr (fdom \<rho> - heapVars h) \<rho>) = \<lbrace>h\<rbrace>\<rho>"
    apply (rule parallel_HSem_ind)
    apply simp
    apply auto
    apply (subst fmap_restr_fmap_addI)
    apply simp_all
    done
  
  lemma HSem_reorder:
    assumes "distinctVars \<Gamma>"
    assumes "distinctVars \<Delta>"
    assumes "set \<Gamma> = set \<Delta>"
    shows "\<lbrace>\<Gamma>\<rbrace>\<rho> = \<lbrace>\<Delta>\<rbrace>\<rho>"
  by (simp add: HSem_def' heapToEnv_reorder[OF assms] assms(3) heapVars_def)
  
  lemma HSem_reorder_head:
    assumes "x \<noteq> y"
    shows "\<lbrace>(x,e1)#(y,e2)#\<Gamma>\<rbrace>\<rho> = \<lbrace>(y,e2)#(x,e1)#\<Gamma>\<rbrace>\<rho>"
  proof-
    have "set ((x,e1)#(y,e2)#\<Gamma>) = set ((y,e2)#(x,e1)#\<Gamma>)"
      by auto
    thus ?thesis      
      unfolding HSem_def  heapToEnv_reorder_head[OF assms]
      by (simp add: heapVars_def)
  qed
  
  lemma HSem_reorder_head_append:
    assumes "x \<notin> heapVars \<Gamma>"
    shows "\<lbrace>(x,e)#\<Gamma>@\<Delta>\<rbrace>\<rho> = \<lbrace>\<Gamma> @ ((x,e)#\<Delta>)\<rbrace>\<rho>"
  proof-
    have "set ((x,e)#\<Gamma>@\<Delta>) = set (\<Gamma> @ ((x,e)#\<Delta>))" by auto
    thus ?thesis
      unfolding HSem_def  heapToEnv_reorder_head_append[OF assms]
      by (simp add: )
  qed  
    
  lemma fmap_restr_HSem_noop:
    assumes "heapVars \<Gamma> \<inter> fdom \<rho> = {}"
    shows "fmap_restr (fdom \<rho>) (\<lbrace>\<Gamma>\<rbrace>\<rho>) = \<rho>"
    apply (rule fmap_eqI)
    using assms apply auto[1]
    using assms apply auto[1]
    apply (subst the_lookup_HSem_other)
    apply auto
    done
  
  lemma HSem_disjoint_less:
    assumes "heapVars \<Gamma> \<inter> fdom \<rho> = {}"
    shows "\<rho> \<le> \<lbrace>\<Gamma>\<rbrace>\<rho>"
    using assms
  by (metis fmap_less_restrict fmap_restr_HSem_noop)

  lemma HSem_Nil[simp]: "\<lbrace>[]\<rbrace>\<rho> = \<rho>"
    by (subst HSem_eq, simp)

  lemma iterative_HSem:
    assumes "x \<notin> heapVars \<Gamma>"
    shows "\<lbrace>(x,e) # \<Gamma>\<rbrace>\<rho> =
         fix_on' (fmap_bottom (insert x (fdom \<rho> \<union> heapVars \<Gamma>)))
            (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>\<rho>'))( x f\<mapsto> \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>))"
  proof-
    interpret iterative
      where e1 =  "\<lambda> \<rho>'. heapToEnv \<Gamma> (\<lambda> e. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>)"
      and e2 = "\<lambda> \<rho>'. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>"
      and S = "heapVars \<Gamma>"
      and x = x
      and D =  "insert x (fdom \<rho> \<union> heapVars \<Gamma>) "
      apply -
      apply unfold_locales
      using assms
      by (simp_all add: ESem_cont)

    have "\<lbrace>(x,e) # \<Gamma>\<rbrace>\<rho> = fix_on' b L"
      by (simp add: HSem_def' fmap_add_upd)
    also have "\<dots> = fix_on' b R"
      by (rule iterative_fmap_add)
    also have "\<dots> = fix_on' (fmap_bottom (insert x (fdom \<rho> \<union> heapVars \<Gamma>)))
            (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>\<rho>'))( x f\<mapsto> \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>))"
      apply (rule fix_on_cong[OF condR])
      apply (simp add: HSem_def')
      apply (drule sym)
      apply simp
      by (metis Un_commute Un_left_absorb)
    finally show ?thesis.
  qed

  lemma iterative_HSem'_cond:
    assumes "x \<notin> heapVars \<Gamma>"
    shows "fix_on_cond {\<rho>'. fmap_bottom (insert x (fdom \<rho> \<union> heapVars \<Gamma>)) \<sqsubseteq> \<rho>'}
             (fmap_bottom (insert x (fdom \<rho> \<union> heapVars \<Gamma>)))
             (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>\<rho>'))( x f\<mapsto> \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>'\<^esub>))"
  proof-
    interpret iterative
      where e1 =  "\<lambda> \<rho>'. heapToEnv \<Gamma> (\<lambda> e. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>)"
      and e2 = "\<lambda> \<rho>'. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>"
      and S = "heapVars \<Gamma>"
      and x = x
      and D =  "insert x (fdom \<rho> \<union> heapVars \<Gamma>) "
      apply -
      apply unfold_locales
      using assms
      by (simp_all add: ESem_cont)

    show ?thesis
      apply (rule fix_on_cond_cong[OF condR'])
      apply (simp add: HSem_def')
      apply (drule sym)
      apply simp
      by (metis Un_commute Un_left_absorb)
  qed

  lemma iterative_HSem':
    assumes "x \<notin> heapVars \<Gamma>"
    shows "fix_on' (fmap_bottom (insert x (fdom \<rho> \<union> heapVars \<Gamma>)))
            (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>\<rho>'))( x f\<mapsto> \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>)) 
       = fix_on' (fmap_bottom (insert x (fdom \<rho> \<union> heapVars \<Gamma>)))
            (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>\<rho>'))( x f\<mapsto> \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>'\<^esub>))"
  proof-
    interpret iterative
      where e1 =  "\<lambda> \<rho>'. heapToEnv \<Gamma> (\<lambda> e. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>)"
      and e2 = "\<lambda> \<rho>'. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>"
      and S = "heapVars \<Gamma>"
      and x = x
      and D =  "insert x (fdom \<rho> \<union> heapVars \<Gamma>) "
      apply -
      apply unfold_locales
      using assms
      by (simp_all add: ESem_cont)

    have "fix_on' (fmap_bottom (insert x (fdom \<rho> \<union> heapVars \<Gamma>)))
            (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>\<rho>'))( x f\<mapsto> \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>)) =
          fix_on' b R"
      apply (rule fix_on_cong[symmetric, OF condR])
      apply (simp add: HSem_def')
      apply (drule sym)
      apply simp
      by (metis Un_commute Un_left_absorb)
    also have "\<dots> = fix_on' b L"
      by (rule iterative_fmap_add[symmetric])
    also have "\<dots> = fix_on' b R'"
      by (rule iterative_fmap_add')
    also have "\<dots> = fix_on' (fmap_bottom (insert x (fdom \<rho> \<union> heapVars \<Gamma>)))
            (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>\<rho>'))( x f\<mapsto> \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>'\<^esub>))"
      apply (rule fix_on_cong[OF condR'])
      apply (simp add: HSem_def')
      apply (drule sym)
      apply simp
      by (metis Un_commute Un_left_absorb)
    finally
    show ?thesis.
  qed

end

lemma HSem_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> ESem1 e = ESem2 e); env1 = env2 ; heap1 = heap2  \<rbrakk>
      \<Longrightarrow> has_ESem.HSem ESem1 heap1 env1 = has_ESem.HSem  ESem2 heap2 env2"
  unfolding has_ESem.HSem_def
  by (auto cong:heapToEnv_cong)

subsubsection {* Equivariance *}

lemma subcpo_eqvt[eqvt]:
  fixes S :: "('a::cont_pt) set"
  assumes "subcpo S"
  shows "subcpo (\<pi> \<bullet> S)"
proof(rule subcpoI)
  fix Y :: "nat \<Rightarrow> 'a"
  assume "chain Y"
    hence "chain (-\<pi> \<bullet> Y)" by (rule chain_eqvt)
  moreover
  assume "\<And> i. Y i \<in> \<pi> \<bullet> S"
  hence "\<And> i. - \<pi> \<bullet> Y i \<in> S" by (metis (full_types) mem_permute_iff permute_minus_cancel(1))
  hence "\<And> i. (- \<pi> \<bullet> Y) i \<in> S" by (metis eqvt_apply permute_pure)
  ultimately
  have "(\<Squnion> i. (- \<pi> \<bullet> Y) i) \<in> S" by (metis subcpo.cpo'[OF assms])
  hence "\<pi> \<bullet> (\<Squnion> i. (- \<pi> \<bullet> Y) i) \<in> \<pi> \<bullet> S"  by (metis mem_permute_iff)
  find_theorems permute cont
  thus "(\<Squnion> i. Y i) \<in> \<pi> \<bullet> S"
    apply -
    apply (subst (asm) cont2contlubE[OF perm_cont `chain (-\<pi> \<bullet> Y)`])
    by (metis image_image permute_minus_cancel(1) permute_set_eq_image range_eqvt)
qed

lemma subpcpo_bot_eqvt[eqvt]:
  fixes S :: "('a::cont_pt) set"
  assumes "subpcpo_bot S b"
  shows "subpcpo_bot (\<pi> \<bullet> S) (\<pi> \<bullet> b)"
  apply (rule subpcpo_botI)
  apply (metis subcpo.cpo'[OF subcpo_eqvt[OF subpcpo_is_subcpo[OF subpcpo_bot_is_subpcpo[OF assms]]]])
  apply (metis bottom_of_subpcpo_bot_there[OF assms] mem_permute_iff)
  apply (metis (full_types) bottom_of_subpcpo_bot_minimal[OF assms] eqvt_bound mem_permute_iff perm_cont_simp)
  done

lemma subpcpo_eqvt[eqvt]:
  fixes S :: "('a::cont_pt) set"
  assumes "subpcpo S"
  shows "subpcpo (\<pi> \<bullet> S)"
  by (rule subpcpo_bot_is_subpcpo[OF subpcpo_bot_eqvt[OF subpcpo_is_subpcpo_bot[OF assms]]])

lemma bottom_of_eqvt:
  assumes "subpcpo S"
  shows "\<pi> \<bullet> (bottom_of (S ::('a::cont_pt) set)) = bottom_of (\<pi> \<bullet> S)"
  by (rule bottom_of_subpcpo_bot[symmetric, OF subpcpo_bot_eqvt[OF  subpcpo_is_subpcpo_bot[OF assms]]])

lemma closed_on_eqvt:
  "closed_on S F \<Longrightarrow> closed_on (\<pi> \<bullet> S) (\<pi> \<bullet> F)"
  apply (rule closed_onI)
  apply (simp add: permute_set_def)
  by (metis closed_onE eqvt_apply)

lemma cont_eqvt[eqvt]:
  "cont (F::'a::cont_pt \<Rightarrow> 'b::cont_pt) \<Longrightarrow> cont (\<pi> \<bullet> F)"
  apply (rule contI)
  apply (drule_tac Y = "unpermute \<pi> Y" in contE)
  apply (auto intro: chain_eqvt simp add: unpermute_def)[1]
  apply (drule perm_is_lub_eqvt[of _ _ "\<pi>"])
  apply (subst (asm) eqvt_apply[of _ F])
  apply (subst (asm) lub_eqvt)
  apply (rule cpo)
  apply (auto intro: chain_eqvt simp add: unpermute_def)[1]
  apply perm_simp
  apply assumption
  done

lemma chain_on_eqvt:
  "chain_on (S::'a::cont_pt set) Y \<Longrightarrow> chain_on (\<pi> \<bullet> S) (\<pi> \<bullet> Y)"
  apply (rule chain_onI)
  apply (drule_tac i = i in chain_onE)
  apply (metis perm_cont_simp permute_fun_app_eq permute_pure)
  apply (drule_tac i = i in chain_on_is_on)
  by (metis (full_types) mem_permute_iff permute_fun_app_eq permute_pure)

lemma cont_on_eqvt:
  "cont_on S (F::'a::cont_pt \<Rightarrow> 'b::cont_pt) \<Longrightarrow> cont_on (\<pi> \<bullet> S) (\<pi> \<bullet> F)"
  apply (rule cont_onI)
  apply (drule_tac Y = "unpermute \<pi> Y" in cont_onE)
  apply (auto intro: chain_eqvt simp add: unpermute_def)[1]
  apply (metis chain_on_eqvt permute_minus_cancel(2))
  apply (drule perm_is_lub_eqvt[of _ _ "\<pi>"])
  apply (subst (asm) eqvt_apply[of _ F])
  apply (subst (asm) lub_eqvt)
  apply (rule cpo)
  apply (drule chain_on_is_chain)
  apply (auto intro: chain_eqvt simp add: unpermute_def)[1]
  apply perm_simp
  apply assumption
  done


lemma fix_on_cond_eqvt:
  assumes "fix_on_cond S (b::'a::cont_pt) F"
  shows "fix_on_cond (\<pi> \<bullet> S) (\<pi> \<bullet> b) (\<pi> \<bullet> F)"
proof
  from assms
  have pcpo1: "subpcpo S" and closed: "closed_on S F" and cont: "cont_on S F" and [simp]:"b = bottom_of S"
    by (metis fix_on_cond.cases)+

  show "subpcpo (\<pi> \<bullet> S)" by (rule subpcpo_eqvt[OF pcpo1])
  show "bottom_of (\<pi> \<bullet> S) = \<pi> \<bullet> b" by (simp add: bottom_of_eqvt[OF pcpo1, symmetric])
  show "closed_on (\<pi> \<bullet> S) (\<pi> \<bullet> F)" by (rule closed_on_eqvt[OF closed])
  show "cont_on (\<pi> \<bullet> S) (\<pi> \<bullet> F)" by (rule cont_on_eqvt[OF cont])
qed

lemma fix_on_eqvt:
  assumes "fix_on_cond S (b::'a::cont_pt) F"
  shows "\<pi> \<bullet> (fix_on' b F) = fix_on' (\<pi> \<bullet> b) (\<pi> \<bullet> F)"
proof-
  have permuted: "fix_on_cond (\<pi> \<bullet> S) (\<pi> \<bullet> b) (\<pi> \<bullet> F)"
    by (rule fix_on_cond_eqvt[OF assms])
  show ?thesis
    apply (rule parallel_fix_on_ind[OF assms permuted])
    apply (rule adm_is_adm_on, auto)[1]
    by (auto simp add: eqvt_apply)
qed

lemma HSem_eqvt[eqvt]:
  "\<pi> \<bullet> has_ESem.HSem ESem h \<rho> = has_ESem.HSem (\<pi> \<bullet> ESem) (\<pi> \<bullet> h) (\<pi> \<bullet> \<rho>)"
proof(cases "\<forall> e \<in> snd ` set h.  cont (ESem e)")
case True
  from permute_boolI[OF this, where p = \<pi>]
  have True_permuted: "\<forall> e \<in> snd ` set (\<pi> \<bullet> h). cont ((\<pi> \<bullet> ESem) e)"
    by perm_simp

  show ?thesis          
   unfolding has_ESem.HSem_def if_P[OF True]  if_P[OF True_permuted] 
   apply (subst fix_on_eqvt[OF has_ESem.fix_on_cond_HSem'])
   apply (metis True)
   apply (subst fmap_bottom_eqvt, simp)
   apply perm_simp
   apply rule
   done
next
case False 
  from permute_boolI[OF this, where p = \<pi>]
  have False_permuted: "\<not> (\<forall> e \<in> snd ` set (\<pi> \<bullet> h). cont ((\<pi> \<bullet> ESem) e))"
    by perm_simp
  show ?thesis
   unfolding has_ESem.HSem_def if_not_P[OF False]  if_not_P[OF False_permuted] 
   apply (subst fmap_bottom_eqvt, simp)
   apply perm_simp
   apply rule
   done
qed


end
