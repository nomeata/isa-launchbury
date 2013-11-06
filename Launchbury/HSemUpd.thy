theory HSemUpd
  imports "HeapToEnv" "DistinctVars-Nominal" "HOLCF-Set-Nominal" "FMap-Nominal-HOLCF" "HasESem"
begin

subsubsection {* A locale for heap semantics, abstract in the expression semantics *}

text {*
This theory follows closely the theory @{text HSem}, but uses right-sided updates of envrionments
instead of least upper bounds. 
*}

context has_ESem
begin

definition HSem :: "('var \<times> 'exp) list \<Rightarrow> 'var f\<rightharpoonup> 'value \<rightarrow> 'var f\<rightharpoonup> 'value" 
  where
  "HSem h = (\<Lambda> \<rho> . fix_on' (f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (\<lambda> \<rho>'. \<rho> f++ heapToEnv h (\<lambda> e. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>)))"

abbreviation HSem_syn ("\<lbrace> _ \<rbrace>_"  [60,60] 60) where "\<lbrace>\<Gamma>\<rbrace>\<rho> \<equiv> HSem \<Gamma> \<cdot> \<rho>"

lemma fix_on_cond_HSem:
  shows "fix_on_cond {x. f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub> \<sqsubseteq> x}
          (f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (\<lambda>\<rho>'. \<rho> f++ heapToEnv h (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>))"
  apply (rule fix_on_condI)
  apply (rule subpcpo_cone_above)
  apply (rule bottom_of_cone_above)
  apply (rule closed_onI, simp)
  apply (rule cont_is_cont_on, simp)
  done

lemma HSem_monofun'': "monofun (\<lambda> \<rho>. fix_on' (f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars \<Gamma>]\<^esub>) (\<lambda>\<rho>''. \<rho> f++ heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>''\<^esub>)))"
  apply (rule monofunI)
  apply (rule fix_on_mono2[OF fix_on_cond_HSem fix_on_cond_HSem])
  unfolding fmap_below_dom[OF assms] apply rule
  by (simp, intro fmap_add_mono assms heapToEnv_mono  cont2monofunE[OF cont2cont_heapToEnv] cont_Rep_cfun2)

lemma HSem_cont'':
  assumes "chain Y"
  shows "fix_on' (f\<emptyset>\<^bsub>[fdom (\<Squnion> i. Y i) \<union> heapVars \<Gamma>]\<^esub>) (\<lambda>\<rho>'. (\<Squnion> i. Y i) f++ heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)) =
        (\<Squnion> i. fix_on' (f\<emptyset>\<^bsub>[fdom (Y i) \<union> heapVars \<Gamma>]\<^esub>) (\<lambda>\<rho>'. Y i f++ heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>)))"
proof-
  have fdoms:"\<And> i. fdom (Y i) = fdom (\<Squnion> i. Y i)" (is "\<And> _ .(_ = ?d)") by (metis chain_fdom `chain Y`) 
  show ?thesis
    unfolding fdoms
    apply (rule fix_on_cont[OF `chain Y`, where S = "{x . f\<emptyset>\<^bsub>[fdom (\<Squnion> i. Y i) \<union> heapVars \<Gamma>]\<^esub> \<sqsubseteq> x}"])
    apply (rule fix_on_cond_HSem[where \<rho> = "Y i", standard, where Y = Y, unfolded fdoms])
    apply simp
    done
qed

lemma HSem_cont':
  shows "cont (\<lambda> \<rho>. fix_on' (f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars \<Gamma>]\<^esub>) (\<lambda>\<rho>''. \<rho> f++ heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>''\<^esub>)))"
  apply (rule contI2)
  apply (rule HSem_monofun'')
  apply (erule eq_imp_below[OF HSem_cont''])
  done

lemma HSem_def':
    "\<lbrace>\<Gamma>\<rbrace>\<rho> = fix_on' (f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars \<Gamma>]\<^esub>) (\<lambda> \<rho>'. \<rho> f++ heapToEnv \<Gamma> (\<lambda> e. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>))"
  unfolding HSem_def
  by (rule arg_cong[OF beta_cfun[OF HSem_cont']])

subsubsection {* Induction and other lemmas about @{term HSem} *}

  lemma HSem_ind:
    assumes "adm P"
    assumes "P (f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>)"
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

  lemma HSem_below:
    assumes [simp]:"fdom r = fdom \<rho> \<union> heapVars h" 
    assumes rho: "\<And>x. x \<in> fdom \<rho> \<Longrightarrow> x \<notin> heapVars h \<Longrightarrow> \<rho> f! x \<sqsubseteq> r f! x"
    assumes h: "\<And>x. x \<in> heapVars h \<Longrightarrow> \<lbrakk>the (map_of h x)\<rbrakk>\<^bsub>r\<^esub> \<sqsubseteq> r f! x"
    shows "\<lbrace>h\<rbrace>\<rho> \<sqsubseteq> r"
  proof (rule HSem_ind)
    case goal1 show ?case by (auto intro: adm_is_adm_on)
    case goal2 show ?case by (simp add: to_bot_fmap_def)
    case (goal3 \<rho>')
      show ?case
      by (rule fmap_add_belowI)
         (auto simp add: lookupHeapToEnv  below_trans[OF monofun_cfun_arg[OF `\<rho>' \<sqsubseteq> r`] h] rho)
  qed  

  lemma HSem_fempty_below:
    assumes [simp]:"fdom r = heapVars h" 
    assumes h: "\<And>x. x \<in> heapVars h \<Longrightarrow> \<lbrakk>the (map_of h x)\<rbrakk>\<^bsub>r\<^esub> \<sqsubseteq> r f! x"
    shows "\<lbrace>h\<rbrace>f\<emptyset> \<sqsubseteq> r"
    using assms 
    by (metis HSem_below fdomIff lookup_fempty subsetI sup.order_iff sup_commute)

  lemma parallel_HSem_ind:
    assumes "adm (\<lambda>\<rho>'. P (fst \<rho>') (snd \<rho>'))"
    assumes "P (f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (f\<emptyset>\<^bsub>[fdom \<rho>2 \<union> heapVars h2]\<^esub>)"
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

  lemma fmap_lookup_bot_HSem_other:
    assumes "y \<notin> heapVars h"
    shows "(\<lbrace>h\<rbrace>\<rho>) f!\<^sub>\<bottom> y = \<rho> f!\<^sub>\<bottom> y"
    using assms
    by (subst HSem_eq, cases "y \<in> fdom \<rho>", auto)
  
  lemma the_lookup_HSem_heap:
    assumes "y \<in> heapVars h"
    shows "(\<lbrace>h\<rbrace>\<rho>) f! y = \<lbrakk> the (map_of h y) \<rbrakk>\<^bsub>\<lbrace>h\<rbrace>\<rho>\<^esub>"
    apply (subst HSem_eq)
    using assms by (simp add: lookupHeapToEnv)

  lemma fdom_HSem[simp]:
    "fdom (\<lbrace>h\<rbrace>\<rho>) = fdom \<rho> \<union> heapVars h"
    by (subst HSem_eq, simp)

  lemma fmap_restr_fmap_addI:"fdom \<rho>1 - fdom \<rho>2 \<subseteq> S \<Longrightarrow> fmap_restr S \<rho>1 f++ \<rho>2 = \<rho>1 f++ \<rho>2"
    by rule (auto simp add: lookup_fmap_add_eq)

  lemma HSem_restr:
    "\<lbrace>h\<rbrace>(\<rho> f|` (fdom \<rho> - heapVars h)) = \<lbrace>h\<rbrace>\<rho>"
    apply (rule parallel_HSem_ind)
    apply simp
    apply auto[1]
    apply (subst fmap_restr_fmap_addI)
    apply simp_all
    done

  lemma HSem_restr':
    "\<lbrace>h\<rbrace>(\<rho> f|` (- heapVars h)) = \<lbrace>h\<rbrace>\<rho>"
    apply (rule parallel_HSem_ind)
    apply simp
    apply auto[1]
    apply (subst fmap_restr_fmap_addI)
    apply auto
    done

  lemma HSem_fresh_cong:
    assumes "\<rho> f|` (- heapVars h) = \<rho>' f|` (- heapVars h)"
    shows "\<lbrace>h\<rbrace>\<rho> = \<lbrace>h\<rbrace>\<rho>'"
    apply (subst (1 2) HSem_restr'[symmetric])
    by (simp add: assms)

  lemma HSem_reorder:
    assumes "map_of \<Gamma> = map_of \<Delta>"
    shows "\<lbrace>\<Gamma>\<rbrace>\<rho> = \<lbrace>\<Delta>\<rbrace>\<rho>"
  by (simp add: HSem_def' heapToEnv_reorder[OF assms] assms dom_map_of_conv_heapVars[symmetric])
  
  lemma HSem_reorder_head:
    assumes "x \<noteq> y"
    shows "\<lbrace>(x,e1)#(y,e2)#\<Gamma>\<rbrace>\<rho> = \<lbrace>(y,e2)#(x,e1)#\<Gamma>\<rbrace>\<rho>"
  proof-
    have "set ((x,e1)#(y,e2)#\<Gamma>) = set ((y,e2)#(x,e1)#\<Gamma>)"
      by auto
    thus ?thesis      
      unfolding HSem_def heapToEnv_reorder_head[OF assms]
      by (simp add: heapVars_def)
  qed
  
  lemma HSem_reorder_head_append:
    assumes "x \<notin> heapVars \<Gamma>"
    shows "\<lbrace>(x,e)#\<Gamma>@\<Delta>\<rbrace>\<rho> = \<lbrace>\<Gamma> @ ((x,e)#\<Delta>)\<rbrace>\<rho>"
  proof-
    have "set ((x,e)#\<Gamma>@\<Delta>) = set (\<Gamma> @ ((x,e)#\<Delta>))" by auto
    thus ?thesis
      unfolding HSem_def  heapToEnv_reorder_head_append[OF assms]
      by simp
  qed  

 lemma fmap_restr_HSem:
    assumes "heapVars \<Gamma> \<inter> S = {}"
    shows "fmap_restr S (\<lbrace>\<Gamma>\<rbrace>\<rho>) = fmap_restr S \<rho>"
    apply (rule fmap_eqI)
    using assms apply auto[1]
    using assms apply auto[1]
    apply (subst the_lookup_HSem_other)
    apply auto
    done
  
  lemma fmap_restr_HSem_noop:
    assumes "heapVars \<Gamma> \<inter> fdom \<rho> = {}"
    shows "fmap_restr (fdom \<rho>) (\<lbrace>\<Gamma>\<rbrace>\<rho>) = \<rho>"
    by (simp add: fmap_restr_HSem[OF assms] fmap_restr_useless)
 
  lemma HSem_disjoint_less:
    assumes "heapVars \<Gamma> \<inter> fdom \<rho> = {}"
    shows "\<rho> \<le> \<lbrace>\<Gamma>\<rbrace>\<rho>"
    using assms
  by (metis fmap_less_restrict fmap_restr_HSem_noop)

  lemma HSem_Nil[simp]: "\<lbrace>[]\<rbrace>\<rho> = \<rho>"
    by (subst HSem_eq, simp)

subsubsection {* Re-calculating the semantics of the heap is idempotent *} 

  lemma HSem_redo:
    shows "\<lbrace>\<Gamma>\<rbrace>(\<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>) f|` (fdom \<rho> \<union> heapVars \<Delta>) = \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>" (is "?LHS = ?RHS")
  proof (rule below_antisym)
    show "?LHS \<sqsubseteq> ?RHS"
    by (rule HSem_below) (auto simp add: the_lookup_HSem_heap)
    
  
    show "?RHS \<sqsubseteq> ?LHS"
    proof(rule HSem_below)
    case goal1 show ?case by auto
    next
    case goal2
      thus ?case by (auto simp add: the_lookup_HSem_other)
    next
    case (goal3 x)
      thus ?case
      proof(cases "x \<in> heapVars \<Gamma>")
      case True
        thus ?thesis by (auto simp add: the_lookup_HSem_heap)
      next
      case False
        hence delta: "x \<in> heapVars \<Delta>" using goal3 by auto
        with False  `?LHS \<sqsubseteq> ?RHS`
        show ?thesis by (auto simp add: the_lookup_HSem_other the_lookup_HSem_heap monofun_cfun_arg)
      qed
    qed
  qed


subsubsection {* Iterative definition of the heap semantics *}

  lemma iterative_HSem:
    assumes "x \<notin> heapVars \<Gamma>"
    shows "\<lbrace>(x,e) # \<Gamma>\<rbrace>\<rho> =
         fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars \<Gamma>)]\<^esub>)
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
      by (simp_all)

    have "\<lbrace>(x,e) # \<Gamma>\<rbrace>\<rho> = fix_on' b L"
      by (simp add: HSem_def' fmap_add_upd)
    also have "\<dots> = fix_on' b R"
      by (rule iterative_fmap_add)
    also have "\<dots> = fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars \<Gamma>)]\<^esub>)
            (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>\<rho>'))( x f\<mapsto> \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>))"
      by (rule fix_on_cong[OF condR], simp add: HSem_def')
    finally show ?thesis.
  qed

  lemma iterative_HSem'_cond:
    assumes "x \<notin> heapVars \<Gamma>"
    shows "fix_on_cond {\<rho>'. f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars \<Gamma>)]\<^esub> \<sqsubseteq> \<rho>'}
             (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars \<Gamma>)]\<^esub>)
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
      by simp_all

    show ?thesis
      by (rule fix_on_cond_cong[OF condR'], simp add: HSem_def')
  qed

  lemma iterative_HSem':
    assumes "x \<notin> heapVars \<Gamma>"
    shows "fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars \<Gamma>)]\<^esub>)
            (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>\<rho>'))( x f\<mapsto> \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>)) 
       = fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars \<Gamma>)]\<^esub>)
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
      by simp_all

    have "fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars \<Gamma>)]\<^esub>)
            (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>\<rho>'))( x f\<mapsto> \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>)) =
          fix_on' b R"
      by (rule fix_on_cong[symmetric, OF condR], simp add: HSem_def')
    also have "\<dots> = fix_on' b L"
      by (rule iterative_fmap_add[symmetric])
    also have "\<dots> = fix_on' b R'"
      by (rule iterative_fmap_add')
    also have "\<dots> = fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars \<Gamma>)]\<^esub>)
            (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>\<rho>'))( x f\<mapsto> \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>'\<^esub>))"
      by (rule fix_on_cong[OF condR'], simp add: HSem_def')
    finally
    show ?thesis.
  qed

end

lemma HSem_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> ESem1 e = ESem2 e); heap1 = heap2  \<rbrakk>
      \<Longrightarrow> has_ESem.HSem ESem1 heap1 = has_ESem.HSem ESem2 heap2"
  unfolding has_ESem.HSem_def
  by (auto cong:heapToEnv_cong)

subsubsection {* Equivariance *}

lemma HSem_eqvt[eqvt]:
  "\<pi> \<bullet> has_ESem.HSem ESem h = has_ESem.HSem (\<pi> \<bullet> ESem) (\<pi> \<bullet> h)"
proof-
  show ?thesis
   unfolding has_ESem.HSem_def
   apply (subst permute_Lam[OF HSemUpd.has_ESem.HSem_cont'])
   apply (rule arg_cong[where f = Abs_cfun])
   apply (subst eqvt_lambda)
   apply rule
   apply (subst fix_on_eqvt[OF has_ESem.fix_on_cond_HSem])
   apply perm_simp
   apply rule
   done
qed

subsubsection {* Fresh variables on the heap are irrelevant *}

context  has_ESem 
begin
  lemma HSem_ignores_fresh_restr':
    assumes "fv \<Gamma> \<subseteq> S"
    assumes "\<And> x \<rho>. x \<in> heapVars \<Gamma> \<Longrightarrow> \<lbrakk> the (map_of \<Gamma> x) \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> the (map_of \<Gamma> x) \<rbrakk>\<^bsub>\<rho> f|` (fv (the (map_of \<Gamma> x)))\<^esub>"
    shows "(\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` S = \<lbrace>\<Gamma>\<rbrace>\<rho> f|` S"
  proof(induction rule: parallel_HSem_ind[case_names adm base step])
    case adm thus ?case by simp
  next
    case base
      from assms(1) heapVars_fv_subset have "heapVars \<Gamma> \<subseteq> S" by auto
      thus ?case by -(rule, auto)
  next
    case (step y z)
    thm step(3)[symmetric]
    have "heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>y\<^esub>) = heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>z\<^esub>)"
    proof(rule heapToEnv_cong')
      fix x
      assume "x \<in> heapVars \<Gamma>"
      hence "fv (the (map_of \<Gamma> x)) \<subseteq> fv \<Gamma>" by (rule map_of_fv_subset)
      with assms(1)
      have "fv (the (map_of \<Gamma> x)) \<inter> S = fv (the (map_of \<Gamma> x))" by auto
      with `x \<in> heapVars \<Gamma>`
      show "\<lbrakk> the (map_of \<Gamma> x) \<rbrakk>\<^bsub>y\<^esub> = \<lbrakk> the (map_of \<Gamma> x) \<rbrakk>\<^bsub>z\<^esub>"
        by (subst (1 2) assms(2)[OF `x \<in> heapVars \<Gamma>`]) (simp add: step(3)[symmetric])
    qed
    moreover
    have "heapVars \<Gamma> \<subseteq> S" using heapVars_fv_subset assms(1) by auto
    ultimately
    show ?case by (simp add: fmap_restr_add fmap_restr_heapToEnv_noop)
  qed
end

locale has_ignore_fresh_ESem = has_ESem +
  assumes fv_supp: "supp e = atom ` (fv e :: 'b set)"
  assumes ESem_considers_fv: "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho> f|` (fv e)\<^esub>"
begin
 
  lemma ESem_fresh_cong:
    assumes "\<rho> f|` (fv e) = \<rho>' f|` (fv e)"
    shows "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>"
  by (metis assms ESem_considers_fv )
  
  lemma ESem_ignores_fresh_restr:
    assumes "atom ` S \<sharp>* e"
    shows "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho> f|` (- S)\<^esub>"
  proof-
    have "fv e \<inter> - S = fv e" using assms by (auto simp add: fresh_def fresh_star_def fv_supp)
    thus ?thesis by (subst (1 2) ESem_considers_fv) simp
  qed

  lemma ESem_ignores_fresh_restr':
    assumes "atom ` (fdom \<rho> - S) \<sharp>* e"
    shows "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho> f|` S\<^esub>"
  proof-
    have "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> =  \<lbrakk> e \<rbrakk>\<^bsub>\<rho> f|` (- (fdom \<rho> - S))\<^esub>"
      by (rule ESem_ignores_fresh_restr[OF assms])
    also have "\<rho> f|` (- (fdom \<rho> - S)) = \<rho> f|` S" by auto
    finally show ?thesis.
  qed

  lemma ESem_ignores_fresh: "\<rho>1 \<le> \<rho>2 \<Longrightarrow> atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* e \<Longrightarrow> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>1\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>2\<^esub>"
    by (metis ESem_ignores_fresh_restr' fmap_less_restrict)  

  lemma HSem_ignores_fresh_restr:
    assumes "atom ` S \<sharp>* \<Gamma>"
    shows "(\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` (- S) = \<lbrace>\<Gamma>\<rbrace>\<rho> f|` (- S)"
  proof-
    from assms have "fv \<Gamma> \<subseteq> - S" by (auto simp add: fv_def fresh_star_def fresh_def)
    thus ?thesis by (rule HSem_ignores_fresh_restr'[OF _ ESem_considers_fv])
  qed

subsubsection {* Adding a fresh variable to a heap does not affect its semantics *} 

  lemma HSem_add_fresh':
    assumes fresh: "atom x \<sharp> \<Gamma>"
    assumes "x \<notin> fdom \<rho>"
    assumes step: "\<And>e \<rho>'. fdom \<rho>' = fdom \<rho> \<union> heapVars ((x, e) # \<Gamma>) \<Longrightarrow> e \<in> snd ` set \<Gamma> \<Longrightarrow> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>' f|` (- {x})\<^esub>"
    shows  "(\<lbrace>(x, e) # \<Gamma>\<rbrace>\<rho>) f|` (fdom \<rho> \<union> heapVars \<Gamma>) = \<lbrace>\<Gamma>\<rbrace>\<rho>"
  proof (rule parallel_HSem_ind)
  case goal1 show ?case by simp
  case goal2 show ?case by auto
  case (goal3 y z)
    have "fmap_restr (fdom \<rho> \<union> heapVars \<Gamma>) \<rho> = \<rho>" by auto
    moreover
    have "x \<notin> fdom \<rho> \<union> heapVars \<Gamma>"
      using fresh `x \<notin> fdom \<rho>` by (auto simp add: fresh_Pair heapVars_not_fresh)
    hence "fdom y \<inter> (- {x}) = fdom \<rho> \<union> heapVars \<Gamma>"
      using goal3(1) by auto
    hence [simp]: "z = y f|` (- {x})"
      by (auto simp add: `_= z`[symmetric] intro: fmap_restr_cong)

    have "heapToEnv ((x, e) # \<Gamma>) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>y\<^esub>) f|` (fdom \<rho> \<union> heapVars \<Gamma>) = heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>y\<^esub>)"
      using `x \<notin> fdom \<rho> \<union> heapVars \<Gamma>` by auto
    moreover
    have "heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>y\<^esub>) = heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>z\<^esub>)"
      apply (rule heapToEnv_cong[OF refl])
      apply (subst (1) step)
      using goal3(1) apply auto
      done
    ultimately
    show ?case by (simp only: fmap_restr_add)
  qed

  lemma HSem_add_fresh:
    assumes "atom x \<sharp> \<Gamma>"
    assumes "x \<notin> fdom \<rho>"
    shows  "(\<lbrace>(x, e) # \<Gamma>\<rbrace>\<rho>) f|` (fdom \<rho> \<union> heapVars \<Gamma>) = \<lbrace>\<Gamma>\<rbrace>\<rho>"
  proof(rule HSem_add_fresh'[OF assms])
  case (goal1 e \<rho>')
    assume "e \<in> snd ` set \<Gamma>"
    hence "atom x \<sharp> e" by (metis assms(1) fresh_heap_expr')
    hence "fv e \<inter> -{x} = fv e" by (auto simp add: fv_def fresh_def)
    thus ?case by (simp cong: ESem_fresh_cong)
  qed
 

subsubsection {* Binding more variables increases knowledge *}

  lemma HSem_subset_below:
    assumes fresh: "atom ` heapVars \<Gamma> \<sharp>* \<Delta>" 
    shows "\<lbrace>\<Delta>\<rbrace>(\<rho> f|` (- heapVars \<Gamma>)) \<sqsubseteq> (\<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho>)  f|` (- heapVars \<Gamma>)"
  proof(rule HSem_below)
    from fresh
    show "fdom ((\<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho>) f|` (- heapVars \<Gamma>)) = fdom (\<rho> f|` (- heapVars \<Gamma>)) \<union> heapVars \<Delta>"
      by (auto dest: fresh_distinct )

    fix x
    assume [simp]: "x \<in> heapVars \<Delta>"
    with assms have *: "atom ` heapVars \<Gamma> \<sharp>* the (map_of \<Delta> x)" by (metis fresh_star_map_of)
    hence [simp]: "x \<notin> heapVars \<Gamma>" using fresh `x \<in> heapVars \<Delta>` by (metis fresh_star_def heapVars_not_fresh image_eqI)
    show "\<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>(\<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho>) f|` (- heapVars \<Gamma>)\<^esub> \<sqsubseteq> (\<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho>) f|` (- heapVars \<Gamma>) f! x"
      by (simp add: the_lookup_HSem_heap ESem_ignores_fresh_restr[OF *, symmetric])
   qed (simp add: the_lookup_HSem_other)

  subsubsection {* Additional, fresh bindings in one or two steps *}  

  lemma HSem_merge:
    assumes fresh: "atom ` heapVars \<Gamma> \<sharp>* \<Delta>"
    shows "\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> = \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
  proof(rule below_antisym)
    have map_of_eq: "map_of (\<Delta> @ \<Gamma>) = map_of (\<Gamma> @ \<Delta>)"
    proof
      fix x
      show "map_of (\<Delta> @ \<Gamma>) x = map_of (\<Gamma> @ \<Delta>) x"
      proof (cases "x \<in> heapVars \<Gamma>")
        case True
        hence "x \<notin> heapVars \<Delta>" by (metis fresh_distinct fresh IntI equals0D)
        thus "map_of (\<Delta> @ \<Gamma>) x = map_of (\<Gamma> @ \<Delta>) x"
          by (simp add: map_add_dom_app_simps dom_map_of_conv_heapVars)
      next
        case False
        thus "map_of (\<Delta> @ \<Gamma>) x = map_of (\<Gamma> @ \<Delta>) x"
          by (simp add: map_add_dom_app_simps dom_map_of_conv_heapVars)
      qed
    qed

    show "\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
    proof(rule HSem_below)
      fix x
      assume "x \<in> fdom (\<lbrace>\<Delta>\<rbrace>\<rho>)" and [simp]:"x \<notin> heapVars \<Gamma>"

      have "\<lbrace>\<Delta>\<rbrace>\<rho> f! x = ((\<lbrace>\<Delta>\<rbrace>\<rho>) f|` (- heapVars \<Gamma>)) f! x" by simp
      also have "\<dots> = \<lbrace>\<Delta>\<rbrace>(\<rho> f|` (- heapVars \<Gamma>)) f! x"
        by (rule arg_cong[OF HSem_ignores_fresh_restr[OF fresh]])
      also have "\<dots> \<sqsubseteq> (\<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho>)  f|` (- heapVars \<Gamma>) f! x"
        by (rule fmap_belowE[OF HSem_subset_below[OF fresh]] )
      also have "\<dots> = \<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho> f! x" by simp
      also have "\<dots> = \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>  f! x" by (rule arg_cong[OF HSem_reorder[OF map_of_eq]])
      finally
      show "\<lbrace>\<Delta>\<rbrace>\<rho> f! x \<sqsubseteq> \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho> f! x".
    qed (auto simp add: the_lookup_HSem_heap)

     have *: "\<And> x. x \<in> heapVars \<Delta> \<Longrightarrow> x \<notin> heapVars \<Gamma>"
      using fresh by (auto simp add: fresh_Pair fresh_star_def heapVars_not_fresh)

    have foo: "fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma> - (fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma>) \<inter> - heapVars \<Gamma> = heapVars \<Gamma>" by auto
    have foo2:"(fdom \<rho> \<union> heapVars \<Delta> - (fdom \<rho> \<union> heapVars \<Delta>) \<inter> - heapVars \<Gamma>) \<subseteq> heapVars \<Gamma>" by auto

    { fix x
      assume "x \<in> heapVars \<Delta>"
      hence *: "atom ` heapVars \<Gamma> \<sharp>* the (map_of \<Delta> x)"
        by (rule  fresh_star_map_of[OF _ fresh])

      have "\<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> = \<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>(\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>) f|` (- heapVars \<Gamma>)\<^esub>"
        by (rule ESem_ignores_fresh_restr[OF *])
      also have "(\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>) f|` (- heapVars \<Gamma>) = (\<lbrace>\<Delta>\<rbrace>\<rho>) f|` (- heapVars \<Gamma>)"
        by (simp add: fmap_restr_HSem)
      also have "\<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>\<dots>\<^esub> = \<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
        by (rule ESem_ignores_fresh_restr[symmetric, OF *])
      finally
      have "\<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> = \<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>".
    }
    thus "\<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>"
      by -(rule HSem_below, auto simp add: the_lookup_HSem_other the_lookup_HSem_heap *)
  qed

  subsubsection {* The semantics of let only adds new bindings *}
  
  lemma HSem_less:
    assumes fresh: "atom ` heapVars \<Gamma> \<sharp>* \<Delta>"
    assumes distinct: "heapVars \<Gamma> \<inter> fdom (\<lbrace>\<Delta>\<rbrace>\<rho>) = {}"
    shows "\<lbrace>\<Delta>\<rbrace>\<rho> \<le> \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
  proof-
    have "\<lbrace>\<Delta>\<rbrace>\<rho> \<le> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>"
      by (rule HSem_disjoint_less[OF distinct])
    also have "\<dots> =  \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
      apply (rule HSem_merge)
      using fresh by simp
    finally
    show ?thesis.
  qed

subsubsection {* Substitution *}

  lemma HSem_subst_exp:
    assumes "\<And>\<rho>'. fdom \<rho>' = fdom \<rho> \<union> (heapVars ((x,e)#\<Gamma>)) \<Longrightarrow>  \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub> = \<lbrakk> e' \<rbrakk>\<^bsub>\<rho>'\<^esub>"
    shows "\<lbrace>(x, e) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>"
    by (rule parallel_HSem_ind) (auto simp add: assms heapToEnv_subst_exp)

  lemma HSem_subst_expr_below:
    assumes below: "\<lbrakk> e1 \<rbrakk>\<^bsub>\<lbrace>(x, e2) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> e2 \<rbrakk>\<^bsub>\<lbrace>(x, e2) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    shows "\<lbrace>(x, e1) # \<Gamma>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>(x, e2) # \<Gamma>\<rbrace>\<rho>"
  proof (rule HSem_ind) back
  case goal1 show ?case by auto
  case goal2 show ?case by (simp add: to_bot_fmap_def)
  case (goal3 \<rho>')
    show ?case
      apply (subst HSem_eq)
      apply (rule fmap_add_mono[OF below_refl])
      apply simp
      apply (rule fmap_upd_mono)
      apply (rule cont2monofunE[OF cont2cont_heapToEnv[OF cont_Rep_cfun2] goal3(2)])
      apply (rule below_trans[OF cont2monofunE[OF cont_Rep_cfun2 goal3(2)] below])
      done
  qed
  
  lemma HSem_subst_expr:
    assumes below1: "\<lbrakk> e1 \<rbrakk>\<^bsub>\<lbrace>(x, e2) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> e2 \<rbrakk>\<^bsub>\<lbrace>(x, e2) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    assumes below2: "\<lbrakk> e2 \<rbrakk>\<^bsub>\<lbrace>(x, e1) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> e1 \<rbrakk>\<^bsub>\<lbrace>(x, e1) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    shows "\<lbrace>(x, e1) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, e2) # \<Gamma>\<rbrace>\<rho>"
    by (metis assms HSem_subst_expr_below below_antisym)

end

lemma parallel_HSem_ind_different_ESem:
  assumes "adm (\<lambda>\<rho>'. P (fst \<rho>') (snd \<rho>'))"
  assumes "P (f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (f\<emptyset>\<^bsub>[fdom \<rho>2 \<union> heapVars h2]\<^esub>)"
  assumes "\<And>y z. P y z \<Longrightarrow> P (\<rho> f++ heapToEnv h (\<lambda>e. ESem1 e $ y)) (\<rho>2 f++ heapToEnv h2 (\<lambda>e. ESem2 e $ z))"
  shows "P (has_ESem.HSem ESem1 h\<cdot>\<rho>) (has_ESem.HSem ESem2 h2\<cdot>\<rho>2)"
proof-
  interpret HSem1: has_ESem ESem1.
  interpret HSem2: has_ESem ESem2.

  show ?thesis
    unfolding HSem1.HSem_def' HSem2.HSem_def'
    apply (rule parallel_fix_on_ind[OF HSem1.fix_on_cond_HSem HSem2.fix_on_cond_HSem])
    apply (rule adm_is_adm_on[OF assms(1)])
    apply (rule assms(2))
    apply (erule assms(3))
    done
qed

end
