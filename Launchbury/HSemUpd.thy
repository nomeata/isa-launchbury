theory HSemUpd
  imports "HeapToEnv" "DistinctVars-Nominal" "HOLCF-Set-Nominal" "FMap-Utils" "HasESem"
begin

subsubsection {* A locale for heap semantics, abstract in the expression semantics *}

text {*
This theory follows closely the theory @{text HSem}, but uses right-sided updates of envrionments
instead of least upper bounds. 
*}

context has_ESem
begin

definition UHSem :: "('var \<times> 'exp) list \<Rightarrow> 'var f\<rightharpoonup> 'value \<Rightarrow> 'var f\<rightharpoonup> 'value" ("\<lbrace>_\<rbrace>_"  [60,60] 60)
  where
  "\<lbrace>h\<rbrace>\<rho> = 
    (if (\<forall> e \<in> snd `set h. cont (ESem e))
     then  fix_on' (f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (\<lambda> \<rho>'. \<rho> f++ heapToEnv h (\<lambda> e. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>))
     else (f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>))"

lemma UHSem_def'':
  assumes "\<And> e. e \<in> snd ` set h \<Longrightarrow> cont (ESem e)"
  shows "\<lbrace>h\<rbrace>\<rho> = fix_on' (f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (\<lambda> \<rho>'. \<rho> f++ heapToEnv h (\<lambda> e. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>))"
  unfolding UHSem_def using assms by metis

lemma fix_on_cond_UHSem':
  assumes cont: "\<And> e. e \<in> snd ` set h \<Longrightarrow> cont (ESem e)"
  shows "fix_on_cond {x. f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub> \<sqsubseteq> x}
          (f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (\<lambda>\<rho>'. \<rho> f++ heapToEnv h (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>))"
  apply (rule fix_on_condI)
  apply (rule subpcpo_cone_above)
  apply (rule bottom_of_cone_above)
  apply (rule closed_onI, simp)
  apply (rule cont_onI)
  apply (rule contE[OF fmap_add_cont2cont[OF cont_const cont2cont_heapToEnv[OF assms]] chain_on_is_chain])
    apply assumption+
  done

subsubsection {* Continuity *}

lemma UHSem_monofun'':
  assumes cont: "\<And> e. e \<in> snd ` set h \<Longrightarrow> cont (ESem e)"
  assumes "\<rho> \<sqsubseteq> \<rho>'"
  shows "\<lbrace>h\<rbrace>\<rho> \<sqsubseteq> \<lbrace>h\<rbrace>\<rho>'"
  apply (subst (1 2) UHSem_def'')
  apply (erule cont)
  apply (rule fix_on_mono2[OF fix_on_cond_UHSem'[OF cont] fix_on_cond_UHSem'[OF cont]])
    apply assumption+
  apply (metis assms(2) below.r_refl fmap_below_dom)
  apply (rule fmap_add_mono[OF `\<rho> \<sqsubseteq> \<rho>'`])
  by (rule cont2monofunE[OF cont2cont_heapToEnv[OF cont]])

lemma UHSem_cont'':
  assumes cont: "\<And> e. e \<in> snd ` set h \<Longrightarrow> cont (ESem e)"
  assumes "chain Y"
  shows "\<lbrace>h\<rbrace>(\<Squnion> i. Y  i) = (\<Squnion> i. \<lbrace>h\<rbrace>(Y i))"
proof-
  have fdoms:"\<And> i. fdom (Y i) = fdom (\<Squnion> i. Y i)" (is "\<And> _ .(_ = ?d)") by (metis chain_fdom `chain Y`) 
  show ?thesis
    apply (subst (1 2) UHSem_def'')
    apply (erule cont)+
    unfolding fdoms
    proof (rule fix_on_cont[OF `chain Y`, where S = "{x . f\<emptyset>\<^bsub>[fdom (\<Squnion> i. Y i) \<union> heapVars h]\<^esub> \<sqsubseteq> x}"])
      show "cont (\<lambda>a b. a f++ heapToEnv h (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>b\<^esub>))"
        by (rule cont2cont_lambda[OF fmap_add_cont1])
      fix i
        from fix_on_cond_UHSem'[OF cont, where \<rho> = "Y i", unfolded fdoms]
        show "fix_on_cond {x. f\<emptyset>\<^bsub>[fdom (\<Squnion> i. Y i) \<union> heapVars h]\<^esub> \<sqsubseteq> x}
               (f\<emptyset>\<^bsub>[fdom (Lub Y) \<union> heapVars h]\<^esub>) (\<lambda>a. Y i f++ heapToEnv h (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>a\<^esub>))"
           by metis
    qed
qed
end

context has_cont_ESem
begin

  lemma UHSem_def':
    shows "\<lbrace>h\<rbrace>\<rho> = fix_on' (f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (\<lambda> \<rho>'. \<rho> f++ heapToEnv h (\<lambda> e. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>))"
    unfolding UHSem_def using ESem_cont by metis

  lemma fix_on_cond_UHSem:
    shows "fix_on_cond {x. f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub> \<sqsubseteq> x}
            (f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (\<lambda>\<rho>'. \<rho> f++ heapToEnv h (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>))"
    apply (rule fix_on_cond_UHSem') using ESem_cont by metis


subsubsection {* Induction and other lemmas about @{term HSem} *}

  lemma UHSem_ind:
    assumes "adm P"
    assumes "P (f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>)"
    assumes step: "\<And> y. fdom y = fdom \<rho> \<union> heapVars h \<Longrightarrow>
          P y \<Longrightarrow>  P (\<rho> f++ (heapToEnv h (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>y\<^esub>)))"
    shows "P (\<lbrace>h\<rbrace>\<rho>)"
    unfolding UHSem_def'
    apply (rule fix_on_ind[OF fix_on_cond_UHSem])
    apply (rule adm_is_adm_on[OF `adm P`])
    apply fact
    apply (rule step)
    apply simp
    apply assumption
    done

  lemma UHSem_below:
    assumes [simp]:"fdom r = fdom \<rho> \<union> heapVars h" 
    assumes rho: "\<And>x. x \<in> fdom \<rho> \<Longrightarrow> x \<notin> heapVars h \<Longrightarrow> \<rho> f! x \<sqsubseteq> r f! x"
    assumes h: "\<And>x. x \<in> heapVars h \<Longrightarrow> \<lbrakk>the (map_of h x)\<rbrakk>\<^bsub>r\<^esub> \<sqsubseteq> r f! x"
    shows "UHSem h \<rho> \<sqsubseteq> r"
  proof (rule UHSem_ind)
    case goal1 show ?case by (auto intro: adm_is_adm_on)
    case goal2 show ?case by (simp add: to_bot_fmap_def)
    case (goal3 \<rho>')
      show ?case
      apply (rule fmap_add_belowI)
      apply simp
      apply (auto intro: below_trans[OF cont2monofunE[OF ESem_cont goal3(2)] h]
                  simp add: lookupHeapToEnv)[1]
      apply (auto intro: rho)
      done
  qed  

  lemma UHSem_fempty_below:
    assumes [simp]:"fdom r = heapVars h" 
    assumes h: "\<And>x. x \<in> heapVars h \<Longrightarrow> \<lbrakk>the (map_of h x)\<rbrakk>\<^bsub>r\<^esub> \<sqsubseteq> r f! x"
    shows "\<lbrace>h\<rbrace>f\<emptyset> \<sqsubseteq> r"
    using assms 
    by (metis UHSem_below fdomIff lookup_fempty subsetI sup.order_iff sup_commute)

  lemma parallel_UHSem_ind:
    assumes "adm (\<lambda>\<rho>'. P (fst \<rho>') (snd \<rho>'))"
    assumes "P (f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (f\<emptyset>\<^bsub>[fdom \<rho>2 \<union> heapVars h2]\<^esub>)"
    assumes step: "\<And>y z. fdom y = fdom \<rho> \<union> heapVars h \<Longrightarrow>
            fdom z = fdom \<rho>2 \<union> heapVars h2 \<Longrightarrow>
            P y z \<Longrightarrow>
            P (\<rho> f++ (heapToEnv h (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>y\<^esub>))) (\<rho>2 f++ (heapToEnv h2 (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>z\<^esub>)))"
    shows "P (\<lbrace>h\<rbrace>\<rho>) (\<lbrace>h2\<rbrace>\<rho>2)"
    unfolding UHSem_def'
    apply (rule parallel_fix_on_ind[OF fix_on_cond_UHSem fix_on_cond_UHSem])
    apply (rule adm_is_adm_on[OF `adm _`])
    apply fact
    apply (rule step)
    apply simp+
    done
  
  lemma UHSem_eq:
    shows "\<lbrace>h\<rbrace>\<rho> = \<rho> f++ (heapToEnv h (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>h\<rbrace>\<rho>\<^esub>))"
    unfolding UHSem_def'
    by (rule fix_on_eq[OF fix_on_cond_UHSem])  
  
  lemma the_lookup_UHSem_other:
    assumes "y \<notin> heapVars h"
    shows "(\<lbrace>h\<rbrace>\<rho>) f! y = \<rho> f! y"
    apply (subst UHSem_eq)
    using assms by simp

  lemma fmap_lookup_bot_UHSem_other:
    assumes "y \<notin> heapVars h"
    shows "(\<lbrace>h\<rbrace>\<rho>) f!\<^sub>\<bottom> y = \<rho> f!\<^sub>\<bottom> y"
    using assms
    by (subst UHSem_eq, cases "y \<in> fdom \<rho>", auto)
  
  lemma the_lookup_UHSem_heap:
    assumes "y \<in> heapVars h"
    shows "(\<lbrace>h\<rbrace>\<rho>) f! y = \<lbrakk> the (map_of h y) \<rbrakk>\<^bsub>\<lbrace>h\<rbrace>\<rho>\<^esub>"
    apply (subst UHSem_eq)
    using assms by (simp add: lookupHeapToEnv)

  lemma fdom_UHSem[simp]:
    "fdom (\<lbrace>h\<rbrace>\<rho>) = fdom \<rho> \<union> heapVars h"
    by (subst UHSem_eq, simp)

  lemma fmap_restr_fmap_addI:"finite S \<Longrightarrow> fdom \<rho>1 - fdom \<rho>2 \<subseteq> S \<Longrightarrow> fmap_restr S \<rho>1 f++ \<rho>2 = \<rho>1 f++ \<rho>2"
    apply (rule fmap_eqI)
    apply auto[1]
    apply auto
    by (metis lookup_fmap_add1 lookup_fmap_add2 lookup_fmap_restr)

  lemma UHSem_restr:
    "\<lbrace>h\<rbrace>(fmap_restr (fdom \<rho> - heapVars h) \<rho>) = \<lbrace>h\<rbrace>\<rho>"
    apply (rule parallel_UHSem_ind)
    apply simp
    apply auto
    apply (subst fmap_restr_fmap_addI)
    apply simp_all
    done
  
  lemma UHSem_reorder:
    assumes "map_of \<Gamma> = map_of \<Delta>"
    shows "\<lbrace>\<Gamma>\<rbrace>\<rho> = \<lbrace>\<Delta>\<rbrace>\<rho>"
  by (simp add: UHSem_def' heapToEnv_reorder[OF assms] assms dom_map_of_conv_heapVars[symmetric])
  
  lemma UHSem_reorder_head:
    assumes "x \<noteq> y"
    shows "\<lbrace>(x,e1)#(y,e2)#\<Gamma>\<rbrace>\<rho> = \<lbrace>(y,e2)#(x,e1)#\<Gamma>\<rbrace>\<rho>"
  proof-
    have "set ((x,e1)#(y,e2)#\<Gamma>) = set ((y,e2)#(x,e1)#\<Gamma>)"
      by auto
    thus ?thesis      
      unfolding UHSem_def heapToEnv_reorder_head[OF assms]
      by (simp add: heapVars_def)
  qed
  
  lemma UHSem_reorder_head_append:
    assumes "x \<notin> heapVars \<Gamma>"
    shows "\<lbrace>(x,e)#\<Gamma>@\<Delta>\<rbrace>\<rho> = \<lbrace>\<Gamma> @ ((x,e)#\<Delta>)\<rbrace>\<rho>"
  proof-
    have "set ((x,e)#\<Gamma>@\<Delta>) = set (\<Gamma> @ ((x,e)#\<Delta>))" by auto
    thus ?thesis
      unfolding UHSem_def  heapToEnv_reorder_head_append[OF assms]
      by simp
  qed  
    
  lemma fmap_restr_UHSem_noop:
    assumes "heapVars \<Gamma> \<inter> fdom \<rho> = {}"
    shows "fmap_restr (fdom \<rho>) (\<lbrace>\<Gamma>\<rbrace>\<rho>) = \<rho>"
    apply (rule fmap_eqI)
    using assms apply auto[1]
    using assms apply auto[1]
    apply (subst the_lookup_UHSem_other)
    apply auto
    done
  
  lemma UHSem_disjoint_less:
    assumes "heapVars \<Gamma> \<inter> fdom \<rho> = {}"
    shows "\<rho> \<le> \<lbrace>\<Gamma>\<rbrace>\<rho>"
    using assms
  by (metis fmap_less_restrict fmap_restr_UHSem_noop)

  lemma UHSem_Nil[simp]: "\<lbrace>[]\<rbrace>\<rho> = \<rho>"
    by (subst UHSem_eq, simp)

  lemma UHSem_mono:
    assumes "\<rho>1 \<sqsubseteq> \<rho>2"
    shows "\<lbrace>\<Gamma>\<rbrace>\<rho>1 \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<rho>2"
    by(rule UHSem_monofun''[OF ESem_cont assms])

subsubsection {* Re-calculating the semantics of the heap is idempotent *} 

  lemma map_add_heapVars[simp]: 
    "x \<in> heapVars \<Gamma> \<Longrightarrow> (map_of \<Delta> ++ map_of \<Gamma>) x = map_of \<Gamma> x"
    "x \<notin> heapVars \<Gamma> \<Longrightarrow> (map_of \<Delta> ++ map_of \<Gamma>) x = map_of \<Delta> x"
      apply (metis dom_map_of_conv_heapVars map_add_dom_app_simps(1))
      apply (metis dom_map_of_conv_heapVars map_add_dom_app_simps(3))
      done

  lemma UHSem_redo:
    shows "\<lbrace>\<Gamma>\<rbrace>(\<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>) f|` (fdom \<rho> \<union> heapVars \<Delta>) = \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>" (is "?LHS = ?RHS")
  proof (rule below_antisym)
    show "?LHS \<sqsubseteq> ?RHS"
    by (rule UHSem_below) (auto simp add: the_lookup_UHSem_heap)
    
  
    show "?RHS \<sqsubseteq> ?LHS"
    proof(rule UHSem_below)
    case goal1 show ?case by auto
    next
    case goal2
      thus ?case by (auto simp add: the_lookup_UHSem_other)
    next
    case (goal3 x)
      thus ?case
      proof(cases "x \<in> heapVars \<Gamma>")
      case True
        thus ?thesis by (auto simp add: the_lookup_UHSem_heap)
      next
      case False
        hence delta: "x \<in> heapVars \<Delta>" using goal3 by auto
        with False
        show ?thesis
          apply (auto simp add: the_lookup_UHSem_other the_lookup_UHSem_heap)
          apply (rule cont2monofunE[OF ESem_cont `?LHS \<sqsubseteq> ?RHS`])
          done
      qed
    qed
  qed


subsubsection {* Iterative definition of the heap semantics *}

  lemma iterative_UHSem:
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
      by (simp_all add: ESem_cont)

    have "\<lbrace>(x,e) # \<Gamma>\<rbrace>\<rho> = fix_on' b L"
      by (simp add: UHSem_def' fmap_add_upd)
    also have "\<dots> = fix_on' b R"
      by (rule iterative_fmap_add)
    also have "\<dots> = fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars \<Gamma>)]\<^esub>)
            (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>\<rho>'))( x f\<mapsto> \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>))"
      by (rule fix_on_cong[OF condR], simp add: UHSem_def')
    finally show ?thesis.
  qed

  lemma iterative_UHSem'_cond:
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
      by (simp_all add: ESem_cont)

    show ?thesis
      by (rule fix_on_cond_cong[OF condR'], simp add: UHSem_def')
  qed

  lemma iterative_UHSem':
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
      by (simp_all add: ESem_cont)

    have "fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars \<Gamma>)]\<^esub>)
            (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>\<rho>'))( x f\<mapsto> \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>)) =
          fix_on' b R"
      by (rule fix_on_cong[symmetric, OF condR], simp add: UHSem_def')
    also have "\<dots> = fix_on' b L"
      by (rule iterative_fmap_add[symmetric])
    also have "\<dots> = fix_on' b R'"
      by (rule iterative_fmap_add')
    also have "\<dots> = fix_on' (f\<emptyset>\<^bsub>[insert x (fdom \<rho> \<union> heapVars \<Gamma>)]\<^esub>)
            (\<lambda> \<rho>'. (\<rho> f++ fmap_restr (heapVars \<Gamma>) (\<lbrace>\<Gamma>\<rbrace>\<rho>'))( x f\<mapsto> \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>'\<^esub>))"
      by (rule fix_on_cong[OF condR'], simp add: UHSem_def')
    finally
    show ?thesis.
  qed

end

lemma UHSem_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> ESem1 e = ESem2 e); env1 = env2 ; heap1 = heap2  \<rbrakk>
      \<Longrightarrow> has_ESem.UHSem ESem1 heap1 env1 = has_ESem.UHSem  ESem2 heap2 env2"
  unfolding has_ESem.UHSem_def
  by (auto cong:heapToEnv_cong)

subsubsection {* Equivariance *}

lemma UHSem_eqvt[eqvt]:
  "\<pi> \<bullet> has_ESem.UHSem ESem h \<rho> = has_ESem.UHSem (\<pi> \<bullet> ESem) (\<pi> \<bullet> h) (\<pi> \<bullet> \<rho>)"
proof(cases "\<forall> e \<in> snd ` set h.  cont (ESem e)")
case True
  from permute_boolI[OF this, where p = \<pi>]
  have True_permuted: "\<forall> e \<in> snd ` set (\<pi> \<bullet> h). cont ((\<pi> \<bullet> ESem) e)"
    by perm_simp

  show ?thesis          
   unfolding has_ESem.UHSem_def if_P[OF True]  if_P[OF True_permuted] 
   apply (subst fix_on_eqvt[OF has_ESem.fix_on_cond_UHSem'])
   apply (metis True)
   apply perm_simp
   apply rule
   done
next
case False 
  from permute_boolI[OF this, where p = \<pi>]
  have False_permuted: "\<not> (\<forall> e \<in> snd ` set (\<pi> \<bullet> h). cont ((\<pi> \<bullet> ESem) e))"
    by perm_simp
  show ?thesis
   unfolding has_ESem.UHSem_def if_not_P[OF False]  if_not_P[OF False_permuted] 
   apply perm_simp
   apply rule
   done
qed

locale has_ignore_fresh_ESem = has_cont_ESem +
  assumes ESem_ignores_fresh: "\<rho>1 \<le> \<rho>2 \<Longrightarrow> atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* e \<Longrightarrow> ESem e \<rho>1 = ESem e \<rho>2"
begin

subsubsection {* Adding a fresh variable to a heap does not affect its semantics *} 

  lemma HSem_add_fresh':
    assumes fresh: "atom x \<sharp> (\<rho>,\<Gamma>)"
    assumes step: "\<And>e \<rho>'. fdom \<rho>' = fdom \<rho> \<union> heapVars ((x, e) # \<Gamma>) \<Longrightarrow> e \<in> snd ` set \<Gamma> \<Longrightarrow> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>' f|` (fdom \<rho>' - {x})\<^esub>"
    shows  "(\<lbrace>(x, e) # \<Gamma>\<rbrace>\<rho>) f|` (fdom \<rho> \<union> heapVars \<Gamma>) = \<lbrace>\<Gamma>\<rbrace>\<rho>"
  proof (rule parallel_UHSem_ind)
  case goal1 show ?case by simp
  case goal2 show ?case by auto
  case (goal3 y z)
    have "fmap_restr (fdom \<rho> \<union> heapVars \<Gamma>) \<rho> = \<rho>" by auto
    moreover
  
    have "x \<notin> fdom \<rho> \<union> heapVars \<Gamma>"
      using fresh
      apply (auto simp add: sharp_Env fresh_Pair)
      by (metis heapVars_not_fresh)
    hence "fdom y - {x} = fdom \<rho> \<union> heapVars \<Gamma>"
      using goal3(1) by auto
    hence [simp]: "z = y f|` (fdom y - {x})" using `_ = z` by auto

    have "heapToEnv ((x, e) # \<Gamma>) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>y\<^esub>) f|` (fdom \<rho> \<union> heapVars \<Gamma>) = heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>y\<^esub>)"
      using `x \<notin> fdom \<rho> \<union> heapVars \<Gamma>` by auto
    moreover
    have "heapToEnv \<Gamma> (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>y\<^esub>) = heapToEnv \<Gamma> (\<lambda>e. ESem e z)"
      apply (rule heapToEnv_cong[OF refl])
      apply (subst (1) step)
      using goal3(1) apply auto
      done
    ultimately
    show ?case by (simp only: fmap_restr_add)
  qed

  lemma UHSem_add_fresh:
    assumes fresh: "atom x \<sharp> (\<rho>, \<Gamma>)"
    shows  "(\<lbrace>(x, e) # \<Gamma>\<rbrace>\<rho>) f|` (fdom \<rho> \<union> heapVars \<Gamma>) = \<lbrace>\<Gamma>\<rbrace>\<rho>"
  proof(rule HSem_add_fresh'[OF assms])
  case (goal1 e \<rho>')
    assume "e \<in> snd ` set \<Gamma>"
    hence "atom x \<sharp> e"
      apply auto
      by (metis fresh fresh_PairD(2) fresh_list_elem)
  
    assume "fdom \<rho>' = fdom \<rho> \<union> heapVars ((x, e) # \<Gamma>)"
    hence [simp]:"fdom \<rho>' - fdom \<rho>' \<inter> (fdom \<rho>' - {x}) = {x}" by auto
  
    show ?case
      apply (rule ESem_ignores_fresh[symmetric, OF fmap_restr_less])
      apply (simp add: fresh_star_def)
      using `atom x \<sharp> e`.
  qed

  lemma UHSem_append_fresh:
    assumes fresh: "atom ` heapVars \<Gamma> \<sharp>* (\<Delta>, \<rho>)"
    shows  "(\<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>) f|` (fdom \<rho> \<union> heapVars \<Delta>) = \<lbrace>\<Delta>\<rbrace>\<rho>"
  proof-
    have [simp]: "\<And> f . heapToEnv (\<Gamma> @ \<Delta>) f f|` (fdom \<rho> \<union> heapVars \<Delta>) = heapToEnv \<Delta> f"
      apply rule
      using assms
      apply (auto simp add: heapVars_not_fresh  fresh_star_def fresh_Pair lookupHeapToEnv)
      apply (metis fresh_fdom map_add_heapVars(2))
      apply (metis heapVars_not_fresh map_add_heapVars(2))
      done
    show ?thesis using assms
      apply (induction rule: parallel_UHSem_ind)
      apply simp
      apply auto
      apply (auto simp add: fmap_restr_add fmap_restr_useless)
      apply (rule arg_cong) back
      apply (rule heapToEnv_cong)
      apply simp
      apply (rule ESem_ignores_fresh[symmetric, OF fmap_restr_less])
      apply (auto simp add: fresh_star_def fresh_Pair fresh_heap_expr)
      done
   qed  
  

subsubsection {* Binding more variables increases knowledge *}

  lemma UHSem_subset_below:
    assumes fresh: "atom ` heapVars \<Gamma> \<sharp>* (\<Delta>, \<rho>)" 
    shows "(\<lbrace>\<Delta>\<rbrace>\<rho>)\<^bsub>[fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma>]\<^esub> \<sqsubseteq> \<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho>"
  proof-
    have fdoms: "fdom \<rho> \<union> (heapVars \<Delta> \<union> heapVars \<Gamma>) - (fdom \<rho> \<union> heapVars \<Delta>) = heapVars \<Gamma>"
      using fresh by (auto dest: fresh_heapVars_distinct simp add: sharp_star_Env' fresh_star_Pair)

    have *: "\<And> x. x \<in> fdom \<rho> \<Longrightarrow> x \<notin> heapVars \<Gamma>"
      using fresh by (auto simp add: sharp_star_Env' fresh_star_Pair)
    
    have below: "\<lbrace>\<Delta>\<rbrace>\<rho> \<sqsubseteq> (\<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho>)\<^bsub>[fdom \<rho> \<union> heapVars \<Delta>]\<^esub>" (is "_ \<sqsubseteq> ?RHS")
    apply (rule UHSem_below)
    apply (auto simp add: the_lookup_UHSem_other the_lookup_UHSem_heap *)
    apply (subst ESem_ignores_fresh)
    prefer 3
    apply (rule below_refl)
    apply auto[1]
    apply (simp add: fdoms)
    apply (metis fresh fresh_Pair fresh_map_of fresh_star_def)
    done

    show ?thesis
    proof(rule fmap_expand_belowI)
    case (goal2 x) 
      with fmap_belowE[OF below, where x = x]
      show ?case by (cases "x\<in> fdom \<rho>", auto)
    qed auto
  qed

  subsubsection {* Additional, fresh bindings in one or two steps *}  

  lemma UHSem_merge:
    assumes fresh: "atom ` heapVars \<Gamma> \<sharp>* (\<Delta>, \<rho>)"
    shows "\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> = \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
  proof(rule below_antisym)
    from fresh
    have Gamma_fresh: "heapVars \<Gamma> \<inter> (fdom \<rho> \<union> heapVars \<Delta>) = {}"
      by (auto dest: fresh_heapVars_distinct simp add: sharp_star_Env' fresh_star_Pair)
    hence fdoms: "fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma> - (fdom \<rho> \<union> heapVars \<Delta>) = heapVars \<Gamma>"
      by auto

    have map_of_eq: "map_of (\<Delta> @ \<Gamma>) = map_of (\<Gamma> @ \<Delta>)"
    proof
      fix x
      show "map_of (\<Delta> @ \<Gamma>) x = map_of (\<Gamma> @ \<Delta>) x"
      proof (cases "x \<in> heapVars \<Gamma>")
        case True
        hence "x \<notin> heapVars \<Delta>" by (metis Gamma_fresh IntI equals0D in_mono sup_ge2)
        thus "map_of (\<Delta> @ \<Gamma>) x = map_of (\<Gamma> @ \<Delta>) x"
          by (simp add: map_add_dom_app_simps dom_map_of_conv_heapVars)
      next
        case False
        thus "map_of (\<Delta> @ \<Gamma>) x = map_of (\<Gamma> @ \<Delta>) x"
          by (simp add: map_add_dom_app_simps dom_map_of_conv_heapVars)
      qed
    qed

    show "\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
    proof(rule UHSem_below)
      fix x
      assume "x \<in> fdom (\<lbrace>\<Delta>\<rbrace>\<rho>)" and "x \<notin> heapVars \<Gamma>"
      hence "\<lbrace>\<Delta>\<rbrace>\<rho> f! x = (\<lbrace>\<Delta>\<rbrace>\<rho>)\<^bsub>[fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma>]\<^esub> f! x" by simp
      also have "\<dots> \<sqsubseteq> \<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho> f! x"
        by (rule fmap_belowE[OF UHSem_subset_below[OF fresh]])
      also have "\<dots> = \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>  f! x"
        by (rule arg_cong[OF UHSem_reorder[OF map_of_eq]])
      finally
      show "\<lbrace>\<Delta>\<rbrace>\<rho> f! x \<sqsubseteq> \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho> f! x".
    qed (auto simp add: the_lookup_UHSem_heap)

     have *: "\<And> x. x \<in> heapVars \<Delta> \<Longrightarrow> x \<notin> heapVars \<Gamma>"
      using fresh by (auto simp add: fresh_Pair fresh_star_def heapVars_not_fresh)

    { fix x
      assume "x \<in> heapVars \<Delta>"
      have "\<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> = \<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
        apply (rule ESem_ignores_fresh[symmetric])
        apply (rule UHSem_disjoint_less) apply (metis Gamma_fresh  fdom_UHSem)
        apply (simp add: fdoms)
            using fresh apply (metis fresh fresh_PairD(1) fresh_heap_expr'[OF _ the_map_of_snd[OF `x \<in> heapVars \<Delta>`]] fresh_star_def)
        done
    }
    thus "\<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>"
      by -(rule UHSem_below, auto simp add: the_lookup_UHSem_other the_lookup_UHSem_heap *)
  qed

  subsubsection {* The semantics of let only adds new bindings *}
  
  lemma UHSem_less:
    assumes fresh: "atom ` heapVars \<Gamma> \<sharp>* (\<Delta>, \<rho>)"
    shows "\<lbrace>\<Delta>\<rbrace>\<rho> \<le> \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
  proof-
    have "heapVars \<Gamma> \<inter> fdom (\<lbrace>\<Delta>\<rbrace>\<rho>) = {}"
      using fresh
      by (auto dest: fresh_heapVars_distinct simp add: sharp_star_Env' fresh_star_Pair)
    hence "\<lbrace>\<Delta>\<rbrace>\<rho> \<le> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>"
      by (rule UHSem_disjoint_less)
    also have "\<dots> =  \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
      by (rule UHSem_merge[OF assms])
    finally
    show ?thesis.
  qed

subsubsection {* Substitution *}

  lemma UHSem_subst_exp:
    assumes "\<And>\<rho>'. fdom \<rho>' = fdom \<rho> \<union> (heapVars ((x,e)#\<Gamma>)) \<Longrightarrow> ESem e \<rho>' = ESem e' \<rho>'"
    shows "\<lbrace>(x, e) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>"
    by (rule parallel_UHSem_ind) (auto simp add: assms heapToEnv_subst_exp)

  lemma UHSem_subst_expr_below:
    assumes below: "\<lbrakk> e1 \<rbrakk>\<^bsub>\<lbrace>(x, e2) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> e2 \<rbrakk>\<^bsub>\<lbrace>(x, e2) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    shows "\<lbrace>(x, e1) # \<Gamma>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>(x, e2) # \<Gamma>\<rbrace>\<rho>"
  proof (rule UHSem_ind) back
  case goal1 show ?case by auto
  case goal2 show ?case by (simp add: to_bot_fmap_def)
  case (goal3 \<rho>')
    show ?case
      apply (subst UHSem_eq)
      apply (rule fmap_add_mono[OF below_refl])
      apply simp
      apply (rule fmap_upd_mono)
      apply (rule cont2monofunE[OF cont2cont_heapToEnv[OF ESem_cont] goal3(2)])
      apply (rule below_trans[OF cont2monofunE[OF ESem_cont goal3(2)] below])
      done
  qed
  
  lemma UHSem_subst_expr:
    assumes below1: "\<lbrakk> e1 \<rbrakk>\<^bsub>\<lbrace>(x, e2) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> e2 \<rbrakk>\<^bsub>\<lbrace>(x, e2) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    assumes below2: "\<lbrakk> e2 \<rbrakk>\<^bsub>\<lbrace>(x, e1) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> e1 \<rbrakk>\<^bsub>\<lbrace>(x, e1) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    shows "\<lbrace>(x, e1) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, e2) # \<Gamma>\<rbrace>\<rho>"
    by (metis assms UHSem_subst_expr_below below_antisym)

end

lemma parallel_UHSem_ind_different_ESem:
  assumes cont1: "\<And>x. cont (ESem1 x)"
  assumes cont2: "\<And>x. cont (ESem2 x)"
  assumes "adm (\<lambda>\<rho>'. P (fst \<rho>') (snd \<rho>'))"
  assumes "P (f\<emptyset>\<^bsub>[fdom \<rho> \<union> heapVars h]\<^esub>) (f\<emptyset>\<^bsub>[fdom \<rho>2 \<union> heapVars h2]\<^esub>)"
  assumes "\<And>y z. P y z \<Longrightarrow> P (\<rho> f++ heapToEnv h (\<lambda>e. ESem1 e y)) (\<rho>2 f++ heapToEnv h2 (\<lambda>e. ESem2 e z))"
  shows "P (has_ESem.UHSem ESem1 h \<rho>) (has_ESem.UHSem ESem2 h2 \<rho>2)"
proof-
  interpret HSem1: has_cont_ESem ESem1 apply default using cont1.
  interpret HSem2: has_cont_ESem ESem2 apply default using cont2.

  show ?thesis
    unfolding HSem1.UHSem_def' HSem2.UHSem_def'
    apply (rule parallel_fix_on_ind[OF HSem1.fix_on_cond_UHSem HSem2.fix_on_cond_UHSem])
    apply (rule adm_is_adm_on[OF assms(3)])
    apply (rule assms(4))
    apply (erule assms(5))
    done
qed


end
