theory HSemUpd
  imports "HeapToEnv" "DistinctVars-Nominal"  "HOLCF-Fix-Join-Nominal" "FMap-Utils" "HasESem"
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
end
