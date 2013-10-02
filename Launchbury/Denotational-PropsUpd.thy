theory "Denotational-PropsUpd"
  imports "DenotationalUpd"
begin

subsubsection {* Continuity of the semantics *}

lemma ESem_cont':"Y0 = Y 0 \<Longrightarrow> chain Y \<Longrightarrow> range (\<lambda>i. \<lbrakk> e \<rbrakk>\<^bsub>Y i\<^esub>) <<| \<lbrakk> e \<rbrakk>\<^bsub>(\<Squnion> i. Y i)\<^esub> " and
  "\<And>e. e \<in> snd ` set (asToHeap as) \<Longrightarrow> cont (ESem e)"
proof(nominal_induct e and as avoiding: Y0  arbitrary: Y rule:exp_assn.strong_induct)
case (Lam x e Y0 Y)
  have [simp]: "\<And> i. fdom (Y i) = fdom (Lub Y)"
    by (metis chain_fdom `chain Y`)
  have [simp]:"\<And> i. atom x \<sharp> Y i" and [simp]:"atom x \<sharp> Lub Y"  using Lam.hyps(1) Lam.prems(1)
    unfolding sharp_Env by auto
  have "cont (ESem e)" using Lam.hyps(2) by (rule contI, auto)
  have  "cont (\<lambda> \<rho>. Fn\<cdot>(\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>))"
    by (intro cont2cont cont_compose[OF `cont (ESem e)`])
  from contE[OF this, OF Lam.prems(2)]
  show ?case
    by simp
next
case (App e v Y0 Y)
  have "cont (ESem e)" using App.hyps(1) by (rule contI, auto)
  thus ?case
    by (auto intro:contE[OF _ App.prems(2)])
next
case (Var v Y0 Y)
  have "cont (\<lambda> \<rho>. ESem (Var v) \<rho>)" by auto
  thus ?case
    by (rule contE[OF _ Var.prems(2)])    
next
case (Let as e Y0 Y)
  have fdoms[simp]: "\<And> i. fdom (Y i) = fdom (Lub Y)"
    by (metis chain_fdom `chain Y`)
  have [simp]:"\<And> i. set (bn as) \<sharp>* Y i" and [simp]: "set (bn as) \<sharp>* Lub Y"  using Let.hyps(1) Let.prems(1)
    unfolding sharp_star_Env by auto
  have unset: "\<And>i. fdom (Y i) \<inter> (heapVars (asToHeap as)) = {}"
    using Let by (metis fdoms disjoint_iff_not_equal sharp_star_Env)
  have conts: "\<forall>e\<in>snd ` set (asToHeap as). cont (ESem e)" using Let.hyps(2) by metis
  have "cont (ESem e)" using Let.hyps(3) by (rule contI, auto)

  have chain: "chain (\<lambda>i. HSem (asToHeap as) (Y i))"
    apply (rule chainI)
    apply (rule HSem_monofun''[OF Let.hyps(2)  chainE[OF `chain Y`]])
    by assumption

  have "(\<Squnion> i. HSem (asToHeap as) (Y i)) = HSem (asToHeap as) (Lub Y)"
    apply (rule HSem_cont''[OF Let.hyps(2) `chain Y`, symmetric])
    by assumption
  thus ?case
    apply simp
    by (metis Let(3) chain)
next
case ANil thus ?case by auto
next
case (ACons v e as Y0 Y)
  have "cont (ESem e)" using ACons.hyps(1) by (rule contI, auto)
  with ACons
  show ?case by auto
qed

interpretation has_cont_ESem ESem
  apply default
  using ESem_cont'[OF refl]
  by (rule contI)

lemmas ESem_cont2cont[simp,cont2cont] = cont_compose[OF ESem_cont]

abbreviation HSem_syn ("\<lbrace>_\<rbrace>_"  [60,60] 60) where "\<lbrace>\<Gamma>\<rbrace>\<rho> \<equiv> HSem \<Gamma> \<rho>"

abbreviation HSem_fempty  ("\<lbrace>_\<rbrace>"  [60] 60) where "\<lbrace>\<Gamma>\<rbrace> \<equiv> \<lbrace>\<Gamma>\<rbrace>fempty"

subsubsection {* The semantics ignores fresh variables *}

lemma ESem_ignores_fresh:
  "\<rho>1 \<le> \<rho>2 \<Longrightarrow> atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* e \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^bsub>\<rho>1\<^esub> = \<lbrakk>e\<rbrakk>\<^bsub>\<rho>2\<^esub>"
  and
  "\<rho>1 \<le> \<rho>2 \<Longrightarrow> atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* as \<Longrightarrow> heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>1\<^esub>) = heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>2\<^esub>)"
proof (nominal_induct e and as avoiding: \<rho>1 \<rho>2 rule:exp_assn.strong_induct)
case (Var x \<rho>1 \<rho>2)
  show ?case
  proof(cases "x \<in> fdom \<rho>1")
  case True
    with `\<rho>1 \<le> \<rho>2`
    have "x \<in> fdom \<rho>2" by (metis (full_types) fmap_less_fdom set_mp)
    with True
    show ?thesis
      by (simp add: fmap_less_eqD[OF `\<rho>1 \<le> \<rho>2` True])
  next
  case False
    with Var(2)
    have "x \<notin> fdom \<rho>2" by (metis Diff_iff exp_assn.fresh(1) fresh_star_def imageI not_self_fresh)
    with False
    show ?thesis
      by (auto simp add: lookup_not_fdom)
  qed
next
case (App e x \<rho>1 \<rho>2)
  from App(3)
  have "atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* e"
    by (auto simp add: fresh_star_def)
  note hyps = App.hyps[OF App.prems(1) this]
  moreover
  have "\<rho>1 f!\<^sub>\<bottom> x = \<rho>2 f!\<^sub>\<bottom> x"
  proof(cases "x \<in> fdom \<rho>1")
  case True
    with `\<rho>1 \<le> \<rho>2`
    have "x \<in> fdom \<rho>2" by (metis (full_types) fmap_less_fdom set_mp)
    with True
    show ?thesis
      by (simp add: fmap_less_eqD[OF `\<rho>1 \<le> \<rho>2` True])
  next
  case False
    with App(3)
    have "x \<notin> fdom \<rho>2"
      by (metis Diff_iff exp_assn.fresh(2) fresh_star_def imageI not_self_fresh)
    with False
    show ?thesis
      by (auto simp add: lookup_not_fdom)
  qed
  ultimately
  show ?case
    by simp
next
case (Let as e \<rho>1 \<rho>2)
  have "fdom \<rho>1 \<subseteq> fdom \<rho>2" by (metis Let(5) fmap_less_fdom)

  have "\<lbrace>asToHeap as\<rbrace>\<rho>1 \<le> \<lbrace>asToHeap as\<rbrace>\<rho>2"
  proof (rule parallel_HSem_ind)
  case goal1 show ?case by simp
  case goal2
    show ?case
      apply (rule fmap_bottom_less)
      using `fdom \<rho>1 \<subseteq> fdom \<rho>2` by auto
  case (goal3 \<rho>1' \<rho>2')[simp]
    have prem: "atom ` (fdom \<rho>2' - fdom \<rho>1') \<sharp>* as"
      using Let(6) Let(1) Let(2)
      by (auto simp add: sharp_star_Env fresh_star_def)

    show "\<rho>1 f++ heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>1'\<^esub>) \<le> \<rho>2 f++ heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>2'\<^esub>) "
    proof(rule fmap_less_eqI)
    case goal1
      show ?case using `fdom \<rho>1 \<subseteq> fdom \<rho>2` by auto
    next
    case (goal2 x)
      thus ?case
      apply (cases "x \<in> heapVars (asToHeap as)")
      apply (simp add: Let(3)[OF goal3(3) prem])
      apply (simp add: fmap_less_eqD[OF `\<rho>1 \<le> \<rho>2`])
      done
    qed
  qed
  moreover
  have "atom ` (fdom (\<lbrace>asToHeap as\<rbrace>\<rho>2) - fdom (\<lbrace>asToHeap as\<rbrace>\<rho>1)) \<sharp>* e "
    using Let(6) Let(1) Let(2)
    by (auto simp add: sharp_star_Env fresh_star_def)
  ultimately
  have "\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>1\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>2\<^esub>"
    apply (rule Let.hyps(4))
    done
  thus "\<lbrakk> Terms.Let as e \<rbrakk>\<^bsub>\<rho>1\<^esub> = \<lbrakk> Terms.Let as e \<rbrakk>\<^bsub>\<rho>2\<^esub>"
    using Let.hyps(1,2) by simp
next
case (Lam x e \<rho>1 \<rho>2)
  { fix v
    have "\<rho>1(x f\<mapsto> v) \<le> \<rho>2(x f\<mapsto> v)"
      apply (rule fmap_less_eqI)
      using fmap_less_fdom[OF Lam(4)] apply auto[1]
      apply (case_tac "xa = x")
      by (auto simp add: fmap_less_eqD[OF `\<rho>1 \<le> \<rho>2`])
    moreover
    have "atom ` (fdom (\<rho>2(x f\<mapsto> v)) - fdom (\<rho>1(x f\<mapsto> v))) \<sharp>* e"
      using Lam(5)
      by (auto simp add: fresh_star_def)
    ultimately
    have "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>1(x f\<mapsto> v)\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>2(x f\<mapsto> v)\<^esub>"
      by (rule Lam(3))
  }
  thus "\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>1\<^esub> = \<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>2\<^esub>"
    using Lam(1,2)
    by simp
next
case ANil
  thus ?case by simp
next
case (ACons x e as \<rho>1 \<rho>2)
  from ACons(4)
  have prem1: "atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* e" and  prem2: "atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* as"
    by (auto simp add: fresh_star_def)
  from ACons.hyps(1)[OF `\<rho>1 \<le> \<rho>2` prem1] ACons.hyps(2)[OF `\<rho>1 \<le> \<rho>2` prem2]
  show ?case by simp
qed

subsubsection {* Denotation of Substitution *}

lemma ESem_subst_same: "\<rho> f!\<^sub>\<bottom> x = \<rho> f!\<^sub>\<bottom> y \<Longrightarrow>  \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<rho>\<^esub>"
  and 
  "\<rho> f!\<^sub>\<bottom> x = \<rho> f!\<^sub>\<bottom> y  \<Longrightarrow>  heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>) = heapToEnv (asToHeap as[x::a=y]) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>) "
proof (nominal_induct e and as  avoiding: \<rho> x y rule:exp_assn.strong_induct)
case (Var var \<rho> x y) thus ?case by auto
next
case (App exp var \<rho> x y)
  from App(1)[OF App(2)] App(2)
  show ?case by auto
next
case (Let as exp \<rho> x y)
  from `set (bn as) \<sharp>* x` `set (bn as) \<sharp>* y` 
  have "x \<notin> heapVars (asToHeap as)" "y \<notin> heapVars (asToHeap as)"
    by (induct as rule: exp_assn.bn_inducts, auto simp add: exp_assn.bn_defs fresh_star_insert)
  hence [simp]:"heapVars (asToHeap (as[x::a=y])) = heapVars (asToHeap as)" 
     by (induct as rule: exp_assn.bn_inducts, auto)

  from `\<rho> f!\<^sub>\<bottom> x = \<rho> f!\<^sub>\<bottom> y`
  have "\<lbrace>asToHeap as\<rbrace>\<rho> f!\<^sub>\<bottom> x = \<lbrace>asToHeap as\<rbrace>\<rho> f!\<^sub>\<bottom> y"
    using `x \<notin> heapVars (asToHeap as)` `y \<notin> heapVars (asToHeap as)`
    by (simp add: fmap_lookup_bot_HSem_other)
  hence "\<lbrakk>exp\<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>\<^esub> = \<lbrakk>exp[x::=y]\<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>\<^esub>"
    by (rule Let)
  moreover
  from `\<rho> f!\<^sub>\<bottom> x = \<rho> f!\<^sub>\<bottom> y` `x \<notin> heapVars (asToHeap as)` `y \<notin> heapVars (asToHeap as)`
  have "\<lbrace>asToHeap as\<rbrace>\<rho> = \<lbrace>asToHeap as[x::a=y]\<rbrace>\<rho>" and "\<lbrace>asToHeap as\<rbrace>\<rho> f!\<^sub>\<bottom> x = \<lbrace>asToHeap as[x::a=y]\<rbrace>\<rho> f!\<^sub>\<bottom> y"
    by (induction rule: parallel_HSem_ind) (auto dest: Let(4))
  ultimately
  show ?case using Let(1-3) by (simp add: fresh_star_Pair)
next
case (Lam var exp \<rho> x y)
  from `\<rho> f!\<^sub>\<bottom> x = \<rho> f!\<^sub>\<bottom> y`
  have "\<And>v. \<rho>(var f\<mapsto> v) f!\<^sub>\<bottom> x = \<rho>(var f\<mapsto> v) f!\<^sub>\<bottom> y"
    using Lam(2,3) by (simp add: fresh_at_base)
  hence "\<And> v. \<lbrakk>exp\<rbrakk>\<^bsub>\<rho>(var f\<mapsto> v)\<^esub> = \<lbrakk>exp[x::=y]\<rbrakk>\<^bsub>\<rho>(var f\<mapsto> v)\<^esub>"
    by (rule Lam)
  thus ?case using Lam(1-3) by simp
next
case (ANil \<rho> x y) thus ?case by auto
next
case (ACons var exp as \<rho> x y)
  from ACons(1,2)[OF ACons(3)] ACons(3)
  show ?case by auto
qed

lemma ESem_subst:
  assumes "x \<noteq> y" (* Can be dropped, but this is sufficient for us *) 
  assumes "atom x \<sharp> \<rho>"
  shows "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> \<lbrakk>Var y\<rbrakk>\<^bsub>\<rho>\<^esub>)\<^esub> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<rho>\<^esub>"
proof-
  from assms have [simp]:"x \<notin> fdom \<rho>" by (simp add: sharp_Env)
  have [simp]:"insert x (fdom \<rho>) - fdom \<rho> = {x}" by auto

  have "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> \<lbrakk>Var y\<rbrakk>\<^bsub>\<rho>\<^esub>)\<^esub> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> \<lbrakk>Var y\<rbrakk>\<^bsub>\<rho>\<^esub>)\<^esub>"
    by (cases "x = y") (auto intro: ESem_subst_same)
  also have "\<dots> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<rho>\<^esub>"
    by (auto intro: ESem_ignores_fresh[symmetric] simp add: fresh_star_singleton assms)
  finally
  show ?thesis.
qed

subsubsection {* Binding more variables increases knowledge *}

lemma HSem_subset_below:
  assumes fresh: "atom ` heapVars \<Gamma> \<sharp>* (\<Delta>, \<rho>)" 
  shows "(\<lbrace>\<Delta>\<rbrace>\<rho>)\<^bsub>[fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma>]\<^esub> \<sqsubseteq> \<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho>"
proof (rule HSem_ind) back
case goal1 show ?case by (auto intro!: adm_is_adm_on adm_subst[OF fmap_expand_cont])
next
case goal2 show ?case by (auto simp add: to_bot_fmap_def)
next
case (goal3 x)
  from fresh
  have "heapVars \<Gamma> \<inter> (fdom \<rho> \<union> heapVars \<Delta>) = {}"
    by (auto dest: fresh_heapVars_distinct simp add: sharp_star_Env' fresh_star_Pair)
  hence fdoms: "fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma> - (fdom \<rho> \<union> heapVars \<Delta>) = heapVars \<Gamma>"
    by auto
  {
    fix v e
    assume "e \<in> snd` set \<Delta>"
    from fresh_star_heap_expr'[OF _ this]
    have fresh_e: "atom ` heapVars \<Gamma> \<sharp>* e"
      by (metis fresh fresh_star_Pair)
    have "\<lbrakk> e \<rbrakk>\<^bsub>x\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>x\<^bsub>[fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma>]\<^esub>\<^esub>"
      apply (rule ESem_ignores_fresh)
      apply (rule less_fmap_expand)
        using `fdom x = _` apply auto[2]
      apply (simp add: `fdom x = _` fdoms)
      apply (rule fresh_e)
      done
    with goal3(2)
    have "\<lbrakk> e \<rbrakk>\<^bsub>x\<^esub> \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho>\<^esub>"
      by (metis cont2monofunE[OF ESem_cont])
  } note e_less = this

  show ?case
  proof (rule fmap_expand_belowI)
  case goal1 show ?case by auto
  case (goal2 y)
    show ?case
    proof (cases "y \<in> heapVars \<Delta>")
    case True
      thus ?thesis
        by (subst HSem_eq, auto intro: e_less[OF the_map_of_snd] simp add: dom_map_of_conv_heapVars lookupHeapToEnv map_add_dom_app_simps)
    next
    case False
      moreover
      with goal2(1) `_ = {}`
      have "y \<notin> heapVars \<Gamma>" by auto
      ultimately
      show ?thesis
        by (subst HSem_eq, simp)
    qed
  qed
qed

subsubsection {* Additional, fresh bindings in one or two steps *}

lemma HSem_merge:
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
  proof(rule HSem_below)
  case goal1 show ?case by (auto simp add: adm_is_adm_on)
  next
  case (goal2 x)
    with fmap_belowE[OF HSem_subset_below[OF fresh], where x = x]
    have "\<lbrace>\<Delta>\<rbrace>\<rho> f! x \<sqsubseteq> \<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho> f! x" by auto
    also have "\<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho> = \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>"
      by (rule HSem_reorder[OF map_of_eq])
    finally show ?case.
  next
  case (goal3 x)
    thus ?case
      by (auto simp add: the_lookup_HSem_heap map_add_dom_app_simps dom_map_of_conv_heapVars)
  qed
  
  show "\<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>"
  proof(rule HSem_below)
  case goal1 show ?case by (auto simp add: adm_is_adm_on)
  next
  case (goal2 x)
    thus ?case by (simp add: the_lookup_HSem_other)
  next
  case (goal3 x)
    {
      assume x: "x \<in> heapVars \<Gamma> "
      hence "the (map_of (\<Gamma>@\<Delta>) x) = the (map_of \<Gamma> x)" by (simp add: map_add_dom_app_simps dom_map_of_conv_image_fst dom_map_of_conv_heapVars[symmetric])
      also
      have "\<lbrakk> the (map_of \<Gamma> x) \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> = \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> f! x"
        by (rule the_lookup_HSem_heap[OF x, symmetric])
      finally have ?case by (rule eq_imp_below)
    } moreover {
      assume "x \<notin> heapVars \<Gamma>"
      hence "\<lbrakk>  the (map_of (\<Gamma>@\<Delta>) x) \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> = \<lbrakk> the (map_of \<Delta> x)  \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>" by (simp add: map_add_dom_app_simps dom_map_of_conv_image_fst dom_map_of_conv_heapVars[symmetric])
      also
      assume x: "x \<in> heapVars \<Delta>"
      hence "\<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> = \<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
        apply -
        apply (rule ESem_ignores_fresh[symmetric])
        apply (rule HSem_disjoint_less)
          using Gamma_fresh apply auto[1]
        using assms apply (simp add: fdoms fresh_star_map_of fresh_star_Pair)
        done
      also have "\<dots> = \<lbrace>\<Delta>\<rbrace>\<rho> f! x"
        by (rule the_lookup_HSem_heap[OF  `x \<in> heapVars \<Delta>`, symmetric])
      also have "\<dots> = \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> f! x"
        by (rule the_lookup_HSem_other[OF `x \<notin> heapVars \<Gamma>`, symmetric])
      finally have ?case by (rule eq_imp_below)
  } ultimately show ?case using goal3 by auto
  qed
qed

subsubsection {* The semantics of let only adds new bindings *}

lemma HSem_less:
  assumes fresh: "atom ` heapVars \<Gamma> \<sharp>* (\<Delta>, \<rho>)"
  shows "\<lbrace>\<Delta>\<rbrace>\<rho> \<le> \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
proof-
  have "heapVars \<Gamma> \<inter> fdom (\<lbrace>\<Delta>\<rbrace>\<rho>) = {}"
    using fresh
    by (auto dest: fresh_heapVars_distinct simp add: sharp_star_Env' fresh_star_Pair)
  hence "\<lbrace>\<Delta>\<rbrace>\<rho> \<le> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>"
    by (rule HSem_disjoint_less)
  also have "\<dots> =  \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
    by (rule HSem_merge[OF assms])
  finally
  show ?thesis.
qed
end
