theory "Denotational-Props"
  imports "Denotational"
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
  have cont: "cont (ESem e)" using Let.hyps(3) by (rule contI, auto)
  have cond: "HSem_cond'' (asToHeap as) (\<Squnion> i. Y i)" by (rule disjoint_is_HSem_cond'[OF unset[unfolded fdoms] conts])
  have conds: "\<And>i. HSem_cond'' (asToHeap as) (Y i)" by (rule disjoint_is_HSem_cond'[OF unset conts])

  have chain: "chain (\<lambda>i. HSem (asToHeap as) (Y i))"
    apply (rule chainI)
    apply (rule HSem_monofun''[OF Let.hyps(2) conds conds chainE[OF `chain Y`]])
    by assumption

  have "(\<Squnion> i. HSem (asToHeap as) (Y i)) = HSem (asToHeap as) (Lub Y)"
    apply (rule HSem_cont''[OF Let.hyps(2) cond conds `chain Y`, symmetric])
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

(* TODO: Where to put this *)
  
lemma fresh_fmap_upd_lookup[simp]: "S \<sharp>* (\<rho>::Env) \<Longrightarrow> S \<sharp>* x \<Longrightarrow> S \<sharp>* \<rho>(x f\<mapsto> \<rho> f!\<^sub>\<bottom> y)"
  by (auto simp add: fresh_append fresh_star_fmap_upd_eq intro: eqvt_fresh_star_cong2[where f = fmap_delete, OF fmap_delete_eqvt])

lemma compatible_insert:
  assumes [simp]: "S = insert x (fdom \<rho>1)"
  and "x \<notin> fdom \<rho>1"
  and "x \<notin> fdom \<rho>2"
  and compat: "compatible \<rho>1 (\<rho>2\<^bsub>[fdom \<rho>1]\<^esub>)"  
  shows "compatible (\<rho>1(x f\<mapsto> y)) (\<rho>2\<^bsub>[S]\<^esub>)"
proof(rule compatible_fmapI)
case (goal1 z)
  show ?case
  apply(cases "z = x")
  using `x \<notin> fdom \<rho>2` apply simp
  using goal1(1) the_lookup_compatible[OF compat, of z]
  apply (cases "z \<in> fdom \<rho>2")
  by auto
next
case goal2 with assms(1) show ?case by simp
qed
    
(* TODO move where? *)

lemma fmap_expand_compatible:
  assumes [simp]: "finite S"
  assumes compat:"compatible \<rho>1 \<rho>2"
  shows "compatible (\<rho>1\<^bsub>[S]\<^esub>) (\<rho>2\<^bsub>[S]\<^esub>)"
  apply (rule compatible_fmapI)
  apply (case_tac "x \<in> fdom \<rho>1")
  apply (auto simp add: fdom_compatible[OF compat] intro: the_lookup_compatible[OF compat])
  done


lemma fmap_expand_join:
  assumes [simp]: "finite S"
  assumes compat:"compatible \<rho>1 \<rho>2"
  shows "(\<rho>1 \<squnion> \<rho>2)\<^bsub>[S]\<^esub> = \<rho>1\<^bsub>[S]\<^esub> \<squnion> \<rho>2\<^bsub>[S]\<^esub>"
proof-
  have [simp]: "fdom \<rho>2 = fdom \<rho>1" by (metis fdom_compatible[OF compat])
  have [simp]: "fdom (\<rho>1 \<squnion> \<rho>2) = fdom \<rho>1" by (rule fdom_join[OF compat])
  have compat2: "compatible (\<rho>1\<^bsub>[S]\<^esub>) (\<rho>2\<^bsub>[S]\<^esub>)"
    by (rule fmap_expand_compatible[OF assms])
  show ?thesis
    apply (rule fmap_eqI)
    apply (simp add: fdom_join[OF compat2])
    apply (case_tac "x \<in> fdom \<rho>1")
    by (auto simp add: the_lookup_join[OF compat2] the_lookup_join[OF compat])
qed

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
    with Var(1)
    have "x \<in> fdom \<rho>2" by (metis (full_types) fmap_less_fdom set_mp)
    with True
    show ?thesis
      by (simp add: fmap_less_eqD[OF `\<rho>1 \<le> \<rho>2` True])
  next
  case False
    have "x \<notin> fdom \<rho>2"
    proof
      assume "x \<in> fdom \<rho>2"
      hence "x \<in> fdom \<rho>2 - fdom \<rho>1" using False by simp
      thus False
        using Var(2)
        apply (simp add: fresh_star_def)
        apply (erule ballE[where x = "x"])
        by auto
    qed
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
    with App(2)
    have "x \<in> fdom \<rho>2" by (metis (full_types) fmap_less_fdom set_mp)
    with True
    show ?thesis
      by (simp add: fmap_less_eqD[OF `\<rho>1 \<le> \<rho>2` True])
  next
  case False
    have "x \<notin> fdom \<rho>2"
    proof
      assume "x \<in> fdom \<rho>2"
      hence "x \<in> fdom \<rho>2 - fdom \<rho>1" using False by simp
      thus False
        using App(3)
        apply (simp add: fresh_star_def)
        apply (erule ballE[where x = "x"])
        by auto
    qed
    with False
    show ?thesis
      by (auto simp add: lookup_not_fdom)
  qed
  ultimately
  show ?case
    by simp
next
case (Let as e \<rho>1 \<rho>2)
  have cond1: "HSem_cond' (asToHeap as) \<rho>1"
      (is "fix_join_cond ?\<rho>1 ?F1")
    apply (rule disjoint_is_HSem_cond)
    using Let(1)
    by (auto simp add: sharp_star_Env)
  have cond2: "HSem_cond' (asToHeap as) \<rho>2"
      (is "fix_join_cond ?\<rho>2 ?F2")
    apply (rule disjoint_is_HSem_cond)
    using Let(2)
    by (auto simp add: sharp_star_Env)

  have "fdom \<rho>1 \<subseteq> fdom \<rho>2" by (metis Let(5) fmap_less_fdom)

  have "\<lbrace>asToHeap as\<rbrace>\<rho>1 \<le> \<lbrace>asToHeap as\<rbrace>\<rho>2"
  proof (rule parallel_HSem_ind[OF cond1 cond2])
  case goal1 show ?case by (rule adm_is_adm_on, simp)
  case goal2
    show ?case
      apply (rule fmap_bottom_less)
      using `fdom \<rho>1 \<subseteq> fdom \<rho>2` apply auto[2]
      done
  case (goal3 \<rho>1' \<rho>2')
    have [simp]:"fdom \<rho>1' = fdom \<rho>1 \<union> heapVars (asToHeap as)" and [simp]:"fdom \<rho>2' = fdom \<rho>2 \<union> heapVars (asToHeap as)"
      using fdom_fix_join_compat[OF fix_on_cond_fjc[OF cond1] goal3(1)]
      using fdom_fix_join_compat[OF fix_on_cond_fjc[OF cond2] goal3(2)]
      by simp+  
    note compat1 = rho_F_compat_fjc[OF cond1 goal3(1)]
    note compat2 = rho_F_compat_fjc[OF cond2 goal3(2)]

    have prem: "atom ` (fdom \<rho>2' - fdom \<rho>1') \<sharp>* as"
      using Let(6) Let(1) Let(2)
      by (auto simp add: sharp_star_Env fresh_star_def)

    show "?\<rho>1 \<squnion> ?F1 \<rho>1' \<le> ?\<rho>2 \<squnion> ?F2 \<rho>2'"
    proof(rule fmap_less_eqI)
    case goal1
      show ?case
        apply (subst fdom_join[OF compat1])
        apply (subst fdom_join[OF compat2])
        using `fdom \<rho>1 \<subseteq> fdom \<rho>2`
        by auto
    next
    case (goal2 x)
      hence dom: "x \<in> fdom \<rho>1 \<union> heapVars (asToHeap as)"      
        apply (subst (asm) fdom_join[OF compat1])
        by simp
      hence dom2: "x \<in> fdom \<rho>2 \<union> heapVars (asToHeap as)"
        by (auto intro: set_mp[OF `fdom \<rho>1 \<subseteq> fdom \<rho>2`])

      have "lookup ?\<rho>1 x = lookup ?\<rho>2 x"
      proof (cases "x \<in> fdom \<rho>1")
      case True
        hence "x \<in> fdom \<rho>2" by (rule set_mp[OF `fdom \<rho>1 \<subseteq> fdom \<rho>2`])
        with True show ?thesis
          by (simp add: fmap_less_eqD[OF `\<rho>1 \<le> \<rho>2` True])
      next
      case False
        hence "x \<notin> fdom \<rho>2"
          using Let(2) dom 
          by (auto simp add: sharp_star_Env)
        with False dom show ?thesis by (simp add: lookup_not_fdom)
      qed
      moreover
      have "lookup (?F1 \<rho>1') x = lookup (?F2 \<rho>2') x"
      proof (cases "x \<in> heapVars (asToHeap as)")
      case True
        thus ?thesis
          by (simp add: Let(3)[OF goal3(3) prem])
      next
      case False
        thus ?thesis
          using dom dom2 by simp
      qed
      ultimately
      show ?case
        apply (subst the_lookup_join[OF compat1])
        apply (subst the_lookup_join[OF compat2])
        by simp
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

lemma HSem_add_fresh:
  assumes cond1: "HSem_cond' \<Gamma> \<rho>"
  assumes cond2: "HSem_cond' ((x,e) # \<Gamma>) \<rho>"
  assumes fresh: "atom x \<sharp> (\<rho>, \<Gamma>)"
  shows  "fmap_restr (fdom \<rho> \<union> heapVars \<Gamma>) (\<lbrace>(x, e) # \<Gamma>\<rbrace>\<rho>) = \<lbrace>\<Gamma>\<rbrace>\<rho>"
proof(rule HSem_add_fresh[OF assms])
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

lemma ESem_add_fresh:
  assumes cond1: "HSem_cond' \<Gamma> \<rho>"
  assumes cond2: "HSem_cond' ((x,e') # \<Gamma>) \<rho>"
  assumes fresh: "atom x \<sharp> (\<rho>, \<Gamma>, e)"
  shows "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
proof(rule ESem_ignores_fresh[symmetric])
  have "\<lbrace>\<Gamma>\<rbrace>\<rho> = fmap_restr (fdom \<rho> \<union> heapVars \<Gamma>) (\<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>) "
    apply (rule HSem_add_fresh[OF assms(1,2), symmetric])
    using fresh by (simp add: fresh_Pair)
  thus "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>"
    by (auto simp add: fmap_less_restrict)

  have "(insert x (fdom \<rho> \<union> heapVars \<Gamma>) - (fdom \<rho> \<union> heapVars \<Gamma>)) = {x}"
    using fresh
    apply (auto simp add: fresh_Pair sharp_Env)
    by (metis heapVars_not_fresh)
  thus "atom ` (fdom (\<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>) - fdom (\<lbrace>\<Gamma>\<rbrace>\<rho>)) \<sharp>* e"
    using fresh
    by (simp add: fresh_star_def fresh_Pair)
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

  have cond1: "HSem_cond' (asToHeap as) \<rho>"
      (is "fix_join_cond ?\<rho>1 ?F1")
    apply (rule disjoint_is_HSem_cond)
    apply (auto simp add:  `x \<notin> heapVars (asToHeap as)`)
    by (metis Let(1) sharp_star_Env)
  have cond2: "HSem_cond' (asToHeap as[x::a=y]) \<rho>"
      (is "fix_join_cond ?\<rho>2 ?F2")
    apply (rule disjoint_is_HSem_cond)
    apply (auto simp add:  `x \<notin> heapVars (asToHeap as)`)
    by (metis Let(1) sharp_star_Env)


  from `\<rho> f!\<^sub>\<bottom> x = \<rho> f!\<^sub>\<bottom> y`
  have "\<lbrace>asToHeap as\<rbrace>\<rho> f!\<^sub>\<bottom> x = \<lbrace>asToHeap as\<rbrace>\<rho> f!\<^sub>\<bottom> y"
    using `x \<notin> heapVars (asToHeap as)` `y \<notin> heapVars (asToHeap as)`
    by (simp add: fmap_lookup_bot_HSem_other)
  hence "\<lbrakk>exp\<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>\<^esub> = \<lbrakk>exp[x::=y]\<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>\<^esub>"
    by (rule Let)
  moreover
  from `\<rho> f!\<^sub>\<bottom> x = \<rho> f!\<^sub>\<bottom> y`
  have "\<lbrace>asToHeap as\<rbrace>\<rho> = \<lbrace>asToHeap as[x::a=y]\<rbrace>\<rho>" and "\<lbrace>asToHeap as\<rbrace>\<rho> f!\<^sub>\<bottom> x = \<lbrace>asToHeap as[x::a=y]\<rbrace>\<rho> f!\<^sub>\<bottom> y"
    apply (induction rule: parallel_HSem_ind[OF cond1 cond2])
    apply (rule adm_is_adm_on, simp)
    apply simp
    apply simp
    apply simp
    apply (erule arg_cong[OF Let(4)])
    apply (subst fmap_lookup_bot_join[OF rho_F_compat_fjc[OF cond1]], assumption)
    apply (subst fmap_lookup_bot_join[OF rho_F_compat_fjc[OF cond2]], assumption)
    using `x \<notin> heapVars (asToHeap as)` `y \<notin> heapVars (asToHeap as)`
    apply simp
    done
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
  assumes "x \<noteq> y"
  assumes "atom x \<sharp> \<rho>"
  shows "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> \<lbrakk>Var y\<rbrakk>\<^bsub>\<rho>\<^esub>)\<^esub> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<rho>\<^esub>"
proof-
  from assms(2) have [simp]:"x \<notin> fdom \<rho>" by (simp add: sharp_Env)
  have [simp]:"insert x (fdom \<rho>) - fdom \<rho> = {x}" by auto

  have "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> \<lbrakk>Var y\<rbrakk>\<^bsub>\<rho>\<^esub>)\<^esub> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> \<lbrakk>Var y\<rbrakk>\<^bsub>\<rho>\<^esub>)\<^esub>"
    using assms(1) by (auto intro: ESem_subst_same)
  also have "\<dots> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<rho>\<^esub>"
    by (auto intro: ESem_ignores_fresh[symmetric] simp add: fresh_star_singleton assms(1))
  finally
  show ?thesis.
qed

subsubsection {* Replacing subexpressions by variables *}

lemma HSem_subst_var_app:
  assumes cond1: "HSem_cond' ((x, App (Var n) y) # (n, e) # \<Gamma>) \<rho>"
  assumes cond2: "HSem_cond' ((x, App e y) # (n, e) # \<Gamma>) \<rho>"
  assumes fresh: "atom n \<sharp> (x,\<rho>)"
  shows "\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho> "
proof(rule HSem_subst_expr[OF cond1 cond2])
  from fresh have [simp]:"n \<notin> fdom \<rho>" "n \<noteq> x" by (simp add: fresh_Pair sharp_Env fresh_at_base)+
  have ne: "(n,e) \<in> set ((x, App e y) # (n, e) # \<Gamma>)" by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho> f! n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    apply (subst HSem_eq[OF cond2])
    apply (subst the_lookup_join[OF rho_F_compat_fjc[OF cond2 HSem_there[OF cond2]]])
    apply simp
    done
  finally
  show "\<lbrakk> App (Var n) y \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> App e y \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp

 have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho> f! n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    apply (subst HSem_eq[OF cond1])
    apply (subst the_lookup_join[OF rho_F_compat_fjc[OF cond1 HSem_there[OF cond1]]])
    apply simp
    done
  finally
  show "\<lbrakk> App e y \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> App (Var n) y \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp
qed

lemma HSem_subst_var_var:
  assumes cond1: "HSem_cond' ((x, Var n) # (n, e) # \<Gamma>) \<rho>"
  assumes cond2: "HSem_cond' ((x, e) # (n, e) # \<Gamma>) \<rho>"
  assumes fresh: "atom n \<sharp> (x,\<rho>)"
  shows "\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho> "
proof(rule HSem_subst_expr[OF cond1 cond2])
  from fresh have [simp]:"n \<notin> fdom \<rho>" "n \<noteq> x" by (simp add: fresh_Pair sharp_Env fresh_at_base)+
  have ne: "(n,e) \<in> set ((x, e) # (n, e) # \<Gamma>)" by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho> f! n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    apply (subst HSem_eq[OF cond2])
    apply (subst the_lookup_join[OF rho_F_compat_fjc[OF cond2 HSem_there[OF cond2]]])
    apply simp
    done
  finally
  show "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho> f! n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    apply (subst HSem_eq[OF cond1])
    apply (subst the_lookup_join[OF rho_F_compat_fjc[OF cond1 HSem_there[OF cond1]]])
    apply simp
    done
  finally
  show "\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp
qed

subsubsection {* Binding more variables increases knowledge *}

lemma HSem_subset_below:
  assumes cond2: "HSem_cond' (\<Delta>@\<Gamma>) \<rho>"
  assumes fresh: "atom ` heapVars \<Gamma> \<sharp>* (\<Delta>, \<rho>)" 
  shows "(\<lbrace>\<Delta>\<rbrace>\<rho>)\<^bsub>[fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma>]\<^esub> \<sqsubseteq> \<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho>"
proof-
  have fdoms: "fdom \<rho> \<union> (heapVars \<Delta> \<union> heapVars \<Gamma>) - (fdom \<rho> \<union> heapVars \<Delta>) = heapVars \<Gamma>"
    using fresh by (auto dest: fresh_heapVars_distinct simp add: sharp_star_Env' fresh_star_Pair)
  
  have below: "\<lbrace>\<Delta>\<rbrace>\<rho> \<sqsubseteq> (\<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho>)\<^bsub>[fdom \<rho> \<union> heapVars \<Delta>]\<^esub>" (is "_ \<sqsubseteq> ?RHS")
  proof (rule HSem_below)
    show "\<rho>\<^bsub>[fdom \<rho> \<union> heapVars \<Delta>]\<^esub> \<sqsubseteq> ?RHS"
    proof (rule fmap_expand_belowI)
      fix x
      assume "x \<in> fdom \<rho>"
      with fmap_belowE[OF HSem_refines[OF cond2], where x = x]
      show "\<rho> f! x \<sqsubseteq> ?RHS f! x" by simp
    qed simp
  next
  case (goal2 x)[simp]
    have "\<lbrakk>the (map_of \<Delta> x)\<rbrakk>\<^bsub>?RHS\<^esub> = \<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>(\<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho>)\<^esub>"
      apply (rule ESem_ignores_fresh[OF fmap_expand_less])
      apply simp
      apply auto[1]
      apply (simp add: fdoms)
      using fresh apply (metis fresh fresh_PairD(1) fresh_heap_expr'[OF _ the_map_of_snd[OF goal2]] fresh_star_def)
      done
    also have "\<dots> = \<lbrakk> the (map_of (\<Delta>@\<Gamma>) x) \<rbrakk>\<^bsub>(\<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho>)\<^esub>"
      by (simp add: map_add_dom_app_simps)
    also have "\<dots> \<sqsubseteq> ?RHS f! x"
      by (simp, rule HSem_heap_below[OF cond2, where x = x, simplified])
    finally
    show ?case.
  qed

  show ?thesis
  proof(rule fmap_expand_belowI)
  case (goal2 x) 
    with fmap_belowE[OF below, where x = x]
    show ?case by (cases "x\<in> fdom \<rho>", auto)
  qed auto
qed

subsubsection {* Additional, fresh bindings in one or two steps *}

lemma HSem_merge:
  assumes distinct1: "distinctVars (\<Delta> @ \<Gamma>)"
  assumes fresh: "atom ` heapVars \<Gamma> \<sharp>* (\<Delta>, \<rho>)"
  assumes rho_fresh: "fdom \<rho> \<inter> heapVars (\<Gamma> @ \<Delta>) = {}"
  shows "\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> = \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
proof(rule below_antisym)
  from distinct1
  have distinct2: "distinctVars (\<Gamma> @ \<Delta>)"
    by (auto simp add: distinctVars_append)

  from fresh
  have Gamma_fresh: "heapVars \<Gamma> \<inter> (fdom \<rho> \<union> heapVars \<Delta>) = {}"
    by (auto dest: fresh_heapVars_distinct simp add: sharp_star_Env' fresh_star_Pair)
  hence fdoms: "fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma> - (fdom \<rho> \<union> heapVars \<Delta>) = heapVars \<Gamma>"
    by auto

  have cond1: "HSem_cond' \<Gamma> (\<lbrace>\<Delta>\<rbrace>\<rho>)"
    apply (rule disjoint_is_HSem_cond)
    using Gamma_fresh by auto
  have cond2: "HSem_cond' (\<Gamma>@\<Delta>) \<rho>"
    apply (rule disjoint_is_HSem_cond)
    using rho_fresh by auto
  have cond2': "HSem_cond' (\<Delta>@\<Gamma>) \<rho>"
    apply (rule disjoint_is_HSem_cond)
    using rho_fresh by auto
  have cond3: "HSem_cond' \<Delta> \<rho>"
    apply (rule disjoint_is_HSem_cond)
    using rho_fresh by auto

  show "\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
  proof(rule HSem_below)
    have "(\<lbrace>\<Delta>\<rbrace>\<rho>)\<^bsub>[fdom \<rho> \<union> heapVars \<Delta> \<union> heapVars \<Gamma>]\<^esub> \<sqsubseteq> \<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho>"
      by (rule HSem_subset_below[OF cond2' fresh])
    also have "\<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho> = \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>"
      by (rule HSem_reorder[OF distinct1 distinct2], auto)
    finally
    show "(\<lbrace>\<Delta>\<rbrace>\<rho>)\<^bsub>[fdom (\<lbrace>\<Delta>\<rbrace>\<rho>) \<union> heapVars \<Gamma>]\<^esub> \<sqsubseteq> \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>"
      by simp
    
  case (goal2 x)[simp]
    have "\<lbrakk>the (map_of \<Gamma> x)\<rbrakk>\<^bsub>\<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>\<^esub> = \<lbrakk>the (map_of (\<Gamma>@\<Delta>) x)\<rbrakk>\<^bsub>\<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>\<^esub>"
      by (simp add: map_add_dom_app_simps)
    also have "\<dots> \<sqsubseteq> \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho> f! x"
      by (rule HSem_heap_below[OF cond2], simp)
    finally
    show ?case.
  qed

  show "\<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>"
  proof(rule HSem_below)
    have "\<rho>\<^bsub>[fdom \<rho> \<union> heapVars (\<Gamma> @ \<Delta>)]\<^esub> = (\<rho>\<^bsub>[fdom \<rho> \<union> heapVars \<Delta>]\<^esub>)\<^bsub>[fdom \<rho> \<union> heapVars (\<Gamma> @ \<Delta>)]\<^esub>"
      by (rule fmap_expand_idem[symmetric], auto)
    also have "... \<sqsubseteq> (\<lbrace>\<Delta>\<rbrace>\<rho>)\<^bsub>[fdom \<rho> \<union> heapVars (\<Gamma> @ \<Delta>)]\<^esub>"
      by (rule cont2monofunE[OF fmap_expand_cont HSem_refines[OF cond3]])
    also have "... = (\<lbrace>\<Delta>\<rbrace>\<rho>)\<^bsub>[fdom (\<lbrace>\<Delta>\<rbrace>\<rho>) \<union> heapVars (\<Gamma>)]\<^esub>"
      apply (rule arg_cong) back
      by auto
    also have "... \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>"
      by (rule HSem_refines[OF cond1])
    finally
    show "\<rho>\<^bsub>[fdom \<rho> \<union> heapVars (\<Gamma> @ \<Delta>)]\<^esub> \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> ".
  
  case (goal2 x)
    {
      assume x[simp]: "x \<in> heapVars \<Gamma>"
      have "\<lbrakk>the (map_of (\<Gamma> @ \<Delta>) x)\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> = \<lbrakk>the (map_of (\<Gamma>) x)\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
        by (simp add: map_add_dom_app_simps)
      also have "\<dots> \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> f! x"
        by (rule HSem_heap_below[OF cond1 x])
      finally have ?case.
    }
    moreover
    {
      assume [simp]:"x \<notin> heapVars \<Gamma>" and  "x \<in> heapVars \<Delta>"
      have "\<lbrakk>the (map_of (\<Gamma> @ \<Delta>) x)\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> = \<lbrakk>the (map_of \<Delta> x)\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
        by (simp add: map_add_dom_app_simps)
      also have "\<dots>  = \<lbrakk>the (map_of \<Delta> x)\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
        apply (rule ESem_ignores_fresh[symmetric])
        apply (rule HSem_disjoint_less)
          using Gamma_fresh apply auto[1]
        apply (simp add: fdoms)
          using fresh apply (metis fresh fresh_PairD(1) fresh_heap_expr'[OF _ the_map_of_snd[OF `x \<in> heapVars \<Delta>`]] fresh_star_def)
        done
      also have "\<dots> \<sqsubseteq> \<lbrace>\<Delta>\<rbrace>\<rho> f! x"
        by (rule HSem_heap_below[OF cond3 `x \<in> heapVars \<Delta>`])
      also have "\<dots> = \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> f! x"
        by (rule the_lookup_HSem_other[symmetric, OF `x \<notin> heapVars \<Gamma>`])
      finally have ?case.
    }
    ultimately show ?case using goal2 by auto
  qed
qed

subsubsection {* The semantics of let only adds new bindings *}

text {*
The following lemma is not as general as possible and specialized to @{text "\<rho> = fempty"}, as that is
the only case required later on, and easier to prove.
*}

lemma HSem_unfold_let:
  assumes distinct1: "distinctVars (asToHeap as)"
  assumes distinct2: "distinctVars ((x, body) # \<Gamma>)"
  assumes fresh: "set (bn as) \<sharp>* (x, Let as body, \<Gamma>)"
  shows "\<lbrace>(x, Let as body) # \<Gamma>\<rbrace> \<le> \<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>"
proof (rule iffD2[OF fmap_less_restrict])
  from fresh
  have fresh_Gamma: "atom ` heapVars (asToHeap as) \<sharp>* \<Gamma>"
    by (metis fresh_star_Pair set_bn_to_atom_heapVars)

  from fresh
  have "set (bn as) \<sharp>* ((x, Let as body) # \<Gamma>)"
    by (auto simp add: fresh_star_def fresh_Pair fresh_Cons)
  from fresh_assn_distinct[OF this]
  have disjoint: "heapVars (asToHeap as) \<inter> insert x (heapVars \<Gamma>) = {}"
     by auto
  hence x_not_as: "x \<notin> heapVars (asToHeap as)"
    by auto

  {
    fix x' e
    assume "e \<in> snd ` set \<Gamma>"

    have simp1: " fdom (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>) \<inter> insert x (heapVars \<Gamma>) = insert x (heapVars \<Gamma>)"
      by auto

    have simp2: "fdom (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>) - insert x (heapVars \<Gamma>) = heapVars (asToHeap as)"
      using disjoint
      by auto

    have fresh_e: "atom ` heapVars (asToHeap as) \<sharp>* e"
      by (rule fresh_star_heap_expr'[OF fresh_Gamma `_ \<in> snd\` set \<Gamma>`])

    have "\<lbrakk> e \<rbrakk>\<^bsub>fmap_restr (insert x (heapVars \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>)\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<^esub>"
      apply (rule ESem_ignores_fresh[OF fmap_restr_less])
      apply (subst fdom_fmap_restr)
      apply (subst simp1)
      apply (subst simp2)
      apply (rule fresh_e)
      done
  } note Gamma_eq = this

case goal1
  have "\<lbrace>(x, Let as body) # \<Gamma>\<rbrace> = fmap_restr (insert x (heapVars \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>)"
  proof(rule below_antisym)
    show "\<lbrace>(x, Let as body) # \<Gamma>\<rbrace> \<sqsubseteq> fmap_restr (insert x (heapVars \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>)" (is "_ \<sqsubseteq> ?r")
    proof (rule HSemb_below[OF eq_imp_below])

      have "fdom ?r = insert x (heapVars \<Gamma>)" by auto
      hence [simp]: "set (bn as) \<sharp>* ?r"
        using disjoint
        by (auto simp add: set_bn_to_atom_heapVars fresh_star_def sharp_Env)

      show "heapToEnv ((x, Terms.Let as body) # \<Gamma>) (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>?r\<^esub>) = ?r"
      proof
      case goal1 show ?case by auto
      case (goal2 x')
        hence x': "x' \<in> insert x (heapVars \<Gamma>)" by simp

        hence x'_not_as:"x' \<notin> heapVars (asToHeap as)"
          using disjoint
          by auto

        show ?case
        proof(cases "x' = x")
        case True 
          have "\<lbrakk> Terms.Let as body \<rbrakk>\<^bsub>?r\<^esub> = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>?r\<^esub>" by simp
          also have "... = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>(fmap_restr (insert x (heapVars \<Gamma>)) (\<lbrace>asToHeap as @ ((x, body) # \<Gamma>)\<rbrace>))\<^esub>"
            by (rule arg_cong[OF HSem_reorder_head_append[OF x_not_as]])
          also have "... = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>asToHeap as @ ((x, body) # \<Gamma>)\<rbrace>\<^esub>"
            apply (rule arg_cong) back
            apply (rule HSemb_redo[where \<Delta> = "(x, body) # \<Gamma>", OF disjoint_is_HSem_cond, simplified (no_asm)])
            using disjoint by auto
          also have "... = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>\<^esub>"
            by (rule arg_cong[OF HSem_reorder_head_append[OF x_not_as], symmetric])
          finally
          show ?thesis using True x' by (simp add:the_lookup_HSem_heap [OF fempty_is_HSem_cond])
        next
          case False thus ?thesis
          apply (subst (2) HSemb_eq)
          using x'
          apply (simp add: lookupHeapToEnvNotAppend[OF x'_not_as] lookupHeapToEnv Gamma_eq[OF the_map_of_snd])
          done
        qed
      qed
    qed
  
    have [simp]: "set (bn as) \<sharp>* (\<lbrace>(x, Terms.Let as body) # \<Gamma>\<rbrace>)"
      apply (rule HSem_fresh_star)
      using fresh by (auto simp add: fresh_star_Pair fresh_star_Cons)

    have "(\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>) \<sqsubseteq> \<lbrace>asToHeap as\<rbrace>\<lbrace>(x, Let as body) # \<Gamma>\<rbrace>" (is "_ \<sqsubseteq> ?r")
    proof (rule HSemb_below[OF eq_imp_below])
      show "heapToEnv ((x, body) # asToHeap as @ \<Gamma>) (\<lambda>e. \<lbrakk>e\<rbrakk>\<^bsub>?r\<^esub>) = ?r"
      proof(rule fmap_eqI)
      case goal1 show ?case by auto
      next
      case (goal2 x')
        from goal2 have x': "x' = x \<or> x' \<in> heapVars (asToHeap as) \<or> x' \<in> heapVars \<Gamma>" by simp
        show ?case
        proof(cases "x' = x")
          assume "x' = x"
          thus ?case
            by (simp add: the_lookup_HSem_other[OF x_not_as] the_lookup_HSem_heap[OF fempty_is_HSem_cond])
        next
          have merged_r: "?r = \<lbrace>asToHeap as @ ((x, Let as body) # \<Gamma>)\<rbrace>"
            apply (rule HSem_merge)
              using disjoint  distinct1 distinct2 apply (auto simp add: distinctVars_Cons distinctVars_append)[1]
              using fresh apply (metis fresh_star_Cons fempty_fresh_star fresh_star_Pair set_bn_to_atom_heapVars)              
              apply simp
           done

          assume "x' \<noteq> x"
          hence map_of_reorder: "map_of ((x, body) # asToHeap as @ \<Gamma>) x' = map_of (asToHeap as @ ((x, Let as body) # \<Gamma>)) x'"
            apply simp
            apply (subst map_add_upd_left)
            apply (metis dom_map_of_conv_heapVars x_not_as)
            apply simp
            done

          show ?case
            unfolding merged_r
            apply (subst (2) HSemb_eq)
            apply (subst (1 2) lookupHeapToEnv)  using x' apply simp_all[2]
            apply (rule arg_cong[OF map_of_reorder])
            done 
        qed
      qed
    qed  
    thus "fmap_restr (insert x (heapVars \<Gamma>)) (\<lbrace>(x, body) # asToHeap as @ \<Gamma>\<rbrace>) \<sqsubseteq> \<lbrace>(x, Let as body) # \<Gamma>\<rbrace>"
      apply (rule below_trans[OF cont2monofunE[OF fmap_restr_cont] eq_imp_below])
      apply (rule fmap_restr_HSem_noop[of _ "\<lbrace>(x, Terms.Let as body) # \<Gamma>\<rbrace>", simplified (no_asm)])
      using disjoint apply auto
      done 
  qed
  thus ?case
    by (rule subst[where s = "insert q Q", standard, rotated], auto)
qed
end
