theory "Resourced-Denotational-Props"
  imports "ResourcedDenotational"
begin

lemma CESem_bot[simp]:"(\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>\<bottom> = \<bottom>"
  by (nominal_induct e avoiding: \<sigma> rule: exp_assn.strong_induct(1)) auto


lemma contE_subst:
  "cont g \<Longrightarrow> chain (\<lambda> i. f (Y i)) \<Longrightarrow> range (\<lambda>i. f (Y i)) <<| f (\<Squnion> i. Y i) \<Longrightarrow> range (\<lambda>i. g (f (Y i))) <<| g (f (\<Squnion> i. Y i))"
  by (metis cont_def lub_eqI)

subsubsection {* Continuity of the semantics *}

lemma CESem_cont':"Y0 = Y 0 \<Longrightarrow> chain Y \<Longrightarrow> range (\<lambda>i. \<N>\<lbrakk> e \<rbrakk>\<^bsub>Y i\<^esub>) <<| \<N>\<lbrakk> e \<rbrakk>\<^bsub>(\<Squnion> i. Y i)\<^esub> " and
  "\<And>e. e \<in> snd ` set (asToHeap as) \<Longrightarrow> cont (CESem e)"
proof(nominal_induct e and as avoiding: Y0  arbitrary: Y rule:exp_assn.strong_induct)
case (Lam x e Y0 Y)
  have [simp]: "\<And> i. fdom (Y i) = fdom (Lub Y)"
    by (metis chain_fdom `chain Y`)
  have [simp]:"\<And> i. atom x \<sharp> Y i" and [simp]:"atom x \<sharp> Lub Y"  using Lam.hyps(1) Lam.prems(1)
    unfolding sharp_Env by auto
  have "cont (CESem e)" using Lam.hyps(2) by (rule contI, auto)
  have  "cont (\<lambda> \<rho>. (\<Lambda> (C \<cdot> _). CFn \<cdot> (\<Lambda> v. \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>)))"
    by (intro cont2cont cont_compose[OF `cont (CESem e)`])
  from contE[OF this `chain Y`]
  show ?case by simp
next
case (App e v Y0 Y)
  have "cont (CESem e)" using App.hyps(1) by (rule contI, auto)
  show ?case
    by (auto intro!: contE[OF _ `chain Y`]  cont2cont cont_compose[OF `cont (CESem e)`])
next
case (Var v Y0 Y)
  have "cont (\<lambda> \<rho>. CESem (Var v) \<rho>)" by auto
  thus ?case
    by (rule contE[OF _ `chain Y`])    
next
case (Let as e Y0 Y)
  have fdoms[simp]: "\<And> i. fdom (Y i) = fdom (Lub Y)"
    by (metis chain_fdom `chain Y`)
  have [simp]:"\<And> i. set (bn as) \<sharp>* Y i" and [simp]: "set (bn as) \<sharp>* Lub Y"  using Let.hyps(1) Let.prems(1)
    unfolding sharp_star_Env by auto
  have unset: "\<And>i. fdom (Y i) \<inter> (heapVars (asToHeap as)) = {}"
    using Let by (metis fdoms disjoint_iff_not_equal sharp_star_Env)
  have conts: "\<forall>e\<in>snd ` set (asToHeap as). cont (CESem e)" using Let.hyps(2) by metis
  have cont: "cont (CESem e)" using Let.hyps(3) by (rule contI, auto)
  have cond: "CHSem_cond'' (asToHeap as) (\<Squnion> i. Y i)" by (rule disjoint_is_HSem_cond'[OF unset[unfolded fdoms] conts])
  have conds: "\<And>i. CHSem_cond'' (asToHeap as) (Y i)" by (rule disjoint_is_HSem_cond'[OF unset conts])

  have chain: "chain (\<lambda>i. HSem (asToHeap as) (Y i))"
    by (rule chainI, rule HSem_monofun''[OF Let.hyps(2) conds conds chainE[OF `chain Y`]])

  have HSem_lub: "HSem (asToHeap as) (Lub Y) = (\<Squnion> i. HSem (asToHeap as) (Y i))"
    by (rule HSem_cont''[OF Let.hyps(2) cond conds `chain Y`])
  show ?case
    by (simp add: Rep_cfun_inverse HSem_lub)
       (rule contE[OF cont_compose[OF cont_Rep_cfun2 cont] chain])
next
case ANil thus ?case by auto
next
case (ACons v e as Y0 Y)
  have "cont (CESem e)" using ACons.hyps(1) by (rule contI, auto)
  with ACons
  show ?case by (auto dest!: set_mp[OF set_delete_subset])
qed

interpretation Foo?: has_cont_ESem CESem
  apply default
  using CESem_cont'[OF refl]
  by (rule contI)

lemmas CESem_cont2cont[simp,cont2cont] = cont_compose[OF ESem_cont]

abbreviation CHSem_syn ("\<N>\<lbrace>_\<rbrace>_"  [60,60] 60) where "\<N>\<lbrace>\<Gamma>\<rbrace>\<rho> \<equiv> HSem \<Gamma> \<rho>"

abbreviation CHSem_fempty  ("\<N>\<lbrace>_\<rbrace>"  [60] 60) where "\<N>\<lbrace>\<Gamma>\<rbrace> \<equiv> \<N>\<lbrace>\<Gamma>\<rbrace>fempty"

(* TODO: Where to put this *)
  
lemma fresh_fmap_upd_lookup[simp]: "S \<sharp>* (\<rho>::Env) \<Longrightarrow> S \<sharp>* x \<Longrightarrow> S \<sharp>* \<rho>(x f\<mapsto> \<rho> f! y)"
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

lemma CHSem_bot[simp]:"(\<N>\<lbrace> \<Gamma> \<rbrace> f!\<^sub>\<bottom> x)\<cdot> \<bottom> = \<bottom>"
  by (cases "x \<in> heapVars \<Gamma>") auto



subsubsection {* The semantics ignores fresh variables *}

lemma CESem_ignores_fresh':
  "\<rho>1 \<le> \<rho>2 \<Longrightarrow> atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* e \<Longrightarrow> \<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>1\<^esub> = \<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>2\<^esub>"
  and
  "\<rho>1 \<le> \<rho>2 \<Longrightarrow> atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* as \<Longrightarrow> heapToEnv (asToHeap as) (\<lambda>e. \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>1\<^esub>) = heapToEnv (asToHeap as) (\<lambda>e. \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>2\<^esub>)"
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

  have "\<N>\<lbrace>asToHeap as\<rbrace>\<rho>1 \<le> \<N>\<lbrace>asToHeap as\<rbrace>\<rho>2"
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
  have "atom ` (fdom (\<N>\<lbrace>asToHeap as\<rbrace>\<rho>2) - fdom (\<N>\<lbrace>asToHeap as\<rbrace>\<rho>1)) \<sharp>* e "
    using Let(6) Let(1) Let(2)
    by (auto simp add: sharp_star_Env fresh_star_def)
  ultimately
  have "\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>asToHeap as\<rbrace>\<rho>1\<^esub> = \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>asToHeap as\<rbrace>\<rho>2\<^esub>"
    apply (rule Let.hyps(4))
    done
  thus "\<N>\<lbrakk> Terms.Let as e \<rbrakk>\<^bsub>\<rho>1\<^esub> = \<N>\<lbrakk> Terms.Let as e \<rbrakk>\<^bsub>\<rho>2\<^esub>"
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
    have "\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>1(x f\<mapsto> v)\<^esub> = \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>2(x f\<mapsto> v)\<^esub>"
      by (rule Lam(3))
  }
  thus "\<N>\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>1\<^esub> = \<N>\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>2\<^esub>"
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

interpretation has_ignore_fresh_ESem CESem
  by default (metis CESem_ignores_fresh')

subsection {* Nicer equations for CESem, without freshness requirements *}

lemma CESem_Lam[simp]: "\<N>\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub>  = (\<Lambda> (C \<cdot> _). CFn \<cdot> (\<Lambda> v. \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>))"
proof-
  have "\<N>\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<N>\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>fmap_delete x \<rho>\<^esub>"
    apply (rule ESem_ignores_fresh[symmetric, OF fmap_delete_less])
    apply (auto simp add: fresh_star_def)
    done
  also have "\<dots> = (\<Lambda> (C \<cdot> _). CFn \<cdot> (\<Lambda> v. \<N>\<lbrakk> e \<rbrakk>\<^bsub>(fmap_delete x \<rho>)(x f\<mapsto> v)\<^esub>))"
    apply (rule CESem.simps)
    apply (simp add: sharp_Env)
    done
  also have "\<dots> = (\<Lambda> (C \<cdot> _). CFn \<cdot> (\<Lambda> v. \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>))" by simp
  finally show ?thesis.
qed

lemma CESem_Lam_not_bot[simp]:
  assumes  "(\<N>\<lbrakk> Lam [z]. e \<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>c \<noteq> \<bottom>"
  shows "(\<N>\<lbrakk> Lam [z]. e \<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>c = CFn\<cdot>(\<Lambda> v. \<N>\<lbrakk>e\<rbrakk>\<^bsub>\<sigma>(z f\<mapsto> v)\<^esub>)"
proof-
  from assms have "c \<noteq> \<bottom>" by auto
  then obtain c' where "c = C\<cdot>c'" by (cases c, auto)
  then show ?thesis by (auto simp add: Rep_cfun_inverse)
qed

text {* Does not work with update-based semantics :-( *}

lemma CESem_Let[simp]: "\<N>\<lbrakk>Let as body\<rbrakk>\<^bsub>\<rho>\<^esub> = (\<Lambda> (C \<cdot> r). (\<N>\<lbrakk>body\<rbrakk>\<^bsub>has_ESem.HSem CESem (asToHeap as) \<rho>\<^esub>) \<cdot> r)"
proof-
  have "\<N>\<lbrakk> Let as body \<rbrakk>\<^bsub>\<rho>\<^esub> = \<N>\<lbrakk> Let as body \<rbrakk>\<^bsub>(\<rho> f|` (- heapVars (asToHeap as)))\<^esub>"
    apply (rule ESem_ignores_fresh[symmetric, OF fmap_restr_less])
    apply (auto simp add: fresh_star_def set_bn_to_atom_heapVars)
    done
  also have "\<dots> = (\<Lambda> (C\<cdot>r). (\<N>\<lbrakk>body\<rbrakk>\<^bsub>\<N>\<lbrace>asToHeap as\<rbrace>(\<rho> f|` (- heapVars (asToHeap as)))\<^esub>)\<cdot>r)"
    apply (rule CESem.simps)
    by (metis Compl_iff Int_iff fdom_fmap_restr sharp_star_Env)
  also have "\<N>\<lbrace>asToHeap as\<rbrace>(\<rho> f|` (- heapVars (asToHeap as))) = \<N>\<lbrace>asToHeap as\<rbrace>\<rho>"
    oops
  

subsubsection {* Denotation of Substitution *}

lemma CESem_subst_same: "\<rho> f!\<^sub>\<bottom> x = \<rho> f!\<^sub>\<bottom> y \<Longrightarrow>  \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<N>\<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<rho>\<^esub>"
  and 
  "\<rho> f!\<^sub>\<bottom> x = \<rho> f!\<^sub>\<bottom> y  \<Longrightarrow>  heapToEnv (asToHeap as) (\<lambda>e. \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>) = heapToEnv (asToHeap as[x::a=y]) (\<lambda>e. \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>) "
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
  have "\<N>\<lbrace>asToHeap as\<rbrace>\<rho> f!\<^sub>\<bottom> x = \<N>\<lbrace>asToHeap as\<rbrace>\<rho> f!\<^sub>\<bottom> y"
    using `x \<notin> heapVars (asToHeap as)` `y \<notin> heapVars (asToHeap as)`
    by (simp add: fmap_lookup_bot_HSem_other)
  hence "\<N>\<lbrakk>exp\<rbrakk>\<^bsub>\<N>\<lbrace>asToHeap as\<rbrace>\<rho>\<^esub> = \<N>\<lbrakk>exp[x::=y]\<rbrakk>\<^bsub>\<N>\<lbrace>asToHeap as\<rbrace>\<rho>\<^esub>"
    by (rule Let)
  moreover
  from `\<rho> f!\<^sub>\<bottom> x = \<rho> f!\<^sub>\<bottom> y`
  have "\<N>\<lbrace>asToHeap as\<rbrace>\<rho> = \<N>\<lbrace>asToHeap as[x::a=y]\<rbrace>\<rho>" and "\<N>\<lbrace>asToHeap as\<rbrace>\<rho> f!\<^sub>\<bottom> x = \<N>\<lbrace>asToHeap as[x::a=y]\<rbrace>\<rho> f!\<^sub>\<bottom> y"
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
  hence "\<And> v. \<N>\<lbrakk>exp\<rbrakk>\<^bsub>\<rho>(var f\<mapsto> v)\<^esub> = \<N>\<lbrakk>exp[x::=y]\<rbrakk>\<^bsub>\<rho>(var f\<mapsto> v)\<^esub>"
    by (rule Lam)
  thus ?case using Lam(1-3) by simp
next
case (ANil \<rho> x y) thus ?case by auto
next
case (ACons var exp as \<rho> x y)
  from ACons(1,2)[OF ACons(3)] ACons(3)
  show ?case by auto
qed

lemma CESem_subst:
  assumes "x \<noteq> y"
  assumes "atom x \<sharp> \<sigma>"
  shows "\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<sigma>(x f\<mapsto> (\<sigma> f!\<^sub>\<bottom> y))\<^esub> = \<N>\<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<sigma>\<^esub>"
proof-
  from assms(2) have [simp]:"x \<notin> fdom \<sigma>" by (simp add: sharp_Env)
  have [simp]:"insert x (fdom \<sigma>) - fdom \<sigma> = {x}" by auto

  have "\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<sigma>(x f\<mapsto> (\<sigma> f!\<^sub>\<bottom> y))\<^esub> = \<N>\<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<sigma>(x f\<mapsto> (\<sigma> f!\<^sub>\<bottom> y))\<^esub>"
    using assms(1)
    by (auto intro: CESem_subst_same simp add: Rep_cfun_inverse)
  also have "\<dots> = \<N>\<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<sigma>\<^esub>"
    by (auto intro: ESem_ignores_fresh[symmetric] simp add: fresh_star_singleton assms(1))
  finally
  show ?thesis.
qed

end
