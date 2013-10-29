theory "Abstract-Denotational-Props"
  imports "AbstractDenotational"
begin

locale cont_semantic_domain = semantic_domain + 
  assumes conts: "cont Fn" "cont Fn_project" "\<And> x. cont (Fn_project x)" "cont tick"
begin

lemmas cont_semantic_domain_conts[simp,cont2cont] =
  cont_compose[OF conts(1)]
  cont_compose2[OF conts(2,3)]
  cont_compose[OF conts(4)]

lemma Fn_project_mono: "a \<sqsubseteq> b \<Longrightarrow> c \<sqsubseteq> d \<Longrightarrow> Fn_project a c \<sqsubseteq> Fn_project b d"
  by (metis (hide_lams, no_types) cont2monofunE conts(2) conts(3) fun_belowD rev_below_trans)

lemma contE_subst:
  "cont g \<Longrightarrow> chain (\<lambda> i. f (Y i)) \<Longrightarrow> range (\<lambda>i. f (Y i)) <<| f (\<Squnion> i. Y i) \<Longrightarrow> range (\<lambda>i. g (f (Y i))) <<| g (f (\<Squnion> i. Y i))"
  by (metis cont_def lub_eqI)

subsubsection {* Continuity of the semantics *}

lemma ESem_cont': "Y0 = Y 0 \<Longrightarrow> chain Y \<Longrightarrow> range (\<lambda>i. \<lbrakk> e \<rbrakk>\<^bsub>Y i\<^esub>) <<| \<lbrakk> e \<rbrakk>\<^bsub>(\<Squnion> i. Y i)\<^esub> " and
  "\<And>e. e \<in> snd ` set (asToHeap as) \<Longrightarrow> cont (AESem e)"
proof(nominal_induct e and as avoiding: Y0  arbitrary: Y rule:exp_assn.strong_induct)
case (Lam x e Y0 Y)
  have [simp]: "\<And> i. fdom (Y i) = fdom (Lub Y)"
    by (metis chain_fdom `chain Y`)
  have [simp]:"\<And> i. atom x \<sharp> Y i" and [simp]:"atom x \<sharp> Lub Y"  using Lam.hyps(1) Lam.prems(1)
    unfolding sharp_Env by auto
  have "cont (AESem e)" using Lam.hyps(2) by (rule contI, auto)
  have  "cont (\<lambda> \<rho>. tick (Fn (\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>)))"
    by (intro cont2cont cont_compose[OF `cont (AESem e)`])
  from contE[OF this, OF Lam.prems(2)]
  show ?case
    by simp
next
case (App e v Y0 Y)
  have "cont (AESem e)" using App.hyps(1) by (rule contI, auto)
  thus ?case
    by (auto intro:contE[OF _ App.prems(2)])
next
case (Var v Y0 Y)
  have "cont (\<lambda> \<rho>. AESem (Var v) \<rho>)" by auto
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
  have heap_conts: "\<forall>e\<in>snd ` set (asToHeap as). cont (AESem e)" using Let.hyps(2) by metis
  have "cont (AESem e)" using Let.hyps(3) by (rule contI, auto)

  have chain: "chain (\<lambda>i. UHSem (asToHeap as) (Y i))"
    apply (rule chainI)
    apply (rule UHSem_monofun''[OF Let.hyps(2)  chainE[OF `chain Y`]])
    by assumption

  have "(\<Squnion> i. (UHSem (asToHeap as) (Y i))) = (UHSem (asToHeap as) (Lub Y))"
    apply (rule UHSem_cont''[OF Let.hyps(2) `chain Y`, symmetric])
    by assumption
  hence "range (\<lambda>i. \<lbrakk>e\<rbrakk>\<^bsub>has_ESem.UHSem AESem (asToHeap as) (Y i)\<^esub>) <<| \<lbrakk>e\<rbrakk>\<^bsub>has_ESem.UHSem AESem (asToHeap as) (Lub Y)\<^esub>"
    using Let(3)[OF refl chain] by simp
  thus ?case
    apply simp
    using ch2ch_cont[OF `cont (AESem e)` chain]
    by (erule contE_subst[OF conts(4)]) 
next
case ANil thus ?case by auto
next
case (ACons v e as Y0 Y)
  have "cont (AESem e)" using ACons.hyps(1) by (rule contI, auto)
  with ACons
  show ?case by (auto dest!:set_mp[OF set_delete_subset])
qed

sublocale has_cont_ESem AESem
  apply default
  using ESem_cont'[OF refl] by (rule contI)
  

lemmas CESem_cont2cont[simp,cont2cont] = cont_compose[OF ESem_cont]

abbreviation AHSem_syn ("\<lbrace>_\<rbrace>_"  [60,60] 60) where "\<lbrace>\<Gamma>\<rbrace>\<rho> \<equiv> UHSem \<Gamma> \<rho>"

abbreviation AHSem_fempty  ("\<lbrace>_\<rbrace>"  [60] 60) where "\<lbrace>\<Gamma>\<rbrace> \<equiv> \<lbrace>\<Gamma>\<rbrace>fempty"

subsubsection {* The semantics ignores fresh variables *}

lemma ESem_ignores_fresh':
  "\<rho>1 \<le> \<rho>2 \<Longrightarrow> atom ` (fdom \<rho>2 - fdom \<rho>1) \<sharp>* e \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^bsub>\<rho>1\<^esub> = \<lbrakk>e\<rbrakk>\<^bsub>\<rho>2\<^esub>"
proof (nominal_induct e avoiding: \<rho>1 \<rho>2 rule:exp_strong_induct)
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
  have "fdom \<rho>1 \<subseteq> fdom \<rho>2" by (metis Let(5) fmap_less_fdom)

  have "\<lbrace>asToHeap as\<rbrace>\<rho>1 \<le> \<lbrace>asToHeap as\<rbrace>\<rho>2"
  proof (rule parallel_UHSem_ind)
  case goal1 show ?case by simp
  case goal2
    show ?case
      apply (rule fmap_bottom_less)
      using `fdom \<rho>1 \<subseteq> fdom \<rho>2` by auto
  case (goal3 \<rho>1' \<rho>2')[simp]
    have prem: "atom ` (fdom \<rho>2' - fdom \<rho>1') \<sharp>* asToHeap as"
      using Let(6) Let(1) Let(2)
      by -(rule asToHeap_fresh_star, auto simp add:  sharp_star_Env fresh_star_def)

    show "\<rho>1 f++ heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>1'\<^esub>) \<le> \<rho>2 f++ heapToEnv (asToHeap as) (\<lambda>e. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>2'\<^esub>) "
    proof(rule fmap_less_eqI)
    case goal1
      show ?case using `fdom \<rho>1 \<subseteq> fdom \<rho>2` by auto
    next
    case (goal2 x)
      thus ?case
      proof (cases "x \<in> heapVars (asToHeap as)")
        case True
        with goal2 fresh_star_map_of[OF True prem]
        show ?thesis
          by (simp add: lookupHeapToEnv  Let(3)[OF _ goal3(3)])
      next
        case False with goal2 show ?thesis
          by (simp add: fmap_less_eqD[OF `\<rho>1 \<le> \<rho>2`])
      qed
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
qed

sublocale has_ignore_fresh_ESem AESem
  by default (metis ESem_ignores_fresh')

lemma ESem_add_fresh:
  assumes fresh: "atom x \<sharp> (\<rho>, \<Gamma>, e)"
  shows "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
proof(rule ESem_ignores_fresh[symmetric])
  have "\<lbrace>\<Gamma>\<rbrace>\<rho> = fmap_restr (fdom \<rho> \<union> heapVars \<Gamma>) (\<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>) "
    apply (rule UHSem_add_fresh[symmetric])
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


subsection {* Nicer equations for CESem, without freshness requirements *}

lemma AESem_Lam[simp]: "\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub>  = tick (Fn (\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>))"
proof-
  have "\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>fmap_delete x \<rho>\<^esub>"
    apply (rule ESem_ignores_fresh[symmetric, OF fmap_delete_less])
    apply (auto simp add: fresh_star_def)
    done
  also have "\<dots> = tick (Fn (\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>(fmap_delete x \<rho>)(x f\<mapsto> v)\<^esub>))"
    apply (rule AESem.simps)
    apply (simp add: sharp_Env)
    done
  also have "\<dots> = tick (Fn (\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>))" by simp
  finally show ?thesis.
qed

lemma CESem_Let[simp]: "\<lbrakk>Let as body\<rbrakk>\<^bsub>\<rho>\<^esub> = tick (\<lbrakk>body\<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>\<^esub>)"
proof-
  have "\<lbrakk> Let as body \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> Let as body \<rbrakk>\<^bsub>(\<rho> f|` (fdom \<rho> - heapVars (asToHeap as)))\<^esub>"
    apply (rule ESem_ignores_fresh[symmetric, OF fmap_restr_less])
    apply (auto simp add: fresh_star_def set_bn_to_atom_heapVars)
    done
  also have "\<dots> = tick (\<lbrakk>body\<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>(\<rho> f|` (fdom \<rho> - heapVars (asToHeap as)))\<^esub>)"
    by (auto simp add:fresh_star_def sharp_Env set_bn_to_atom_heapVars)
  also have "\<lbrace>asToHeap as\<rbrace>(\<rho> f|` (fdom \<rho> - heapVars (asToHeap as))) = \<lbrace>asToHeap as\<rbrace>\<rho>"
     by (rule UHSem_restr)
  finally show ?thesis.
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
    by (simp add: fmap_lookup_bot_UHSem_other)
  hence "\<lbrakk>exp\<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>\<^esub> = \<lbrakk>exp[x::=y]\<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>\<^esub>"
    by (rule Let)
  moreover
  from `\<rho> f!\<^sub>\<bottom> x = \<rho> f!\<^sub>\<bottom> y`
  have "\<lbrace>asToHeap as\<rbrace>\<rho> = \<lbrace>asToHeap as[x::a=y]\<rbrace>\<rho>" and "\<lbrace>asToHeap as\<rbrace>\<rho> f!\<^sub>\<bottom> x = \<lbrace>asToHeap as[x::a=y]\<rbrace>\<rho> f!\<^sub>\<bottom> y"
    apply (induction rule: parallel_UHSem_ind)
    apply simp
    apply simp
    apply simp
    apply simp
    apply (erule arg_cong[OF Let(4)])
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
  shows "\<lbrakk> e \<rbrakk>\<^bsub>\<sigma>(x f\<mapsto> (\<sigma> f!\<^sub>\<bottom> y))\<^esub> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<sigma>\<^esub>"
proof-
  have [simp]: "insert x (fdom \<sigma>) - (fdom \<sigma> - {x}) = {x}" by auto

  have "\<lbrakk> e \<rbrakk>\<^bsub>\<sigma>(x f\<mapsto> (\<sigma> f!\<^sub>\<bottom> y))\<^esub> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<sigma>(x f\<mapsto> (\<sigma> f!\<^sub>\<bottom> y))\<^esub>"
    using assms(1)
    by (auto intro: ESem_subst_same simp add: Rep_cfun_inverse)
  also have "\<dots> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>fmap_delete x \<sigma>\<^esub>"
    by (rule ESem_ignores_fresh[symmetric]) (auto simp add: fresh_star_singleton assms(1))
  also have "\<dots> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<sigma>\<^esub>"
    by (rule ESem_ignores_fresh[OF fmap_delete_less]) (auto simp add: fresh_star_def assms(1))
  finally
  show ?thesis.
qed

lemma ESem_mono_relaxed:
  assumes "fmap_lookup_bot \<rho>1 \<sqsubseteq> fmap_lookup_bot \<rho>2"
  shows "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>1\<^esub> \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>2\<^esub>"
using assms
proof(nominal_induct e avoiding: \<rho>1 \<rho>2 rule:exp_strong_induct)
case (Var x \<rho>)
  from Var.prems
  show ?case by (auto intro: cont2monofunE[OF conts(4)] dest: fun_belowD)
next
case (App e x \<rho>)
  from App.hyps[OF App.prems] App.prems
  show ?case
    by (auto intro: Fn_project_mono cont2monofunE[OF conts(4)] dest: fun_belowD)
next
case (Lam x e)
  from Lam(4)
  have "\<And> v. op f!\<^sub>\<bottom> (\<rho>1(x f\<mapsto> v)) \<sqsubseteq> op f!\<^sub>\<bottom> (\<rho>2(x f\<mapsto> v))"
    by (auto intro!: fun_belowI fun_belowD[OF  Lam(4)] simp add: fmap_lookup_bot_fmap_upd_eq Lam.prems)
  from Lam.hyps(3)[OF this]
  show ?case
    by (auto intro!: cfun_belowI cont2monofunE[OF conts(1)]  cont2monofunE[OF conts(4)] dest: fun_belowD)
next
case (Let as x)

  have "op f!\<^sub>\<bottom> (\<lbrace>asToHeap as\<rbrace>\<rho>1) \<sqsubseteq> op f!\<^sub>\<bottom> (\<lbrace>asToHeap as\<rbrace>\<rho>2)"
    apply (rule parallel_UHSem_ind)
    apply simp
    apply simp
    apply (rule fun_belowI)
    apply (case_tac "x \<in> heapVars (asToHeap as)")
     apply (simp add: lookupHeapToEnv )
     apply (rule Let.hyps(3), assumption, assumption)
    apply (simp add: fun_belowD[OF Let.prems])
    done
  from Let.hyps(4)[OF this]
  show ?case using Let(1,2) by (auto intro: cont2monofunE[OF conts(4)] dest: fun_belowD)
qed

lemma ESem_fmap_cong:
  assumes "fmap_lookup_bot \<rho>1 = fmap_lookup_bot \<rho>2"
  shows "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>1\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>2\<^esub>"
using assms
by (metis (full_types) ESem_mono_relaxed below_antisym below_refl)

lemma UHSem_monofun_relaxed:
  assumes "op f!\<^sub>\<bottom> \<rho> \<sqsubseteq> op f!\<^sub>\<bottom>\<rho>'"
  shows "op f!\<^sub>\<bottom> (\<lbrace>h\<rbrace>\<rho>) \<sqsubseteq> op f!\<^sub>\<bottom> (\<lbrace>h\<rbrace>\<rho>')"
  apply (rule parallel_UHSem_ind)
  apply simp
  apply simp
  apply (rule fun_belowI)
  apply (case_tac "x \<in> heapVars h")
  apply (auto simp add: lookupHeapToEnv ESem_mono_relaxed fun_belowD[OF assms])
  done

end

end
