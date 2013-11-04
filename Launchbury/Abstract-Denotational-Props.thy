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

lemma ESem_cont': "cont (AESem e)" and
  "\<And>e. e \<in> snd ` set (asToHeap as) \<Longrightarrow> cont (AESem e)"
proof(nominal_induct e and as rule:exp_assn.strong_induct)
case (Lam x e)
  show "cont (\<lambda> \<rho>. \<lbrakk>Lam [x]. e\<rbrakk>\<^bsub>\<rho>\<^esub>)"
    unfolding AESem.simps
    by (intro cont2cont cont_compose[OF Lam.hyps])
next
case (Let as e)
  show "cont (\<lambda>\<rho>. \<lbrakk>Let as e\<rbrakk>\<^bsub>\<rho>\<^esub>)"
    unfolding AESem.simps
    by (intro cont2cont cont_compose[OF Let.hyps(2)] cont_compose[OF UHSem_cont'''[OF Let.hyps(1)]])
qed (auto dest!:set_mp[OF set_delete_subset])

sublocale has_cont_ESem AESem by default (rule ESem_cont')

lemmas CESem_cont2cont[simp,cont2cont] = cont_compose[OF ESem_cont]

abbreviation AHSem_syn ("\<lbrace>_\<rbrace>_"  [60,60] 60) where "\<lbrace>\<Gamma>\<rbrace>\<rho> \<equiv> UHSem \<Gamma> \<rho>"

abbreviation AHSem_fempty  ("\<lbrace>_\<rbrace>"  [60] 60) where "\<lbrace>\<Gamma>\<rbrace> \<equiv> \<lbrace>\<Gamma>\<rbrace>fempty"

subsubsection {* The semantics ignores fresh variables *}

lemma ESem_considers_fv': "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho> f|` (fv e)\<^esub>"
proof (nominal_induct e avoiding: \<rho> rule:exp_strong_induct)
  case Var
  show ?case by simp
next
  have [simp]: "\<And> S x. S \<inter> insert x S = S" by auto
  case App
  show ?case
    by (simp, subst (1 2) App, simp)
next
  case (Lam x e)
  show ?case by simp
next
  case (Let as e)

  have "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>\<^esub> = \<lbrakk>e\<rbrakk>\<^bsub>(\<lbrace>asToHeap as\<rbrace>\<rho>) f|` (fv as \<union> fv e)\<^esub>"
    by (subst (1 2) Let(3)) (simp add:  sup_commute)
  also
  have "fv (asToHeap as) \<subseteq> fv as \<union> fv e" using fv_asToHeap by auto
  hence "(\<lbrace>asToHeap as\<rbrace>\<rho>) f|` (fv as \<union> fv e) = \<lbrace>asToHeap as\<rbrace>(\<rho> f|` (fv as \<union> fv e))"
     by (rule HSem_ignores_fresh_restr'[OF _ Let(2)])
  also
  have "\<lbrace>asToHeap as\<rbrace>(\<rho> f|` (fv as \<union> fv e)) = \<lbrace>asToHeap as\<rbrace>\<rho> f|` (fv as \<union> fv e - heapVars (asToHeap as))"
    by (rule UHSem_fresh_cong) auto
  finally
  show ?case using Let(1) by simp
qed

sublocale has_ignore_fresh_ESem AESem
  by default (rule fv_supp_exp, rule ESem_considers_fv')

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
    by (auto simp add: fresh_Pair fresh_fmap_pure heapVars_not_fresh)
  thus "atom ` (fdom (\<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>) - fdom (\<lbrace>\<Gamma>\<rbrace>\<rho>)) \<sharp>* e"
    using fresh
    by (simp add: fresh_star_def fresh_Pair)
qed


subsection {* Nicer equations for CESem, without freshness requirements *}

lemma AESem_Lam[simp]: "\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub>  = tick (Fn (\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>))"
proof-
  have *: "\<And> v. ((\<rho> f|` (fv e - {x}))(x f\<mapsto> v)) f|` fv e = (\<rho>(x f\<mapsto> v)) f|` fv e"
    by rule auto

  have "\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>fmap_delete x \<rho>\<^esub>"
    apply (rule ESem_ignores_fresh[symmetric, OF fmap_delete_less])
    apply (auto simp add: fresh_star_def)
    done
  also have "\<dots> = tick (Fn (\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>(\<rho> f|` (fv e - {x}))(x f\<mapsto> v)\<^esub>))"
    by simp
  also have "\<dots> = tick (Fn (\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>((\<rho> f|` (fv e - {x}))(x f\<mapsto> v)) f|` fv e\<^esub>))"
    by (subst  ESem_considers_fv, rule)
  also have "\<dots> = tick (Fn (\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v) f|` fv e\<^esub>))"
    unfolding *..
  also have "\<dots> = tick (Fn (\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>))"
    unfolding  ESem_considers_fv[symmetric]..
  finally show ?thesis.
qed
declare AESem.simps(1)[simp del]

lemma CESem_Let[simp]: "\<lbrakk>Let as body\<rbrakk>\<^bsub>\<rho>\<^esub> = tick (\<lbrakk>body\<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>\<^esub>)"
proof-
  have "\<lbrakk> Let as body \<rbrakk>\<^bsub>\<rho>\<^esub> = tick (\<lbrakk>body\<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>(\<rho> f|` fv (Let as body))\<^esub>)" 
    by simp
  also have "\<lbrace>asToHeap as\<rbrace>(\<rho> f|` fv(Let as body)) = \<lbrace>asToHeap as\<rbrace>(\<rho> f|` (fv as \<union> fv body))" 
    by (rule UHSem_fresh_cong) auto
  also have "\<dots> = (\<lbrace>asToHeap as\<rbrace>\<rho>) f|` (fv as \<union> fv body)"
    by (rule HSem_ignores_fresh_restr'[symmetric, OF subset_trans[OF fv_asToHeap Un_upper1] ESem_considers_fv])
  also have "\<lbrakk>body\<rbrakk>\<^bsub>\<dots>\<^esub> = \<lbrakk>body\<rbrakk>\<^bsub>\<lbrace>asToHeap as\<rbrace>\<rho>\<^esub>"
    by (rule ESem_fresh_cong) auto
  finally show ?thesis.
qed
declare AESem.simps(4)[simp del]

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

lemma fmap_restr_monofun_relaxed:
  "op f!\<^sub>\<bottom> \<rho> \<sqsubseteq> op f!\<^sub>\<bottom>\<rho>' \<Longrightarrow> op f!\<^sub>\<bottom> (\<rho> f|` S) \<sqsubseteq> op f!\<^sub>\<bottom> (\<rho>' f|` S)"
by (auto simp add: below_fun_def lookup_fmap_restr_eq)

lemma UHSem_monofun_relaxed':
  assumes "\<And>x \<rho> \<rho>'. x \<in> heapVars h \<Longrightarrow> op f!\<^sub>\<bottom> \<rho> \<sqsubseteq> op f!\<^sub>\<bottom>\<rho>' \<Longrightarrow> \<lbrakk> the (map_of h x) \<rbrakk>\<^bsub>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> the (map_of h x) \<rbrakk>\<^bsub>\<rho>'\<^esub>"
  assumes "op f!\<^sub>\<bottom> \<rho> \<sqsubseteq> op f!\<^sub>\<bottom>\<rho>'"
  shows "op f!\<^sub>\<bottom> (\<lbrace>h\<rbrace>\<rho>) \<sqsubseteq> op f!\<^sub>\<bottom> (\<lbrace>h\<rbrace>\<rho>')"
  apply (rule parallel_UHSem_ind)
  apply simp
  apply simp
  apply (rule fun_belowI)
  apply (case_tac "x \<in> heapVars h")
  apply (auto simp add: lookupHeapToEnv  assms(1) fun_belowD[OF assms(2)])
  done

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
  show ?case
    by (auto intro!: cont2monofunE[OF conts(4)] UHSem_monofun_relaxed' Let.hyps(3) Let.hyps(4) fmap_restr_monofun_relaxed  Let.prems)
qed

lemma ESem_fmap_cong:
  assumes "fmap_lookup_bot \<rho>1 = fmap_lookup_bot \<rho>2"
  shows "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>1\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>2\<^esub>"
using assms
by (metis (full_types) ESem_mono_relaxed below_antisym below_refl)

lemma UHSem_monofun_relaxed:
  assumes "op f!\<^sub>\<bottom> \<rho> \<sqsubseteq> op f!\<^sub>\<bottom>\<rho>'"
  shows "op f!\<^sub>\<bottom> (\<lbrace>h\<rbrace>\<rho>) \<sqsubseteq> op f!\<^sub>\<bottom> (\<lbrace>h\<rbrace>\<rho>')"
  by (rule UHSem_monofun_relaxed'[OF ESem_mono_relaxed assms])

end

end
