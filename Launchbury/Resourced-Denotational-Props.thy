theory "Resourced-Denotational-Props"
  imports "ResourcedDenotational"
begin

lemma CESem_bot[simp]:"(\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>\<bottom> = \<bottom>"
  by (nominal_induct e avoiding: \<sigma> rule: exp_assn.strong_induct(1)) auto

lemma CESem_Lam_not_bot[simp]:
  assumes [simp]:"atom z \<sharp> \<sigma>"
  assumes  "(\<N>\<lbrakk> Lam [z]. e \<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>c \<noteq> \<bottom>"
  shows "(\<N>\<lbrakk> Lam [z]. e \<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>c = CFn\<cdot>(\<Lambda> v. \<N>\<lbrakk>e\<rbrakk>\<^bsub>\<sigma>(z f\<mapsto> v)\<^esub>)"
proof-
  from assms(2) have "c \<noteq> \<bottom>" by auto
  then obtain c' where "c = C\<cdot>c'" by (cases c, auto)
  then show ?thesis by (auto simp add: Rep_cfun_inverse)
qed

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
  have  "cont (\<lambda> \<rho>. (\<Lambda> (C \<cdot> _). CFn \<cdot> (\<Lambda> v r. (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>) \<cdot> r)))"
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

interpretation has_cont_ESem CESem
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

interpretation has_ignore_fresh_ESem CESem
  apply default
  sorry


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
