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
  show ?case by auto
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


end
