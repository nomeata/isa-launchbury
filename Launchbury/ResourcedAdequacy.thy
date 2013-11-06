theory ResourcedAdequacy
imports "ResourcedDenotational" "Launchbury" "DistinctVars" "CorrectnessResourced"
begin

lemma not_bot_below_trans[trans]:
  "a \<noteq> \<bottom> \<Longrightarrow> a \<sqsubseteq> b \<Longrightarrow> b \<noteq> \<bottom>"
  by (metis below_bottom_iff)

lemma demand_not_0: "demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>) \<noteq> \<bottom>"
proof
  assume "demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>) = \<bottom>"
  with demand_suffices'[where n = 0, simplified, OF this]
  have "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>\<bottom> \<noteq> \<bottom>" by simp
  thus False by simp
qed

definition fmap_C_restr :: "C \<rightarrow> (var f\<rightharpoonup> (C \<rightarrow> 'a::pcpo)) \<rightarrow> (var f\<rightharpoonup> (C \<rightarrow> 'a))" where
  "fmap_C_restr = (\<Lambda> r f.  fmap_cmap\<cdot>(C_restr\<cdot>r)\<cdot>f)"

lemma [simp]: "fmap_C_restr\<cdot>r\<cdot>(\<rho>(x f\<mapsto> v)) = fmap_C_restr\<cdot>r\<cdot>\<rho>(x f\<mapsto> C_restr\<cdot>r\<cdot>v)"
  unfolding fmap_C_restr_def by simp

lemma [simp]: "fmap_C_restr\<cdot>r\<cdot>\<rho> f!\<^sub>\<bottom> v = C_restr\<cdot>r\<cdot>(\<rho> f!\<^sub>\<bottom> v)"
  unfolding fmap_C_restr_def by simp

lemma fmap_C_restr_the_lookup[simp]: "v \<in> fdom \<rho> \<Longrightarrow> fmap_C_restr\<cdot>r\<cdot>\<rho> f! v = C_restr\<cdot>r\<cdot>(\<rho> f! v)"
  unfolding fmap_C_restr_def by (simp del: lookup_fmap_map)

lemma fdom_fmap_C_restr[simp]: "fdom (fmap_C_restr\<cdot>r\<cdot>\<rho>) = fdom \<rho>"
  unfolding fmap_C_restr_def by simp

lemma fdom_fmap_C_restrD: "fmap_C_restr\<cdot>r\<cdot>\<rho> = fmap_C_restr\<cdot>r'\<cdot>\<rho>' \<Longrightarrow>  fdom \<rho> = fdom \<rho>'"
  by (metis fdom_fmap_C_restr)

lemma fmap_C_restr_fmap_expand[simp]: "fmap_C_restr\<cdot>r\<cdot>(\<rho>\<^bsub>[S]\<^esub>) = (fmap_C_restr\<cdot>r\<cdot>\<rho>)\<^bsub>[S]\<^esub>"
  apply (cases "finite S")
  apply (rule fmap_eqI)
  apply auto
  apply (case_tac "x \<in> fdom \<rho>")
  apply (auto simp add: fmap_expand_nonfinite)
  done

lemma fmap_C_restr_fempty[simp]: "fmap_C_restr\<cdot>r\<cdot>f\<emptyset> = f\<emptyset>"
  unfolding fmap_C_restr_def by auto

lemma fmap_C_restr_restr_below[intro]: "fmap_C_restr\<cdot>r\<cdot>\<rho> \<sqsubseteq> \<rho>"
  by (auto intro: fmap_belowI)

lemma C_restr_eq_Cpred: 
  assumes "C_restr\<cdot>r\<cdot>x = C_restr\<cdot>r\<cdot>y"
  shows "C_restr\<cdot>(Cpred\<cdot>r)\<cdot>x = C_restr\<cdot>(Cpred\<cdot>r)\<cdot>y"
  apply (rule cfun_eqI) 
  apply simp
  by (metis C_restr_eqD[OF assms] Cpred_below meet_below2 meet_comm)

lemma fmap_restr_eq_Cpred: 
  assumes "fmap_C_restr\<cdot>r\<cdot>\<rho>1 = fmap_C_restr\<cdot>r\<cdot>\<rho>2"
  shows "fmap_C_restr\<cdot>(Cpred\<cdot>r)\<cdot>\<rho>1 = fmap_C_restr\<cdot>(Cpred\<cdot>r)\<cdot>\<rho>2"
proof(rule fmap_eqI)
  from fdom_fmap_C_restrD[OF assms]
  show "fdom (fmap_C_restr\<cdot>(Cpred\<cdot>r)\<cdot>\<rho>1) = fdom (fmap_C_restr\<cdot>(Cpred\<cdot>r)\<cdot>\<rho>2)" by simp
next
  fix x
  assume *: "x \<in> fdom (fmap_C_restr\<cdot>(Cpred\<cdot>r)\<cdot>\<rho>1)"
  hence "x \<in> fdom (fmap_C_restr\<cdot>r\<cdot>\<rho>1)" by simp
  with assms
  have "C_restr\<cdot>r\<cdot>(\<rho>1 f! x) = C_restr\<cdot>r\<cdot>(\<rho>2 f! x)" by (metis fdom_fmap_C_restr fmap_C_restr_the_lookup)
  hence "C_restr\<cdot>(Cpred\<cdot>r)\<cdot>(\<rho>1 f! x) = C_restr\<cdot>(Cpred\<cdot>r)\<cdot>(\<rho>2 f! x)"  by (rule C_restr_eq_Cpred)
  thus "fmap_C_restr\<cdot>(Cpred\<cdot>r)\<cdot>\<rho>1 f! x = fmap_C_restr\<cdot>(Cpred\<cdot>r)\<cdot>\<rho>2 f! x" using * fdom_fmap_C_restrD[OF assms]
   by (metis fdom_fmap_C_restr fmap_C_restr_the_lookup)
qed

lemma restr_can_restrict_heap: "C_restr\<cdot>r\<cdot>(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>) = C_restr\<cdot>r\<cdot>(\<N>\<lbrakk>e\<rbrakk>\<^bsub>fmap_C_restr\<cdot>(Cpred\<cdot>r)\<cdot>\<rho>\<^esub>)"
proof(nominal_induct e arbitrary: \<rho> r rule: exp_strong_induct)
  case (Var x)
  show ?case
    apply (rule below_antisym)
    defer
    apply (rule cont2monofunE[OF _ fmap_C_restr_restr_below], simp)
    apply (simp)
    apply (cases r)
    apply (simp_all add: Rep_cfun_inverse)
    done
next
  case (Lam x e)
  show ?case
    apply (simp)
    apply (rule C_restr_cong)
    apply (case_tac r', simp)
    apply simp
    apply (rule cfun_eqI)
    apply simp
    apply (rule below_antisym)
    defer
    apply (rule cont2monofunE[OF _ fmap_C_restr_restr_below], simp)
    apply (subst Lam(1))
    apply simp
    apply (intro monofun_cfun below_refl monofun_cfun_arg fmap_upd_mono Cpred_below )
    by (metis below_C rev_below_trans)
next
  case (App e x)
  { fix r r'
    from App[where r = r and \<rho> = \<rho>]
    have "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>(r \<sqinter> r') = (\<N>\<lbrakk>e\<rbrakk>\<^bsub>fmap_C_restr\<cdot>(Cpred\<cdot>r)\<cdot>\<rho>\<^esub>)\<cdot>(r \<sqinter> r')"
      apply (rule C_restr_eqD)
      by (metis below_refl meet_below1)
  } note * = this
  show ?case
    apply (rule below_antisym)
    defer
    apply (intro monofun_cfun_arg monofun_cfun_arg fmap_C_restr_restr_below )
    apply (cases r, simp)
    apply (simp del: C_restr.simps)
    apply (rule monofun_cfun_arg)
    apply (rule cfun_belowI)
    apply (simp)
    apply (subst *)
    apply (intro monofun_cfun_fun monofun_cfun_arg Cpred_below )
    done
next
  case (Let as e)

  have *: "\<And> r. fmap_C_restr\<cdot>r\<cdot>(\<N>\<lbrace>asToHeap as\<rbrace>\<rho>) = fmap_C_restr\<cdot>r\<cdot>(\<N>\<lbrace>asToHeap as\<rbrace>fmap_C_restr\<cdot>r\<cdot>\<rho>)"
    apply (rule has_ESem.parallel_HSem_ind)
    apply simp
    apply simp
    apply (rule, simp)
    apply (case_tac "x \<in> heapVars (asToHeap as)")
    apply (simp add: lookupHeapToEnv) 
    apply (subst (1 2) Let(1), assumption)
    apply (drule fmap_restr_eq_Cpred)
    apply simp
    apply simp
    done

  show ?case
    apply (rule below_antisym)
    defer apply (rule cont2monofunE[OF _ fmap_C_restr_restr_below], simp)
    apply (cases r, simp)
    apply simp
    apply (subst (1 4) Rep_cfun_inverse) (* Be careful not to destroy the locale parameters *)
    apply (subst (1 2) Let(2))
    apply (subst *)
    apply (rule cont2monofunE[OF _ Cpred_below], simp)
    done
qed

lemma can_restrict_heap:
  "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r = (\<N>\<lbrakk>e\<rbrakk>\<^bsub>fmap_C_restr\<cdot>(Cpred\<cdot>r)\<cdot>\<rho>\<^esub>)\<cdot>r"
  by (rule C_restr_eqD[OF restr_can_restrict_heap below_refl])

lemma C_restr_bot_demand:
  assumes "C\<cdot>r \<sqsubseteq> demand f"
  shows "C_restr\<cdot>r\<cdot>f = \<bottom>"
proof(rule cfun_eqI)
  fix r'
  have "f\<cdot>(r \<sqinter> r') = \<bottom>"
  proof(rule classical)
    have "r \<sqsubseteq> C \<cdot> r" by (rule below_C)
    also
    note assms
    also
    assume *: "f\<cdot>(r \<sqinter> r') \<noteq> \<bottom>"
    hence "demand f \<sqsubseteq> (r \<sqinter> r')" unfolding not_bot_demand by auto
    hence "demand f \<sqsubseteq> r"  by (metis below_refl meet_below1 below_trans)
    finally have "r = demand f".
    with assms
    have "demand f = C\<^sup>\<infinity>" by (cases "demand f" rule:C_cases) (auto simp add: iterate_Suc[symmetric] simp del: iterate_Suc)
    thus "f\<cdot>(r \<sqinter> r') = \<bottom>" by (metis not_bot_demand)
  qed
  thus "C_restr\<cdot>r\<cdot>f\<cdot>r' = \<bottom>\<cdot>r'" by simp
qed

lemma C_Cpred_id[simp]:
  "r \<noteq> \<bottom> \<Longrightarrow> C\<cdot>(Cpred\<cdot>r) = r"
  by (cases r) auto

lemma demand_contravariant:
  assumes "f \<sqsubseteq> g"
  shows "demand g \<sqsubseteq> demand f"
proof(cases "demand f" rule:C_cases)
  fix n
  assume "demand f = C\<^bsup>n\<^esup>"
  hence "f\<cdot>(demand f) \<noteq> \<bottom>" by (metis demand_suffices')
  also note monofun_cfun_fun[OF assms]
  finally have "g\<cdot>(demand f) \<noteq> \<bottom>" .
  thus "demand g \<sqsubseteq> demand f" unfolding not_bot_demand by auto
qed auto

lemma add_BH:
  assumes "distinctVars \<Gamma>"
  assumes "(x, e) \<in> set \<Gamma>"
  assumes  "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
  shows "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
proof-
  let ?C = "demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)"

  from  assms(3)
  have "?C \<sqsubseteq> C\<^bsup>n\<^esup>" unfolding not_bot_demand by simp

  from assms(1,2)
  have [simp]: "the (map_of \<Gamma> x) = e" by (metis distinctVars_map_of the.simps)

  have "fmap_C_restr\<cdot>(Cpred\<cdot>?C)\<cdot>(\<N>\<lbrace>\<Gamma>\<rbrace>) \<sqsubseteq> (\<N>\<lbrace>delete x \<Gamma>\<rbrace>)\<^bsub>[heapVars \<Gamma>]\<^esub> \<and> \<N>\<lbrace>\<Gamma>\<rbrace> \<sqsubseteq> \<N>\<lbrace>\<Gamma>\<rbrace>"
    apply (rule HSem_ind) back back back back back back back back back
    apply (intro adm_lemmas cont2cont)
    apply simp
    apply (erule conjE)
    apply rule
    apply (rule fmap_belowI)
    apply simp
    apply (case_tac "xa = x")
    apply (simp add: lookupHeapToEnv)
    apply (rule C_restr_bot_demand)
    apply (subst C_Cpred_id[OF demand_not_0])
    apply (erule demand_contravariant[OF monofun_cfun_arg])

    apply (simp add: lookupHeapToEnv the_lookup_HSem_heap)
    apply (subst restr_can_restrict_heap)
    apply (rule below_trans[OF C_restr_below])
    apply (rule below_trans[OF monofun_cfun_arg eq_imp_below])
    apply (erule below_trans[OF monofun_cfun_fun[OF monofun_cfun_arg[OF Cpred_below]]])
    thm ESem_fmap_cong
    apply (rule ESem_fmap_cong[OF the_lookup_bot_fmap_expand_subset])
    apply simp
    apply (auto dest: fmap_below_dom)[1]

    apply (rule fmap_belowI)
    apply (auto simp add: lookupHeapToEnv the_lookup_HSem_heap monofun_cfun_arg)
    done
  hence heaps: "fmap_C_restr\<cdot>(Cpred\<cdot>?C)\<cdot>(\<N>\<lbrace>\<Gamma>\<rbrace>) \<sqsubseteq> (\<N>\<lbrace>delete x \<Gamma>\<rbrace>)\<^bsub>[heapVars \<Gamma>]\<^esub>"..

  from assms(3)
  have "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>?C \<noteq> \<bottom>"
    by (rule demand_suffices[OF infinite_resources_suffice])
  also
  have "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>?C = (\<N>\<lbrakk>e\<rbrakk>\<^bsub>fmap_C_restr\<cdot>(Cpred\<cdot>?C)\<cdot>(\<N>\<lbrace>\<Gamma>\<rbrace>)\<^esub>)\<cdot>?C"
    by (rule can_restrict_heap)
  also
  have "\<dots> \<sqsubseteq> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>(\<N>\<lbrace>delete x \<Gamma>\<rbrace>)\<^bsub>[heapVars \<Gamma>]\<^esub>\<^esub>)\<cdot>?C"
    by (intro monofun_cfun_arg monofun_cfun_fun heaps )
  also
  have "\<dots> = (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<^esub>)\<cdot>?C"
    by (rule arg_cong[OF ESem_fmap_cong[OF the_lookup_bot_fmap_expand_subset]]) auto
  also
  have "\<dots> \<sqsubseteq> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup>"
    using `?C \<sqsubseteq> C\<^bsup>n\<^esup>` by (rule monofun_cfun_arg)
  finally
  show ?thesis.
qed

lemma ESem_Lam_not_bot[simp]:
  assumes  "(\<N>\<lbrakk> Lam [z]. e \<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>c \<noteq> \<bottom>"
  shows "(\<N>\<lbrakk> Lam [z]. e \<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>c \<sqsubseteq> CFn\<cdot>(\<Lambda> v. \<N>\<lbrakk>e\<rbrakk>\<^bsub>\<sigma>(z f\<mapsto> v)\<^esub>)"
proof-
  from assms have "c \<noteq> \<bottom>" by auto
  then obtain c' where "c = C\<cdot>c'" by (cases c, auto)
  then show ?thesis
    apply auto
    apply (rule cfun_belowI)
    apply simp
    apply (rule below_trans[OF C_restr_below])
    apply (rule cont2monofunE[OF _ C_restr_below])
    apply simp
    done
qed


lemma adequacy_finite:
  assumes "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
  and "distinctVars \<Gamma>"
  shows "\<exists> \<Delta> v. \<Gamma> : e \<Down>\<^bsub>S\<^esub> \<Delta> : v"
using assms
proof(induction n arbitrary: \<Gamma> e S)
  case 0
  hence False by auto
  thus ?case..
next
  case (Suc n)
  show ?case
  proof(cases e rule:exp_assn.strong_exhaust(1)[where c = "(\<Gamma>,S)", case_names Var App Let Lam])
  case (Var x)
    let ?e = "the (map_of \<Gamma> x)"
    from Suc.prems[unfolded Var]
    have "x \<in> heapVars \<Gamma>" by (auto intro: ccontr)
    hence "(x, ?e) \<in> set \<Gamma>" by (induction \<Gamma>) auto
    moreover
    from Suc.prems[unfolded Var] `(x, ?e) \<in> set \<Gamma>` `x \<in> heapVars \<Gamma>`
    have "(\<N>\<lbrakk>?e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by (auto simp add: the_lookup_HSem_heap)
    hence "(\<N>\<lbrakk>?e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by (rule add_BH[OF `distinctVars \<Gamma>` `(x, ?e) \<in> set \<Gamma>`])
    from Suc.IH[OF this distinctVars_delete[OF Suc.prems(2)]]
    obtain \<Delta> v where "delete x \<Gamma> : ?e \<Down>\<^bsub>x # S\<^esub> \<Delta> : v" by blast
    ultimately
    have "\<Gamma> : (Var x) \<Down>\<^bsub>S\<^esub> (x,v) #  \<Delta> : v" by (rule Variable)
    thus ?thesis using Var by auto
  next
  case (App e' x)
    from Suc.prems[unfolded App]
    have prem: "((\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn  C_restr\<cdot>C\<^bsup>n\<^esup>\<cdot>(\<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> x))\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by auto
    hence e'_not_bot: "(\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by auto
    from Suc.IH[OF this Suc.prems(2)]
    obtain \<Delta> v where lhs': "\<Gamma> : e' \<Down>\<^bsub>x#S\<^esub> \<Delta> : v" by blast 

    from result_evaluated_fresh[OF lhs']
    obtain y e'' where n': "v = (Lam [y]. e'')" and "atom y \<sharp> (\<Gamma>, e', x, S, \<Delta>)" by blast
    with lhs'
    have lhs: "\<Gamma> : e' \<Down>\<^bsub>x # S\<^esub> \<Delta> : Lam [y]. e''" by simp

    from `atom y \<sharp> _` have "y \<notin> heapVars \<Delta>" by (metis (full_types) fresh_Pair heapVars_not_fresh)
   

    from correctness[OF lhs `distinctVars \<Gamma>`, where \<rho> = "f\<emptyset>"]
    have correct1: "\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub> \<sqsubseteq> \<N>\<lbrakk>Lam [y]. e''\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>" and correct2: "op f!\<^sub>\<bottom> (\<N>\<lbrace>\<Gamma>\<rbrace>) \<sqsubseteq> op f!\<^sub>\<bottom> (\<N>\<lbrace>\<Delta>\<rbrace>)"
      by auto

    note e'_not_bot
    also note monofun_cfun_fun[OF correct1]
    finally have lam_not_bot: "(\<N>\<lbrakk>Lam [y]. e''\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>".

    have "((\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn C_restr\<cdot>C\<^bsup>n\<^esup>\<cdot>(\<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> x))\<cdot>C\<^bsup>n\<^esup>
          \<sqsubseteq> ((\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn (\<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> x))\<cdot>C\<^bsup>n\<^esup>"
          by (rule cont2monofunE[OF _ C_restr_below], simp)
    also have "\<dots>  \<sqsubseteq> ((\<N>\<lbrakk>Lam [y]. e''\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn (\<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> x))\<cdot>C\<^bsup>n\<^esup>"
      by (intro monofun_cfun_arg monofun_cfun_fun correct1)
    also have "\<dots> \<sqsubseteq> ((\<N>\<lbrakk>Lam [y]. e''\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn (\<N>\<lbrace>\<Delta>\<rbrace> f!\<^sub>\<bottom> x))\<cdot>C\<^bsup>n\<^esup>"
      by (intro monofun_cfun_arg monofun_cfun_fun fun_belowD[OF correct2])
    also have "\<dots> \<sqsubseteq> (CFn\<cdot>(\<Lambda> v. \<N>\<lbrakk>e''\<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>)(y f\<mapsto> v)\<^esub>) \<down>CFn (\<N>\<lbrace>\<Delta>\<rbrace> f!\<^sub>\<bottom> x))\<cdot>C\<^bsup>n\<^esup>"
      by (rule cont2monofunE[OF _ ESem_Lam_not_bot[OF lam_not_bot]]) simp
    also have "\<dots> = (\<N>\<lbrakk>e''\<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>)(y f\<mapsto> (\<N>\<lbrace>\<Delta>\<rbrace> f!\<^sub>\<bottom> x))\<^esub>)\<cdot>C\<^bsup>n\<^esup>"
      using  `y \<notin> heapVars \<Delta>` by simp
    also have "\<dots> = (\<N>\<lbrakk>e''[y::=x]\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup>"
      apply (rule arg_cong[OF ESem_subst])
      using `atom y \<sharp> _` by (simp_all add: fresh_Pair fresh_at_base)
    finally
    have "\<dots> \<noteq> \<bottom>" using prem by auto
    moreover
    have "distinctVars \<Delta>"
      by (rule reds_pres_distinctVars[OF lhs' Suc.prems(2)])
    ultimately
    obtain \<Theta> v' where rhs: "\<Delta> : e''[y::=x] \<Down>\<^bsub>S\<^esub> \<Theta> : v'" using Suc.IH by blast
    
    have "\<Gamma> : App e' x \<Down>\<^bsub>S\<^esub> \<Theta> : v'"
      by (rule reds_ApplicationI[OF `atom y \<sharp> _` lhs rhs])
    thus ?thesis using App by auto
  next
  case (Lam v e')
    have "\<Gamma> : Lam [v]. e' \<Down>\<^bsub>S\<^esub> \<Gamma> : Lam [v]. e'" ..
    thus ?thesis using Lam by blast
  next
  case (Let as e')
    {
    from Suc.prems[unfolded Let] Let(1)
    have prem: "(\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>asToHeap as\<rbrace>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" 
      by (simp add: fresh_star_Pair) 
    also have "\<N>\<lbrace>asToHeap as\<rbrace>\<N>\<lbrace>\<Gamma>\<rbrace> = \<N>\<lbrace>asToHeap as @ \<Gamma>\<rbrace>"
      apply (rule HSem_merge)
      using Let(1)
      by (auto simp add: fresh_star_Pair set_bn_to_atom_heapVars)
    finally 
    have "(\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>asToHeap as @ \<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>".
    }
    moreover
    have "distinctVars (asToHeap as @ \<Gamma>)" by (metis Let(1) Suc.prems(2) distinctVars_append_asToHeap fresh_star_Pair)
    ultimately
    obtain \<Delta> v where "asToHeap as @ \<Gamma> : e' \<Down>\<^bsub>S\<^esub> \<Delta> : v" using Suc.IH by blast
    hence "\<Gamma> : Let as e' \<Down>\<^bsub>S\<^esub> \<Delta> : v"
      by (rule reds.Let[OF Let(1)])
    thus ?thesis using Let by auto
  qed
qed

theorem resourced_adequacy:
  assumes "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>r \<noteq> \<bottom>"
  and "distinctVars \<Gamma>"
  shows "\<exists> \<Delta> v. \<Gamma> : e \<Down>\<^bsub>S\<^esub> \<Delta> : v"
  by (rule finite_resources_suffice[OF infinite_resources_suffice[OF assms(1)]])
     (erule adequacy_finite[OF _ assms(2)])

end
