theory Adequacy
imports "Resourced-Denotational-Props" "Launchbury" "DistinctVars" "CorrectnessResourced"
begin


(*
lemma VariableNoBH:
  assumes "(x, e) \<in> set \<Gamma>"
  assumes "\<Gamma> : e \<Down>\<^bsub>x # L\<^esub> \<Delta> : z"
  shows "\<Gamma> : Var x \<Down>\<^bsub>L\<^esub> (x, z) # delete x \<Delta> : z"
sorry
*)

lemma demand_not_0: "demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>) \<noteq> \<bottom>"
proof
  assume "demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>) = \<bottom>"
  hence "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>\<bottom> \<noteq> \<bottom>" by (metis demand_suffices' iterate_0)
  thus False by simp
qed

(*
inductive pres1 :: "(CValue \<Rightarrow> bool) \<Rightarrow> CValue' \<Rightarrow> bool" for s where
  pres1_bot[simp,intro!]: "pres1 s \<bottom>" |
  pres1_CFn[intro]: "(\<And> x . s x \<Longrightarrow> s (f\<cdot>x)) \<Longrightarrow> pres1 s (CFn\<cdot>f)"

fun pres_prop'
  where
  "pres_prop' P 0 v = True" |
  "pres_prop' P (Suc n) v = pres1 (pres_prop' P n) (v \<cdot> C\<^sup>\<infinity>)" 

definition pres_prop where "pres_prop P v \<longleftrightarrow> (\<forall> n. pres_prop' P n v)"

lemma pres_prop_bot: "pres_prop P \<bottom>"
  unfolding pres_prop_def
  apply rule
  apply (induct_tac n)
  apply simp_all
  done

lemma pres_prop_CFnI: "(\<And> x. pres_prop P x \<Longrightarrow> pres_prop P (f\<cdot>x)) \<Longrightarrow> v \<cdot> C\<^sup>\<infinity> = CFn\<cdot>f \<Longrightarrow> pres_prop P v"
  unfolding pres_prop_def
  apply rule
  apply (induct_tac n)
  apply simp
  apply auto
  apply (intro pres1_CFn)
oops  
*) 

(* Nice try again, but breaks down in CFn_project: 

definition step_fun where
  "step_fun f \<longleftrightarrow> (\<forall> r r'. f\<cdot>r \<noteq> \<bottom> \<and> r \<sqsubseteq> r' \<longrightarrow> f\<cdot>r' = f\<cdot>r)"

lemma step_funI:
  "(\<And> r r'. f \<cdot> r \<noteq> \<bottom> \<Longrightarrow> r \<sqsubseteq> r' \<Longrightarrow> f\<cdot>r' = f\<cdot>r) \<Longrightarrow> step_fun f"
by (metis step_fun_def)

lemma [simp]: "step_fun \<bottom>"
  unfolding step_fun_def by simp

lemma [simp]: "adm step_fun"
  sorry

lemma step_fun_C_case[simp, intro]: "step_fun f \<Longrightarrow> step_fun (C_case\<cdot>f)"
  unfolding step_fun_def
  apply (rule, rule)
  apply (case_tac r, case_tac [2] r')
  apply auto
  done

lemma step_fun_CFn_project[simp, intro]:
  assumes "step_fun f"
  assumes "step_fun g"
  shows "step_fun (\<Lambda> r. ((f \<cdot> r) \<down>CFn g) \<cdot> r)"
proof (rule step_funI)
  fix r r'
  assume "(\<Lambda> r. (f\<cdot>r \<down>CFn g)\<cdot>r)\<cdot>r \<noteq> \<bottom>"
  hence "f \<cdot> r \<noteq> \<bottom>" by auto
  moreover
  assume "r \<sqsubseteq> r'"
  ultimately
  have [simp]: "f \<cdot> r' = f \<cdot> r" by (metis step_fun_def `step_fun f`)
  from `f \<cdot> r \<noteq> \<bottom>` obtain h where [simp]:"f \<cdot> r = CFn \<cdot> h" by (metis CValue'.exhaust)
  
  from `step_fun g` 
  have "step_fun (h \<cdot> g)" sorry
  with `(\<Lambda> r. (f\<cdot>r \<down>CFn g)\<cdot>r)\<cdot>r \<noteq> \<bottom>` `r \<sqsubseteq> r'`
  have [simp]: "h\<cdot>g\<cdot>r' = h\<cdot>g\<cdot>r" apply simp by (metis step_fun_def)

  show "(\<Lambda> r. (f\<cdot>r \<down>CFn g)\<cdot>r)\<cdot>r' = (\<Lambda> r. (f\<cdot>r \<down>CFn g)\<cdot>r)\<cdot>r" by simp
qed

lemma step_fun_const[intro, simp]: "(\<And> g. step_fun g \<Longrightarrow> step_fun (f \<cdot> g)) \<Longrightarrow> step_fun (\<Lambda> _. CFn\<cdot>f)"
  unfolding step_fun_def by simp

lemma bot_or_equal:
  assumes "\<And> x. step_fun (\<rho> f!\<^sub>\<bottom> x)"
  shows "step_fun (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)" and "\<And> x . x \<in> heapVars (asToHeap as) \<Longrightarrow> step_fun (\<N>\<lbrakk>the (map_of (asToHeap as) x)\<rbrakk>\<^bsub>\<rho>\<^esub>)"
using assms
proof(nominal_induct e and as avoiding: \<rho> rule: exp_assn.strong_induct)
  case Var thus ?case by (simp add: Rep_cfun_inverse)
next
  case App thus ?case by simp
next
  case (Lam x e)
  { fix v :: CValue
    assume "step_fun v"
    have "step_fun (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>(x f\<mapsto> v)\<^esub>)"
      apply (rule Lam)
      apply (case_tac "xa = x")
      using `step_fun v` apply simp
      using Lam(3) apply simp
      done
  }
  with Lam show ?case by auto
next
  case (Let as body)
  have *: "has_cont_ESem CESem" by unfold_locales
  have "\<forall> x. step_fun (\<N>\<lbrace>asToHeap as\<rbrace>(\<rho> f|` (- heapVars (asToHeap as))) f!\<^sub>\<bottom> x)" 
    unfolding has_cont_ESem.replace_upd[symmetric, OF *]
    apply (rule has_cont_ESem.UHSem_ind[OF *])
    apply simp
    apply simp
    apply rule
    apply (case_tac "x \<in> heapVars (asToHeap as)")
    apply (auto intro: Let(4) elim: Let(2) simp add: lookupHeapToEnv)
    done
  moreover have "\<rho> f|` (- heapVars (asToHeap as)) = \<rho>"
    using Let(1) by (auto intro: fmap_restr_useless  simp add:  sharp_star_Env)
  moreover note Let(1)
  ultimately
  show ?case by (auto simp add: Rep_cfun_inverse intro: Let(3))
next
  case ANil hence False by simp thus ?case..
next
  case ACons thus ?case by (auto dest: set_mp[OF set_delete_subset])
qed

*)


lemma demand_Var:
  shows "demand (\<N>\<lbrakk>Var x\<rbrakk>\<^bsub>\<rho>\<^esub>) = C\<cdot>(demand (\<rho> f!\<^sub>\<bottom> x))"
  by (simp add: Rep_cfun_inverse)

lemma demand_Var_there:
  assumes "demand (\<N>\<lbrakk>Var x\<rbrakk>\<^bsub>\<rho>\<^esub>) \<noteq> C\<^sup>\<infinity>"
  shows "x \<in> fdom \<rho>"
proof-
  from assms obtain n where *: "(\<N>\<lbrakk>Var x\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
    by (metis finite_resources_suffice infinity_bot_demand)
  hence "n \<noteq> 0" by (auto intro: ccontr)
  from * not0_implies_Suc[OF this]
   show ?thesis by (auto intro: ccontr)
qed

lemma demand_Lam:
  shows "demand (\<N>\<lbrakk>Lam [x]. e\<rbrakk>\<^bsub>\<rho>\<^esub>) = C\<cdot>\<bottom>"
  apply (simp add: Rep_cfun_inverse)
  apply (auto simp add: demand_def)
  done

(*
lemma demand_App:
  shows "demand (\<N>\<lbrakk>App e x\<rbrakk>\<^bsub>\<rho>\<^esub>) = C \<cdot> (demand (\<Lambda> r. ((\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r \<down>CFn (\<rho> f!\<^sub>\<bottom> x))\<cdot>r))"
  by simp
*)

lemma cont2cont_fmap_map [simp, cont2cont]: "cont f \<Longrightarrow> cont g \<Longrightarrow> cont (\<lambda> x. fmap_map (f x) (g x))"
  sorry

lemma fmap_map_lookup[simp]: "v \<in> fdom \<rho> \<Longrightarrow> fmap_map f \<rho> f! v = f (\<rho> f! v)"
  apply auto
  by (metis fdomIff option.exhaust option_map_Some the.simps)

lemma fmap_map_lookup_bot[simp]: "f \<bottom> = \<bottom> \<Longrightarrow> fmap_map f \<rho> f!\<^sub>\<bottom> v = f (\<rho> f!\<^sub>\<bottom> v)"
  apply (cases "v \<in> fdom \<rho>")
  apply auto
  by (metis fdomIff option.exhaust option_map_Some the.simps)

definition fmap_cmap :: "('a::cpo \<rightarrow> 'b::cpo) \<rightarrow> 'c::type f\<rightharpoonup> 'a \<rightarrow> 'c::type f\<rightharpoonup> 'b" 
  where  "fmap_cmap = (\<Lambda> f \<rho>. fmap_map (\<lambda> x. f\<cdot>x) \<rho>)"

lemma [simp]: "fdom (fmap_cmap\<cdot>f\<cdot>\<rho>) = fdom \<rho>"
  unfolding fmap_cmap_def by simp

lemma [simp]: "fmap_cmap\<cdot>f\<cdot>(\<rho>(x f\<mapsto> v)) = fmap_cmap\<cdot>f\<cdot>\<rho>(x f\<mapsto> f\<cdot>v)"
  unfolding fmap_cmap_def by simp

lemma [simp]: "x \<in> fdom \<rho> \<Longrightarrow> fmap_cmap\<cdot>f\<cdot>\<rho> f! x = f\<cdot>(\<rho> f! x )"
  unfolding fmap_cmap_def by (simp del: lookup_fmap_map)

lemma [simp]: "f\<cdot>\<bottom> = \<bottom> \<Longrightarrow> fmap_cmap\<cdot>f\<cdot>\<rho> f!\<^sub>\<bottom> x = f\<cdot>(\<rho> f!\<^sub>\<bottom> x )"
  unfolding fmap_cmap_def by (simp del: lookup_fmap_map)

definition fmap_C_restr :: "C \<rightarrow> (var f\<rightharpoonup> (C \<rightarrow> 'a::pcpo)) \<rightarrow> (var f\<rightharpoonup> (C \<rightarrow> 'a))" where
  "fmap_C_restr = (\<Lambda> r f.  fmap_cmap\<cdot>(C_restr\<cdot>r)\<cdot>f)"

lemma [simp]: "fmap_C_restr\<cdot>r\<cdot>(\<rho>(x f\<mapsto> v)) = fmap_C_restr\<cdot>r\<cdot>\<rho>(x f\<mapsto> C_restr\<cdot>r\<cdot>v)"
  unfolding fmap_C_restr_def by simp

lemma [simp]: "fmap_C_restr\<cdot>r\<cdot>\<rho> f!\<^sub>\<bottom> v = C_restr\<cdot>r\<cdot>(\<rho> f!\<^sub>\<bottom> v)"
  unfolding fmap_C_restr_def by simp

lemma [simp]: "v \<in> fdom \<rho> \<Longrightarrow> fmap_C_restr\<cdot>r\<cdot>\<rho> f! v = C_restr\<cdot>r\<cdot>(\<rho> f! v)"
  unfolding fmap_C_restr_def by (simp del: lookup_fmap_map)

lemma fdom_fmap_C_restr[simp]: "fdom (fmap_C_restr\<cdot>r\<cdot>\<rho>) = fdom \<rho>"
  unfolding fmap_C_restr_def by simp

lemma fmap_C_restr_restr_below[intro]: "fmap_C_restr\<cdot>r\<cdot>\<rho> \<sqsubseteq> \<rho>"
  by (auto intro: fmap_belowI)

lemma fmap_restr_eq_Cpred: 
  "fmap_C_restr\<cdot>r\<cdot>\<rho>1 = fmap_C_restr\<cdot>r\<cdot>\<rho>2 \<Longrightarrow> fmap_C_restr\<cdot>(Cpred\<cdot>r)\<cdot>\<rho>1 = fmap_C_restr\<cdot>(Cpred\<cdot>r)\<cdot>\<rho>2"
  sorry

lemma restr_can_restrict_heap: "C_restr\<cdot>r\<cdot>(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>) = C_restr\<cdot>r\<cdot>(\<N>\<lbrakk>e\<rbrakk>\<^bsub>fmap_C_restr\<cdot>(Cpred\<cdot>r)\<cdot>\<rho>\<^esub>)"
proof(nominal_induct e avoiding: \<rho> arbitrary: r rule: exp_strong_induct)
  case (Var x)
  show ?case
    apply (rule below_antisym)
    defer
    apply (rule cont2monofunE[OF _ fmap_C_restr_restr_below], simp)
    apply (simp add: Rep_cfun_inverse)
    apply (cases r)
    apply simp_all
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
    apply (subst Lam(2))
    apply simp
    apply (intro monofun_cfun below_refl cont2monofunE[OF ESem_cont] fmap_upd_mono Cpred_below )
    by (metis below_C rev_below_trans)
next
  case (App e x)
  { fix r r'
    from App[where r = r and b = \<rho>]
    have "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>(r \<sqinter> r') = (\<N>\<lbrakk>e\<rbrakk>\<^bsub>fmap_C_restr\<cdot>(Cpred\<cdot>r)\<cdot>\<rho>\<^esub>)\<cdot>(r \<sqinter> r')"
      apply (rule C_restr_eqD)
      by (metis below_refl meet_below1)
  } note * = this
  show ?case
    apply (rule below_antisym)
    defer
    apply (intro monofun_cfun_arg cont2monofunE[OF ESem_cont] fmap_C_restr_restr_below )
    apply (cases r, simp)
    apply (simp del: C_restr.simps)
    apply (rule monofun_cfun_arg)
    apply (rule cfun_belowI)
    apply (simp)
    apply (subst *)
    apply (intro monofun_cfun_fun monofun_cfun_arg cont2monofunE[OF ESem_cont] Cpred_below )
    done
next
  case (Let as e)
  hence [simp]: "fdom \<rho> \<inter> heapVars (asToHeap as) = {}"
    by (metis disjoint_iff_not_equal sharp_star_Env)

  note Let(1)[simp]
  hence fresh2[simp]: "set (bn as) \<sharp>* fmap_C_restr\<cdot>(Cpred\<cdot>r)\<cdot>\<rho>"
    by (metis (hide_lams, no_types) fdom_fmap_C_restr sharp_star_Env)

  { fix r
    have *: "has_cont_ESem CESem" by unfold_locales
    have "fmap_C_restr\<cdot>r\<cdot>(\<N>\<lbrace>asToHeap as\<rbrace>(\<rho> f|` (- heapVars (asToHeap as)))) = fmap_C_restr\<cdot>r\<cdot>(\<N>\<lbrace>asToHeap as\<rbrace>((fmap_C_restr\<cdot>r\<cdot>\<rho>)  f|` (- heapVars (asToHeap as))))" 
      unfolding has_cont_ESem.replace_upd[symmetric, OF *]
      apply (rule has_cont_ESem.parallel_UHSem_ind[OF *])
      apply simp
      apply simp
      apply (rule, simp)
      apply (case_tac "x \<in> heapVars (asToHeap as)")
      apply (simp add: lookupHeapToEnv) 
      apply (subst (1 2) Let(2), assumption)
      apply (drule fmap_restr_eq_Cpred)
      apply simp
      apply simp
      done
    also have "\<rho> f|` (- heapVars (asToHeap as)) = \<rho>"
      using Let(1) by (auto intro: fmap_restr_useless  simp add:  sharp_star_Env)
    also have "(fmap_C_restr\<cdot>r\<cdot>\<rho>) f|` (- heapVars (asToHeap as)) = (fmap_C_restr\<cdot>r\<cdot>\<rho>)"
      using Let(1) by (auto intro: fmap_restr_useless  simp add:  sharp_star_Env)
    finally
    have "fmap_C_restr\<cdot>r\<cdot>(\<N>\<lbrace>asToHeap as\<rbrace>\<rho>) = fmap_C_restr\<cdot>r\<cdot>(\<N>\<lbrace>asToHeap as\<rbrace>fmap_C_restr\<cdot>r\<cdot>\<rho>)".
  } note * = this

  show ?case
    apply (rule below_antisym)
    defer
    apply (rule cont2monofunE[OF _ fmap_C_restr_restr_below], simp)
    apply (simp add: Abs_cfun_inverse)
    apply (cases r, simp)
    apply (simp add: Abs_cfun_inverse Rep_cfun_inverse)
    apply (subst (1 2) Let(3))
    apply (subst *)
    apply (rule cont2monofunE[OF _ ]) back back back back
    apply simp
    apply (rule HSem_mono[OF disjoint_is_HSem_cond disjoint_is_HSem_cond])
    apply (simp_all)[2]
    apply (intro monofun_cfun_arg monofun_cfun_fun Cpred_below)
    done
qed

lemma can_restrict_heap:
  "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r = (\<N>\<lbrakk>e\<rbrakk>\<^bsub>fmap_C_restr\<cdot>(Cpred\<cdot>r)\<cdot>\<rho>\<^esub>)\<cdot>r"
  by (rule C_restr_eqD[OF restr_can_restrict_heap below_refl])
  
lemma add_BH:
  assumes "distinctVars \<Gamma>"
  assumes "(x, e) \<in> set \<Gamma>"
  assumes  "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
  shows "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
proof-
  


  have "demand (\<N>\<lbrakk>Var x\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>) = C\<cdot>(demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>))"
    unfolding demand_Var using assms by (auto simp add: distinctVars_map_of heapVars_from_set)
  hence "demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>) \<sqsubseteq> demand (\<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> x)" by (simp add: Rep_cfun_inverse)
  hence "demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>) = demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<^esub>)" sorry
  with assms(3)
  show ?thesis unfolding not_bot_demand by simp
qed



lemma CESem_Lam_not_bot[simp]:
  assumes  "(\<N>\<lbrakk> Lam [z]. e \<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>c \<noteq> \<bottom>"
  shows "(\<N>\<lbrakk> Lam [z]. e \<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>c \<sqsubseteq> CFn\<cdot>(\<Lambda> v. \<N>\<lbrakk>e\<rbrakk>\<^bsub>\<sigma>(z f\<mapsto> v)\<^esub>)"
proof-
  from assms have "c \<noteq> \<bottom>" by auto
  then obtain c' where "c = C\<cdot>c'" by (cases c, auto)
  then show ?thesis
    apply (auto simp add: Rep_cfun_inverse)
    apply (rule cfun_belowI)
    apply simp
    apply (rule below_trans[OF C_restr_below])
    apply (rule cont2monofunE[OF _ C_restr_below])
    apply simp
    done
qed


theorem adequacy:
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
    have "(\<N>\<lbrakk>?e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by auto
    hence "(\<N>\<lbrakk>?e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by (rule add_BH[OF `distinctVars \<Gamma>` `(x, ?e) \<in> set \<Gamma>`])
    from Suc.IH[OF this distinctVars_delete[OF Suc.prems(2)]]
    obtain \<Delta> v where "delete x \<Gamma> : ?e \<Down>\<^bsub>x # S\<^esub> \<Delta> : v" by blast
    ultimately
    have "\<Gamma> : (Var x) \<Down>\<^bsub>S\<^esub> (x,v) #  \<Delta> : v" by (rule Variable)
    thus ?thesis using Var by auto
  next
  case (App e' x)
    from Suc.prems[unfolded App]
    have prem: "((\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn  C_restr\<cdot>C\<^bsup>n\<^esup>\<cdot>(\<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> x))\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by (auto simp add: Rep_cfun_inverse)
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

    from e'_not_bot correct1
    have lam_not_bot: "(\<N>\<lbrakk>Lam [y]. e''\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by (metis below_bottom_iff monofun_cfun_fun)

    have "((\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn C_restr\<cdot>C\<^bsup>n\<^esup>\<cdot>(\<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> x))\<cdot>C\<^bsup>n\<^esup>
          \<sqsubseteq> ((\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn (\<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> x))\<cdot>C\<^bsup>n\<^esup>"
          by (rule cont2monofunE[OF _ C_restr_below], simp)
    also have "\<dots>  \<sqsubseteq> ((\<N>\<lbrakk>Lam [y]. e''\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn (\<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> x))\<cdot>C\<^bsup>n\<^esup>"
      by (intro monofun_cfun_arg monofun_cfun_fun correct1)
    also have "\<dots> \<sqsubseteq> ((\<N>\<lbrakk>Lam [y]. e''\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn (\<N>\<lbrace>\<Delta>\<rbrace> f!\<^sub>\<bottom> x))\<cdot>C\<^bsup>n\<^esup>"
      by (intro monofun_cfun_arg monofun_cfun_fun fun_belowD[OF correct2])
    also have "\<dots> \<sqsubseteq> (CFn\<cdot>(\<Lambda> v. \<N>\<lbrakk>e''\<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>)(y f\<mapsto> v)\<^esub>) \<down>CFn (\<N>\<lbrace>\<Delta>\<rbrace> f!\<^sub>\<bottom> x))\<cdot>C\<^bsup>n\<^esup>"
      by (rule cont2monofunE[OF _ CESem_Lam_not_bot[OF lam_not_bot]]) simp
    also have "\<dots> = (\<N>\<lbrakk>e''\<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>)(y f\<mapsto> (\<N>\<lbrace>\<Delta>\<rbrace> f!\<^sub>\<bottom> x))\<^esub>)\<cdot>C\<^bsup>n\<^esup>"
      using  `y \<notin> heapVars \<Delta>`  by (simp add: sharp_Env)
    also have "\<dots> = (\<N>\<lbrakk>e''[y::=x]\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup>"
      apply (rule arg_cong[OF CESem_subst])
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
      by (simp add: Rep_cfun_inverse fresh_star_Pair) 
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

end

