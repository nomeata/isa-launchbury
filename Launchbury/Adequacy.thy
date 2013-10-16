theory Adequacy
imports "Resourced-Denotational-Props" "Launchbury" "DistinctVars" "CorrectnessResourced"
begin

(*
fixrec restr :: "CValue \<rightarrow> C \<rightarrow> CValue"
  where "restr\<cdot>f\<cdot>r\<cdot>r' = f\<cdot>(r \<sqinter> r')" 

consts resource_preserving :: "CValue' \<Rightarrow> bool"

lemma resource_preservingD:
  "resource_preserving (CFn\<cdot>f) \<Longrightarrow> (f\<cdot>x\<cdot>r = f\<cdot>(restr\<cdot>x\<cdot>r)\<cdot>r)"
  sorry
*)

lemma VariableNoBH:
  assumes "(x, e) \<in> set \<Gamma>"
  assumes "\<Gamma> : e \<Down>\<^bsub>x # L\<^esub> \<Delta> : z"
  shows "\<Gamma> : Var x \<Down>\<^bsub>L\<^esub> (x, z) # delete x \<Delta> : z"
sorry

definition demand :: "(C \<rightarrow> 'a::pcpo) \<Rightarrow> C" where
  "demand f = (if f\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom> then C\<^bsup>(LEAST n. f\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>)\<^esup> else C\<^sup>\<infinity>)"

lemma finite_resources_suffice:
  assumes "f\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom>"
  obtains n where "f\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
proof-
  {
  assume "\<forall>n. f\<cdot>(C\<^bsup>n\<^esup>) = \<bottom>"
  hence "f\<cdot>C\<^sup>\<infinity> \<sqsubseteq> \<bottom>"
    by (auto intro: lub_below[OF ch2ch_Rep_cfunR[OF chain_iterate]]
             simp add: Cinf_def fix_def2 contlub_cfun_arg[OF chain_iterate])
  with assms have False by simp
  }
  thus ?thesis using that by blast
qed

lemma more_resources_suffice:
  assumes "f\<cdot>r \<noteq> \<bottom>" and "r \<sqsubseteq> r'"
  shows "f\<cdot>r' \<noteq> \<bottom>"
  using assms(1) monofun_cfun_arg[OF assms(2), where  f = f]
  by auto

lemma infinite_resources_suffice:
  shows "f\<cdot>r \<noteq> \<bottom> \<Longrightarrow> f\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom>"
  by (erule more_resources_suffice[OF _ below_Cinf])

lemma demand_suffices:
  assumes "f\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom>"
  shows "f\<cdot>(demand f) \<noteq> \<bottom>"
  apply (simp add: assms demand_def)
  apply (rule finite_resources_suffice[OF assms])
  apply (rule LeastI)
  apply assumption
  done

lemma not_bot_demand:
  "f\<cdot>r \<noteq> \<bottom> \<longleftrightarrow> demand f \<noteq> C\<^sup>\<infinity> \<and> demand f \<sqsubseteq> r"
proof(intro iffI)
  assume "f\<cdot>r \<noteq> \<bottom>"
  thus "demand f \<noteq> C\<^sup>\<infinity> \<and> demand f \<sqsubseteq> r"
    apply (cases r rule:C_cases)
    apply (auto intro: Least_le simp add: demand_def dest: infinite_resources_suffice)
    done
next
  assume *: "demand f \<noteq> C\<^sup>\<infinity>  \<and> demand f \<sqsubseteq> r"
  then have "f\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom>" by (auto intro: Least_le simp add: demand_def dest: infinite_resources_suffice)
  hence "f\<cdot>(demand f) \<noteq> \<bottom>" by (rule demand_suffices)
  moreover from * have "demand f \<sqsubseteq> r"..
  ultimately
  show "f\<cdot>r \<noteq> \<bottom>" by (rule more_resources_suffice)
qed

lemma infinity_bot_demand:
  "f\<cdot>C\<^sup>\<infinity> = \<bottom> \<longleftrightarrow> demand f = C\<^sup>\<infinity>"
  by (metis below_Cinf not_bot_demand)

lemma demand_suffices':
  assumes "demand f = C\<^bsup>n\<^esup>"
  shows "f\<cdot>(demand f) \<noteq> \<bottom>"
  by (metis C_eq_Cinf assms demand_suffices infinity_bot_demand)

lemma demand_not_0: "demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>) \<noteq> \<bottom>"
proof
  assume "demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>) = \<bottom>"
  hence "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>\<bottom> \<noteq> \<bottom>" by (metis demand_suffices' iterate_0)
  thus False by simp
qed

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

lemma demand_Suc_Least:
  assumes [simp]: "f\<cdot>\<bottom> = \<bottom>"
  assumes "demand f \<noteq> C\<^sup>\<infinity>"
  shows "demand f = C\<^bsup>(Suc (LEAST n. f\<cdot>C\<^bsup>Suc n\<^esup> \<noteq> \<bottom>))\<^esup>"
proof-
  from assms
  have "demand f = C\<^bsup>(LEAST n. f\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>)\<^esup>" by (auto simp add: demand_def)
  also
  then obtain n where "f\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by (metis  demand_suffices')
  hence "(LEAST n. f\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>) = Suc (LEAST n. f\<cdot>C\<^bsup>Suc n\<^esup> \<noteq> \<bottom>)"
    apply (rule Least_Suc) by simp
  finally show ?thesis.
qed

lemma demand_C_case[simp]: "demand (C_case\<cdot>f) = C \<cdot> (demand f)"
proof(cases "demand (C_case\<cdot>f) = C\<^sup>\<infinity>")
  case True
  with assms
  have "C_case\<cdot>f\<cdot>C\<^sup>\<infinity> = \<bottom>"
    by (metis infinity_bot_demand)
  with True
  show ?thesis apply auto by (metis infinity_bot_demand)
next
  case False
  hence "demand (C_case\<cdot>f) = C\<^bsup>Suc (LEAST n. (C_case\<cdot>f)\<cdot>C\<^bsup>Suc n\<^esup> \<noteq> \<bottom>)\<^esup>"
    by (rule demand_Suc_Least[OF C.case_rews(1)])
  also have "\<dots> = C\<cdot>C\<^bsup>LEAST n. f\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>\<^esup>" by simp
  also have "\<dots> = C\<cdot>(demand  f)"
    using False unfolding demand_def by auto
  finally show ?thesis.
qed


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

lemma least_const_True[simp]: "(LEAST n. True) = (0::nat)"
  by (metis gr0I not_less_Least)

lemma demand_Lam:
  shows "demand (\<N>\<lbrakk>Lam [x]. e\<rbrakk>\<^bsub>\<rho>\<^esub>) = C\<cdot>\<bottom>"
  apply (simp add: Rep_cfun_inverse)
  apply (auto simp add: demand_def)
  done

lemma demand_App:
  shows "demand (\<N>\<lbrakk>App e x\<rbrakk>\<^bsub>\<rho>\<^esub>) = C \<cdot> (demand (\<Lambda> r. ((\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r \<down>CFn (\<rho> f!\<^sub>\<bottom> x))\<cdot>r))"
  by simp

notepad
begin
  fix f g r
  assume *: "(f\<cdot>r \<down>CFn g)\<cdot>r \<noteq> \<bottom>"
  hence "f \<cdot> r \<noteq> \<bottom>" by auto
  then obtain h where "f\<cdot>r = (CFn\<cdot>h)" by (metis CValue'.exhaust)
  from *[unfolded `f\<cdot>r = _`]
  have "(h\<cdot>g)\<cdot>r \<noteq> \<bottom>" by simp
end

fixrec CValue_restr :: "C \<rightarrow> CValue \<rightarrow> CValue"
  and  CValue'_restr :: "C \<rightarrow> CValue' \<rightarrow> CValue'"
  where "CValue_restr\<cdot>r\<cdot>f\<cdot>r' = (f\<cdot>(r \<sqinter> r'))" 
  |     "CValue'_restr\<cdot>r\<cdot>(CFn\<cdot>f) = CFn\<cdot>(CValue_restr\<cdot>r oo f)"


lemma [simp]: "CValue'_restr\<cdot>r\<cdot>\<bottom> = \<bottom>" by fixrec_simp
lemma [simp]: "CValue_restr\<cdot>r\<cdot>\<bottom> = \<bottom>" by fixrec_simp
lemma [simp]: "f \<cdot> \<bottom> = \<bottom> \<Longrightarrow> CValue_restr\<cdot>\<bottom>\<cdot>f = \<bottom>"  by fixrec_simp

lemma [simp]: "r \<sqinter> r = (r::C)"
  by (metis below_refl is_meetI)

lemma [simp]: "(r::C) \<sqinter> (r \<sqinter> x) = r \<sqinter> x"
  by (metis below_refl is_meetI meet_below1)


lemma [simp]: "CValue_restr\<cdot>r\<cdot>(CValue_restr\<cdot>r'\<cdot>v) = CValue_restr\<cdot>(r' \<sqinter> r)\<cdot>v"
  apply (rule cfun_eqI)
  apply simp
  done
  

definition fmap_C_restr where
  "fmap_C_restr r f = fmap_map (Rep_cfun (CValue_restr\<cdot>r)) f"

lemma cont2cont_fmap_map [simp, cont2cont]: "cont f \<Longrightarrow> cont g \<Longrightarrow> cont (\<lambda> x. fmap_map (f x) (g x))"
  sorry

lemma [simp, cont2cont]: "cont f \<Longrightarrow> cont g \<Longrightarrow> cont (\<lambda> x. fmap_C_restr (f x) (g x))"
  unfolding fmap_C_restr_def by simp

lemma [simp]: "v \<in> fdom \<rho> \<Longrightarrow> fmap_map f \<rho> f! v = f (\<rho> f! v)"
  apply auto
  by (metis fdomIff option.exhaust option_map_Some the.simps)

lemma [simp]: "f \<bottom> = \<bottom> \<Longrightarrow> fmap_map f \<rho> f!\<^sub>\<bottom> v = f (\<rho> f!\<^sub>\<bottom> v)"
  apply (cases "v \<in> fdom \<rho>")
  apply auto
  by (metis fdomIff option.exhaust option_map_Some the.simps)

lemma [simp]: "fmap_C_restr r (\<rho>(x f\<mapsto> v)) = fmap_C_restr r \<rho>(x f\<mapsto> CValue_restr\<cdot>r\<cdot>v)"
  unfolding fmap_C_restr_def by simp

lemma [simp]: "fmap_C_restr r \<rho> f!\<^sub>\<bottom> v = CValue_restr\<cdot>r\<cdot>(\<rho> f!\<^sub>\<bottom> v)"
  unfolding fmap_C_restr_def by simp

lemma [simp]: "v \<in> fdom \<rho> \<Longrightarrow> fmap_C_restr r \<rho> f! v = CValue_restr\<cdot>r\<cdot>(\<rho> f! v)"
  unfolding fmap_C_restr_def by (simp del: lookup_fmap_map)

lemma [simp]: "C\<cdot>r \<sqinter> r = r"
  by (auto intro: is_meetI simp add: below_C)

lemma fdom_fmap_C_restr[simp]: "fdom (fmap_C_restr r \<rho>) = fdom \<rho>"
  unfolding fmap_C_restr_def by simp

lemma CValue_restr_below[intro, simp]:
  "CValue_restr\<cdot>r\<cdot>x \<sqsubseteq> x"
  apply (rule cfun_belowI)
  apply simp
  by (metis below_refl meet_below2 monofun_cfun_arg)
  
lemma fmap_C_restr_restr_below[intro]:  "fmap_C_restr r \<rho> \<sqsubseteq> \<rho>"
  by (auto intro: fmap_belowI)

lemma CValue_restr_below_cong:
  "(\<And> r'. r' \<sqsubseteq> r \<Longrightarrow> f \<cdot> r' \<sqsubseteq> g \<cdot> r') \<Longrightarrow> CValue_restr\<cdot>r\<cdot>f \<sqsubseteq> CValue_restr\<cdot>r\<cdot>g"
  apply (rule cfun_belowI)
  apply simp
  by (metis below_refl meet_below1)

lemma CValue_restr_cong:
  "(\<And> r'. r' \<sqsubseteq> r \<Longrightarrow> f \<cdot> r' = g \<cdot> r') \<Longrightarrow> CValue_restr\<cdot>r\<cdot>f = CValue_restr\<cdot>r\<cdot>g"
  apply (intro below_antisym CValue_restr_below_cong )
  by (metis below_refl)+

lemma [simp]: "C\<cdot>r \<sqinter> C\<cdot>r' = C\<cdot>(r \<sqinter> r')"
  apply (rule is_meetI)
  apply (metis below_refl meet_below1 monofun_cfun_arg)
  apply (metis below_refl meet_below2 monofun_cfun_arg)
  apply (case_tac a)
  apply auto
  by (metis meet_above_iff)

lemma CValue_restr_C_case[simp]:
  "CValue_restr\<cdot>(C\<cdot>r)\<cdot>(C_case\<cdot>f) = C_case\<cdot>(CValue_restr\<cdot>r\<cdot>f)"
  apply (rule cfun_eqI)
  apply simp
  apply (case_tac x)
  apply simp
  apply simp
  done


thm CESem_Lam
lemma [simp]: "\<N>\<lbrakk>Lam [x]. e\<rbrakk>\<^bsub>\<rho>\<^esub> = (\<Lambda> (C\<cdot>r). (CFn\<cdot>(\<Lambda> v. CValue_restr\<cdot>r\<cdot>(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>(x f\<mapsto> CValue_restr\<cdot>r\<cdot>v)\<^esub>))))"
  sorry
thm CESem.simps(2)[no_vars]
lemma [simp]: "\<N>\<lbrakk>App e x\<rbrakk>\<^bsub>\<rho>\<^esub> = (\<Lambda> (C\<cdot>r). ((\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r \<down>CFn CValue_restr\<cdot>r\<cdot>(\<rho> f!\<^sub>\<bottom> x))\<cdot>r)"
  sorry

thm exp_assn.strong_induct[no_vars]


lemma  exp_strong_induct[case_names Var App Let Lam]:
  assumes "\<And>var c. P c (Var var)"
  assumes "\<And>exp var c. (\<And>c. P c exp) \<Longrightarrow> P c (App exp var)"
  assumes "\<And>assn exp c.
    set (bn assn) \<sharp>* c \<Longrightarrow> (\<And>c x. x \<in> heapVars (asToHeap assn) \<Longrightarrow>  P c (the (map_of (asToHeap assn) x))) \<Longrightarrow> (\<And>c. P c exp) \<Longrightarrow> P c (Terms.Let assn exp)"
  assumes "\<And>var exp c. {atom var} \<sharp>* c \<Longrightarrow> (\<And>c. P c exp) \<Longrightarrow> P c (Lam [var]. exp)"
  shows "P (c::'a::fs) exp"
  apply (rule exp_assn.strong_induct(1)[of P "\<lambda> c assn. (\<forall>x \<in> heapVars (asToHeap assn). P c (the (map_of (asToHeap assn) x)))"])
  apply (metis assms(1))
  apply (metis assms(2))
  apply (metis assms(3))
  apply (metis assms(4))
  apply auto
  done

lemma restr_can_restrict_heap: "CValue_restr\<cdot>r\<cdot>(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>) = CValue_restr\<cdot>r\<cdot>(\<N>\<lbrakk>e\<rbrakk>\<^bsub>fmap_C_restr r \<rho>\<^esub>)"
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
    apply (simp del: CESem_Lam)
    apply (rule CValue_restr_cong)
    apply (case_tac r')
    apply simp
    apply simp
    apply (rule cfun_eqI)
    apply simp
    apply (rule below_antisym)
    apply (subst Lam(2))
    apply simp
    apply (rule cont2monofunE) back back back back
    apply simp
    apply (metis below_C rev_below_trans)
    apply (rule cont2monofunE[OF _ fmap_C_restr_restr_below], simp)
    done
next
  case (App e x)
  { fix r r'
    from App[where r = r and b = \<rho>]
    have "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>(r \<sqinter> r') = (\<N>\<lbrakk>e\<rbrakk>\<^bsub>fmap_C_restr r \<rho>\<^esub>)\<cdot>(r \<sqinter> r')"
      by (metis CValue_restr.simps)
  } note * = this
  show ?case
    apply (rule below_antisym)
    defer
    apply (rule cont2monofunE[OF _ fmap_C_restr_restr_below], simp)
    apply (cases r, simp)
    apply (simp del: CValue_restr.simps CESem.simps(2))
    apply (rule monofun_cfun_arg)
    apply (rule cfun_belowI)
    apply (simp)
    apply (subst *)
    apply (rule cont2monofunE) back
    apply simp
    apply (rule monofun_cfun)
    apply (rule cont2monofunE[OF _ below_C], simp)
    apply (rule cont2monofunE) back back 
    apply simp
    by (metis below_C below_refl meet_above_iff meet_below1)
next
  case (Let as e)
  hence [simp]: "fdom \<rho> \<inter> heapVars (asToHeap as) = {}" by (metis disjoint_iff_not_equal sharp_star_Env)

  note Let(1)[simp]
  hence fresh2[simp]: "set (bn as) \<sharp>* fmap_C_restr r \<rho>" by (metis fdom_fmap_C_restr sharp_star_Env)

  { fix r
    have *: "has_cont_ESem CESem" by unfold_locales
    have "fmap_C_restr r (\<N>\<lbrace>asToHeap as\<rbrace>(\<rho> f|` (- heapVars (asToHeap as)))) = fmap_C_restr r (\<N>\<lbrace>asToHeap as\<rbrace>((fmap_C_restr r \<rho>)  f|` (- heapVars (asToHeap as))))" 
      unfolding has_cont_ESem.replace_upd[symmetric, OF *]
      apply (rule has_cont_ESem.parallel_UHSem_ind[OF *])
      apply simp
      apply simp
      apply (rule, simp)
      apply (case_tac "x \<in> heapVars (asToHeap as)")
      apply (simp add: lookupHeapToEnv)
      apply (subst (1 2) Let(2), assumption)
      apply simp
      apply simp
      done
    also have "\<rho> f|` (- heapVars (asToHeap as)) = \<rho>"
      using Let(1) by (auto intro: fmap_restr_useless  simp add:  sharp_star_Env)
    also have "(fmap_C_restr r \<rho>) f|` (- heapVars (asToHeap as)) = (fmap_C_restr r \<rho>)"
      using Let(1) by (auto intro: fmap_restr_useless  simp add:  sharp_star_Env)
    finally
    have "fmap_C_restr r (\<N>\<lbrace>asToHeap as\<rbrace>\<rho>) = fmap_C_restr r (\<N>\<lbrace>asToHeap as\<rbrace>fmap_C_restr r \<rho>)".
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
    prefer 3
    apply (rule cont2monofunE[OF _ below_C])
    apply simp_all
    done
qed

lemma
  assumes "C\<^bsup>n\<^esup> \<sqsubseteq> demand (\<rho> f!\<^sub>\<bottom> x)"
  assumes "demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>) = C\<^bsup>n\<^esup>"
  shows higher_demand_ignore: "demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>) = demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>fmap_delete x \<rho>\<^esub>)"
using assms
proof(induction n arbitrary: \<rho> e)
  case 0
  from `demand _ = C\<^bsup>0\<^esup>`
  have False by (metis demand_not_0 iterate_0)
  thus ?case..
next
  case (Suc n)
  have prem: "C\<^bsup>n\<^esup> \<sqsubseteq> demand (\<rho> f!\<^sub>\<bottom> x)"
    by (auto intro: below_trans[OF _ Suc(2)] simp add: below_C)

  show ?case
  proof(cases e rule:exp_assn.strong_exhaust(1)[where c= \<rho>, case_names Var App Let Lam])
    case (Var v)
    from Suc(2,3)[unfolded Var]
    have "v \<noteq> x" apply (auto simp add:Rep_cfun_inverse)
      by (metis C_below_C Suc.prems(1) Suc_n_not_le_n)

    from Suc(3)[unfolded Var]
    have [simp]: "v \<in> fdom \<rho>" by (auto intro: demand_Var_there simp del: iterate_Suc)

    from Suc.prems(2)
    have "demand (\<rho> f!\<^sub>\<bottom> v) = C\<^bsup>n\<^esup>"  unfolding Var demand_Var by simp
    hence "demand (\<rho> f!\<^sub>\<bottom> v) = demand (fmap_delete x \<rho> f!\<^sub>\<bottom> v) " using `v \<noteq> x` by simp
    thus ?thesis unfolding Var demand_Var  by simp
  next
    case (Lam v e')
    show ?thesis unfolding Lam by (simp only: demand_Lam)
  next
    case (App e' v)
    note Suc(3)[unfolded App]

    show ?thesis
      unfolding App
      apply simp
      oops

  

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
    have prem: "((\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn (\<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> x))\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by (auto simp add: Rep_cfun_inverse)
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

    have "((\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn (\<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> x))\<cdot>C\<^bsup>n\<^esup>
          \<sqsubseteq> ((\<N>\<lbrakk>Lam [y]. e''\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn (\<N>\<lbrace>\<Gamma>\<rbrace> f!\<^sub>\<bottom> x))\<cdot>C\<^bsup>n\<^esup>"
      by (intro monofun_cfun_arg monofun_cfun_fun correct1)
    also have "\<dots> \<sqsubseteq> ((\<N>\<lbrakk>Lam [y]. e''\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn (\<N>\<lbrace>\<Delta>\<rbrace> f!\<^sub>\<bottom> x))\<cdot>C\<^bsup>n\<^esup>"
      by (intro monofun_cfun_arg monofun_cfun_fun fun_belowD[OF correct2])
    also have "\<dots> = (\<N>\<lbrakk>e''\<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>)(y f\<mapsto> (\<N>\<lbrace>\<Delta>\<rbrace> f!\<^sub>\<bottom> x))\<^esub>)\<cdot>C\<^bsup>n\<^esup>"
      using lam_not_bot `y \<notin> heapVars \<Delta>`
      by (simp add: sharp_Env del: CESem.simps CESem_Lam)
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

