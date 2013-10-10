theory Adequacy
imports "Resourced-Denotational-Props" "Launchbury" "DistinctVars" "CorrectnessResourced"
begin

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
  from assms
  have "(\<N>\<lbrakk>Var x\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>Suc n\<^esup> \<noteq> \<bottom>"
    by (simp add: distinctVars_map_of heapVars_from_set)
  hence "demand (\<N>\<lbrakk>Var x\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>) \<noteq> None"  unfolding not_bot_demand by auto

  from `demand (\<N>\<lbrakk>Var x\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>) \<noteq> None` 
  have "the (demand (\<N>\<lbrakk>Var x\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)) = Suc (the (demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)))"
    unfolding demand_Var using assms by (auto simp add: distinctVars_map_of heapVars_from_set)
  hence "the (demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)) < the (demand (\<N>\<lbrakk>Var x\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>))" by simp
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

