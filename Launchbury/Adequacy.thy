theory Adequacy
imports "Resourced-Denotational-Props" "Launchbury" "DistinctVars" "CorrectnessResourced"
begin

lemma VariableNoBH:
  assumes "(x, e) \<in> set \<Gamma>"
  assumes "\<Gamma> : e \<Down>\<^bsub>x # L\<^esub> \<Delta> : z"
  shows "\<Gamma> : Var x \<Down>\<^bsub>L\<^esub> (x, z) # delete x \<Delta> : z"
sorry


definition demand :: "CEnv => exp => nat option" where
  "demand \<rho> e = (if (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom> then Some (LEAST n. (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>) else None)"

lemma finite_resources_suffice:
  assumes "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom>"
  obtains n where "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
  sorry

lemma more_resources_suffice:
  assumes "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" and "n \<le> m"
  shows "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>m\<^esup> \<noteq> \<bottom>"
  sorry

lemma infinite_resources_suffice:
  assumes "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
  shows "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom>"
  sorry

lemma demand_suffices:
  assumes "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom>"
  shows "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>the (demand \<rho> e)\<^esup> \<noteq> \<bottom>"
  apply (simp add: assms demand_def)
  apply (rule finite_resources_suffice[OF assms])
  apply (rule LeastI)
  apply assumption
  done

lemma not_bot_demand:
  "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom> \<longleftrightarrow> demand \<rho> e \<noteq> None \<and> n \<ge> the (demand \<rho> e)"
proof(intro iffI)
  assume "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
  thus "demand \<rho> e \<noteq> None \<and> n \<ge> the (demand \<rho> e)"
    by (auto intro: Least_le simp add: demand_def dest: infinite_resources_suffice)
next
  assume *: "demand \<rho> e \<noteq> None \<and> n \<ge> the (demand \<rho> e)"
  then have "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom>"
    by (auto intro: Least_le simp add: demand_def dest: infinite_resources_suffice)
  hence "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>the (demand \<rho> e)\<^esup> \<noteq> \<bottom>" by (rule demand_suffices)
  moreover from * have "n \<ge> the (demand \<rho> e)"..
  ultimately
  show "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by (rule more_resources_suffice)
qed

lemma infinity_bot_demand:
  "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^sup>\<infinity> = \<bottom> \<longleftrightarrow> demand \<rho> e = None"
  by (metis demand_suffices infinite_resources_suffice nat_le_linear not_bot_demand)

lemma demand_suffices':
  assumes "demand \<rho> e = Some n"
  shows "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
  by (metis assms not_bot_demand option.distinct(1) order_refl the.simps)

lemma demand_not_0: "demand \<rho> e \<noteq> Some 0"
proof
  assume "demand \<rho> e = Some 0"
  hence "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>0\<^esup> \<noteq> \<bottom>" by (rule demand_suffices')
  thus False by simp
qed

lemma demand_Suc_Least:
  assumes "demand \<rho> e \<noteq> None"
  shows "demand \<rho> e = Some (Suc (LEAST n. (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>Suc n\<^esup> \<noteq> \<bottom>))"
proof-
  from assms
  have "demand \<rho> e = Some (LEAST n. (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>)" by (auto simp add: demand_def)
  also
  then obtain n where "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by (metis  demand_suffices')
  hence "(LEAST n. (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>) = Suc (LEAST n. (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>Suc n\<^esup> \<noteq> \<bottom>)"
    by (rule Least_Suc) auto
  finally show ?thesis.
qed


lemma demand_Var:
  assumes "distinctVars \<Gamma>"
  assumes "(x,e) \<in> set \<Gamma>"
  shows "demand (\<N>\<lbrace>\<Gamma>\<rbrace>) (Var x) = Option.map Suc (demand (\<N>\<lbrace>\<Gamma>\<rbrace>) e)"
proof(cases "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^sup>\<infinity> = \<bottom>")
  case True
  with assms
  have "(\<N>\<lbrakk>Var x\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^sup>\<infinity> = \<bottom>"
    by (simp add: distinctVars_map_of heapVars_from_set)
  with True
  show ?thesis unfolding infinity_bot_demand by simp
next
  case False
  with assms
  have *: "(\<N>\<lbrakk>Var x\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom>"
    by (simp add: distinctVars_map_of heapVars_from_set)
  hence "demand (\<N>\<lbrace>\<Gamma>\<rbrace>) (Var x) \<noteq> None" by (metis infinity_bot_demand)

  have [simp]: "x \<in> heapVars \<Gamma>" by (metis assms(2) heapVars_from_set)
  have [simp]: "map_of \<Gamma> x = Some e" by (metis assms distinctVars_map_of)

  have "demand (\<N>\<lbrace>\<Gamma>\<rbrace>) (Var x) = Some (Suc (LEAST n. (\<N>\<lbrakk>Var x\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>Suc n\<^esup> \<noteq> \<bottom>))"
    by (rule demand_Suc_Least[OF `demand (\<N>\<lbrace>\<Gamma>\<rbrace>) (Var x) \<noteq> None`])
  also have "\<dots> = Some (Suc (LEAST n. (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>))" by simp
  also have "\<dots> = Option.map Suc (demand (\<N>\<lbrace>\<Gamma>\<rbrace>) e)"
    using False by (simp add: demand_def)
  finally
  show ?thesis.
qed

lemma demand_Var_there:
  assumes "demand \<rho> (Var x) \<noteq> None"
  shows "x \<in> fdom \<rho>"
proof-
  from assms obtain n where *: "(\<N>\<lbrakk>Var x\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
    by (metis not_bot_demand order_refl)
  hence "n \<noteq> 0" by (auto intro: ccontr)
  from * not0_implies_Suc[OF this]
   show ?thesis by (auto intro: ccontr)
qed

lemma demand_Lam:
  assumes "atom x \<sharp> \<rho>"
  shows "demand \<rho> (Lam [x]. e') = Some 1"
proof-
  from assms
  have "(\<N>\<lbrakk>Lam [x]. e'\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>1\<^esup> \<noteq> \<bottom>" by simp
  hence "demand \<rho> (Lam [x]. e') \<noteq> None" and "the (demand \<rho> (Lam [x]. e')) \<le> 1"
    by (metis not_bot_demand)+
  with demand_not_0[where \<rho> = \<rho> and e = "Lam [x]. e'"]
  show ?thesis by auto
qed

lemma demand_App:
  shows "demand \<rho> (App e x) = undefined"
proof(cases "demand \<rho> (App e x) = None")
  case False
  hence "demand \<rho> (App e x) = Some (Suc (LEAST n. (\<N>\<lbrakk>App e x\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>Suc n\<^esup> \<noteq> \<bottom>))" by (rule demand_Suc_Least)
  also have "\<dots> = Some (Suc (LEAST n. ((\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn (\<rho> f!\<^sub>\<bottom> x))\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>))" by simp
  oops


lemma
  assumes "n < the (demand \<rho> (Var x))"
  assumes "demand \<rho> e = Some n"
  shows higher_demand_ignore: "demand \<rho> e = demand (fmap_delete x \<rho>) e"
using assms
proof(induction n arbitrary: \<rho> e)
  case 0
  from `demand \<rho> e = Some 0`
  have False by (metis demand_not_0)
  thus ?case..
next
  case (Suc n)
  note d = `distinctVars \<Gamma>`
  have "n < the (demand \<Gamma> (Var x))" using Suc(3) by simp
  note prems = d this

  show ?case
  proof(cases e rule:exp_assn.strong_exhaust(1)[where c= \<Gamma>, case_names Var App Let Lam])
    case (Var v)
    note d2 = distinctVars_delete[OF d]

    from Suc(3,4)[unfolded Var]
    have "v \<noteq> x" by auto

    from Suc(4)[unfolded Var]
    have [simp]: "v \<in> heapVars \<Gamma>" by (auto intro: demand_Var_there)
    then obtain e' where e': "(v,e') \<in> set \<Gamma>" by (auto simp add: heapVars_def)
    with `v \<noteq> x` have e'': "(v, e') \<in> set (delete x \<Gamma>)" by (metis d distinctVars_map_of map_of_SomeD map_of_delete)

    from Suc.prems(3)
    have "demand \<Gamma> e' = Some n"  unfolding Var demand_Var[OF d e'] by simp
    hence "demand \<Gamma> e' = demand (delete x \<Gamma>) e'"
      by (rule Suc.IH[OF prems])
    thus ?thesis
      unfolding Var demand_Var[OF d e']  demand_Var[OF d2 e'']
      by simp
  next
    case (Lam v e')
    hence "atom v \<sharp> \<Gamma>" by (simp add: fresh_star_def)
    moreover
    hence "atom v \<sharp> delete x \<Gamma>" by (rule fresh_delete)
    ultimately
    show ?thesis
      unfolding Lam by (simp only: demand_Lam)
  next
    case (Let e' v)
    show ?thesis
    
    
    
  

  

lemma add_BH:
  assumes "distinctVars \<Gamma>"
  assumes "(x, e) \<in> set \<Gamma>"
  assumes  "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
  shows "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
proof-
  from assms
  have "(\<N>\<lbrakk>Var x\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>Suc n\<^esup> \<noteq> \<bottom>"
    by (simp add: distinctVars_map_of heapVars_from_set)
  hence "demand \<Gamma> (Var x) \<noteq> None"  unfolding not_bot_demand by auto

  from `demand \<Gamma> (Var x) \<noteq> None` demand_Var[OF assms(1,2)]
  have "the (demand \<Gamma> (Var x)) = Suc (the (demand \<Gamma> e))" by auto
  hence "the (demand \<Gamma> e) < the (demand \<Gamma> (Var x))" by simp
  hence "demand \<Gamma> e = demand (delete x \<Gamma>) e" sorry
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
    hence "(\<N>\<lbrakk>?e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by (rule add_BH)
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
      by (simp add: sharp_Env del: CESem.simps)
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
    from Suc.IH[OF this]
    obtain \<Delta> v where "asToHeap as @ \<Gamma> : e' \<Down>\<^bsub>S\<^esub> \<Delta> : v" by blast
    hence "\<Gamma> : Let as e' \<Down>\<^bsub>S\<^esub> \<Delta> : v"
      by (rule reds.Let[OF Let(1)])
    thus ?thesis using Let by auto
  qed
qed

end

