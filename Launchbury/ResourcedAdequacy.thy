theory ResourcedAdequacy
imports "ResourcedDenotational" "Launchbury" "DistinctVars" "CorrectnessResourced"
begin

lemma demand_not_0: "demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>) \<noteq> \<bottom>"
proof
  assume "demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>) = \<bottom>"
  with demand_suffices'[where n = 0, simplified, OF this]
  have "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>\<bottom> \<noteq> \<bottom>" by simp
  thus False by simp
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
    apply (simp del: fmap_C_restr_lookup)
    apply (rule C_restr_cong)
    apply (case_tac r', simp)
    apply simp
    apply (rule cfun_eqI)
    apply simp
    apply (rule below_antisym)
    defer
    apply (rule cont2monofunE[OF _ fmap_C_restr_restr_below])
    apply (simp del: fun_upd_apply)
    apply (subst Lam(1))
    apply simp
    apply (intro monofun_cfun below_refl monofun_cfun_arg fun_upd_mono Cpred_below )
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
    apply (simp del: C_restr.simps fmap_C_restr_lookup)
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
    apply (rule ext)
    apply (subst (1 3) fmap_C_restr_lookup)
    apply (case_tac "x \<in> heapVars (asToHeap as)")
    apply (simp add: lookupHeapToEnv del: fmap_C_restr_lookup)
    apply (subst (1 2) Let(1), assumption)
    apply (drule fmap_restr_eq_Cpred)
    apply simp
    apply simp
    done

  show ?case
    apply (rule below_antisym)
    defer apply (rule cont2monofunE[OF _ fmap_C_restr_restr_below], simp)
    apply (cases r, simp  del: fmap_C_restr_lookup)
    apply (simp  del: fmap_C_restr_lookup)
    apply (subst (1 4) Rep_cfun_inverse) (* Be careful not to destroy the locale parameters *)
    apply (subst (1 2) Let(2))
    apply (subst *)
    apply (rule cont2monofunE[OF _ Cpred_below], simp)
    done
qed

lemma can_restrict_heap:
  "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r = (\<N>\<lbrakk>e\<rbrakk>\<^bsub>fmap_C_restr\<cdot>(Cpred\<cdot>r)\<cdot>\<rho>\<^esub>)\<cdot>r"
  by (rule C_restr_eqD[OF restr_can_restrict_heap below_refl])

lemma add_BH:
  assumes "map_of \<Gamma> x = Some e"
  assumes  "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
  shows "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
proof-
  let ?C = "demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)"

  from  assms(2)
  have "?C \<sqsubseteq> C\<^bsup>n\<^esup>" unfolding not_bot_demand by simp

  from assms(1)
  have [simp]: "the (map_of \<Gamma> x) = e" by (metis the.simps)

  from assms(1)
  have [simp]: "x \<in> heapVars \<Gamma>" by (metis domIff dom_map_of_conv_heapVars not_Some_eq)

  have "fmap_C_restr\<cdot>(Cpred\<cdot>?C)\<cdot>(\<N>\<lbrace>\<Gamma>\<rbrace>) \<sqsubseteq> (\<N>\<lbrace>delete x \<Gamma>\<rbrace>) \<and> \<N>\<lbrace>\<Gamma>\<rbrace> \<sqsubseteq> \<N>\<lbrace>\<Gamma>\<rbrace>"
    apply (rule HSem_ind) back back back back back back back back back
    apply (intro adm_lemmas cont2cont)
    apply (simp del: app_strict  del: fmap_C_restr_lookup)
    apply (erule conjE)
    apply rule
    apply (rule fun_belowI)
    apply (case_tac "xa = x")
    apply (subst (1) fmap_C_restr_lookup)
    apply (simp add: lookupHeapToEnv lookup_HSem_other del: app_strict fmap_C_restr_lookup)
    apply (subst app_strict)
    apply (simp del: app_strict fmap_C_restr_lookup)
    apply (rule C_restr_bot_demand)
    apply (subst C_Cpred_id[OF demand_not_0])
    apply (erule demand_contravariant[OF monofun_cfun_arg])

    apply (case_tac "xa \<in> heapVars \<Gamma>")
    apply (simp add: lookupHeapToEnv lookup_HSem_heap del: app_strict fmap_C_restr_lookup)
    apply (subst (1) fmap_C_restr_lookup)
    apply (simp add: lookupHeapToEnv lookup_HSem_heap del: app_strict fmap_C_restr_lookup)
    apply (subst restr_can_restrict_heap)
    apply (rule below_trans[OF C_restr_below])
    apply (rule below_trans[OF monofun_cfun_arg eq_imp_below])
    apply (erule below_trans[OF monofun_cfun_fun[OF monofun_cfun_arg[OF Cpred_below]]])
    apply (rule refl)
    
    apply (simp del: app_strict)

    apply (subst HSem_eq)
    apply (erule cont2monofunE[rotated])
    apply simp
    done
  hence heaps: "fmap_C_restr\<cdot>(Cpred\<cdot>?C)\<cdot>(\<N>\<lbrace>\<Gamma>\<rbrace>) \<sqsubseteq> \<N>\<lbrace>delete x \<Gamma>\<rbrace>"..

  from assms(2)
  have "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>?C \<noteq> \<bottom>"
    by (rule demand_suffices[OF infinite_resources_suffice])
  also
  have "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>?C = (\<N>\<lbrakk>e\<rbrakk>\<^bsub>fmap_C_restr\<cdot>(Cpred\<cdot>?C)\<cdot>(\<N>\<lbrace>\<Gamma>\<rbrace>)\<^esub>)\<cdot>?C"
    by (rule can_restrict_heap)
  also
  have "\<dots> \<sqsubseteq> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<^esub>)\<cdot>?C"
    by (intro monofun_cfun_arg monofun_cfun_fun heaps )
  also
  have "\<dots> \<sqsubseteq> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup>"
    using `?C \<sqsubseteq> C\<^bsup>n\<^esup>` by (rule monofun_cfun_arg)
  finally
  show ?thesis.
qed

lemma ESem_Lam_not_bot[simp]:
  assumes  "(\<N>\<lbrakk> Lam [z]. e \<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>c \<noteq> \<bottom>"
  shows "(\<N>\<lbrakk> Lam [z]. e \<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>c \<sqsubseteq> CFn\<cdot>(\<Lambda> v. \<N>\<lbrakk>e\<rbrakk>\<^bsub>\<sigma>(z := v)\<^esub>)"
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
    have "x \<in> heapVars \<Gamma>" 
      by (auto intro: ccontr simp add: lookup_HSem_other)
    hence "map_of \<Gamma> x = Some ?e" by (induction \<Gamma>) auto
    moreover
    from Suc.prems[unfolded Var] `map_of \<Gamma> x = Some ?e` `x \<in> heapVars \<Gamma>`
    have "(\<N>\<lbrakk>?e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by (auto simp add: lookup_HSem_heap  simp del: app_strict)
    hence "(\<N>\<lbrakk>?e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by (rule add_BH[OF `map_of \<Gamma> x = Some ?e`])
    from Suc.IH[OF this]
    obtain \<Delta> v where "delete x \<Gamma> : ?e \<Down>\<^bsub>x # S\<^esub> \<Delta> : v" by blast
    ultimately
    have "\<Gamma> : (Var x) \<Down>\<^bsub>S\<^esub> (x,v) #  \<Delta> : v" by (rule Variable)
    thus ?thesis using Var by auto
  next
  case (App e' x)
    have "finite (set S \<union> fv (\<Gamma>, e'))" by simp
    from finite_list[OF this]
    obtain S' where S': "set S' = set S \<union> fv (\<Gamma>, e')"..

    from Suc.prems[unfolded App]
    have prem: "((\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn  C_restr\<cdot>C\<^bsup>n\<^esup>\<cdot>((\<N>\<lbrace>\<Gamma>\<rbrace>) x))\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by (auto simp del: app_strict)
    hence e'_not_bot: "(\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by auto
    from Suc.IH[OF this]
    obtain \<Delta> v where lhs': "\<Gamma> : e' \<Down>\<^bsub>x#S'\<^esub> \<Delta> : v" by blast 

    from result_evaluated_fresh[OF lhs']
    obtain y e'' where n': "v = (Lam [y]. e'')" and "atom y \<sharp> (\<Gamma>, e', x, S', \<Delta>)" by blast
    with lhs'
    have lhs: "\<Gamma> : e' \<Down>\<^bsub>x # S'\<^esub> \<Delta> : Lam [y]. e''" by simp

    from `atom y \<sharp> _` have "y \<notin> heapVars \<Delta>" by (metis (full_types) fresh_Pair heapVars_not_fresh)
   
    have "fv (\<Gamma>, e') \<subseteq> set (x # S')" using S' by auto
    from correctness_empty_env[OF lhs this]
    have correct1: "\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub> \<sqsubseteq> \<N>\<lbrakk>Lam [y]. e''\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>" and correct2: "\<N>\<lbrace>\<Gamma>\<rbrace> \<sqsubseteq> \<N>\<lbrace>\<Delta>\<rbrace>" by auto

    note e'_not_bot
    also note monofun_cfun_fun[OF correct1]
    finally have lam_not_bot: "(\<N>\<lbrakk>Lam [y]. e''\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>".

    have "((\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn C_restr\<cdot>C\<^bsup>n\<^esup>\<cdot>((\<N>\<lbrace>\<Gamma>\<rbrace>) x))\<cdot>C\<^bsup>n\<^esup>
          \<sqsubseteq> ((\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn ((\<N>\<lbrace>\<Gamma>\<rbrace>) x))\<cdot>C\<^bsup>n\<^esup>"
          by (rule cont2monofunE[OF _ C_restr_below], simp)
    also have "\<dots>  \<sqsubseteq> ((\<N>\<lbrakk>Lam [y]. e''\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn ((\<N>\<lbrace>\<Gamma>\<rbrace>) x))\<cdot>C\<^bsup>n\<^esup>"
      by (intro monofun_cfun_arg monofun_cfun_fun correct1)
    also have "\<dots> \<sqsubseteq> ((\<N>\<lbrakk>Lam [y]. e''\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn ((\<N>\<lbrace>\<Delta>\<rbrace>) x))\<cdot>C\<^bsup>n\<^esup>"
      by (intro monofun_cfun_arg monofun_cfun_fun fun_belowD[OF correct2])
    also have "\<dots> \<sqsubseteq> (CFn\<cdot>(\<Lambda> v. \<N>\<lbrakk>e''\<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>)(y := v)\<^esub>) \<down>CFn ((\<N>\<lbrace>\<Delta>\<rbrace>) x))\<cdot>C\<^bsup>n\<^esup>"
      by (rule cont2monofunE[OF _ ESem_Lam_not_bot[OF lam_not_bot]]) simp
    also have "\<dots> = (\<N>\<lbrakk>e''\<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>)(y := ((\<N>\<lbrace>\<Delta>\<rbrace>) x))\<^esub>)\<cdot>C\<^bsup>n\<^esup>"
      using  `y \<notin> heapVars \<Delta>` by simp
    also have "\<dots> = (\<N>\<lbrakk>e''[y::=x]\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup>"
      apply (rule arg_cong[OF ESem_subst])
      using `atom y \<sharp> _` by (simp_all add: fresh_Pair fresh_at_base)
    finally
    have "\<dots> \<noteq> \<bottom>" using prem by auto
    then
    obtain \<Theta> v' where rhs: "\<Delta> : e''[y::=x] \<Down>\<^bsub>S'\<^esub> \<Theta> : v'" using Suc.IH by blast
    
    have "\<Gamma> : App e' x \<Down>\<^bsub>S'\<^esub> \<Theta> : v'"
      by (rule reds_ApplicationI[OF `atom y \<sharp> _` lhs rhs])
    hence "\<Gamma> : App e' x \<Down>\<^bsub>S\<^esub> \<Theta> : v'"
      apply (rule reds_smaller_L) using S' by auto
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
      by (simp add: fresh_star_Pair del: app_strict) 
    also have "\<N>\<lbrace>asToHeap as\<rbrace>\<N>\<lbrace>\<Gamma>\<rbrace> = \<N>\<lbrace>asToHeap as @ \<Gamma>\<rbrace>"
      apply (rule HSem_merge)
      using Let(1)
      by (auto simp add: fresh_star_Pair set_bn_to_atom_heapVars)
    finally 
    have "(\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>asToHeap as @ \<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>".
    }
    then
    obtain \<Delta> v where "asToHeap as @ \<Gamma> : e' \<Down>\<^bsub>S\<^esub> \<Delta> : v" using Suc.IH by blast
    hence "\<Gamma> : Let as e' \<Down>\<^bsub>S\<^esub> \<Delta> : v"
      by (rule reds.Let[OF Let(1)])
    thus ?thesis using Let by auto
  qed
qed

theorem resourced_adequacy:
  assumes "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>r \<noteq> \<bottom>"
  shows "\<exists> \<Delta> v. \<Gamma> : e \<Down>\<^bsub>S\<^esub> \<Delta> : v"
  by (rule finite_resources_suffice[OF infinite_resources_suffice[OF assms(1)]])
     (erule adequacy_finite)
end
