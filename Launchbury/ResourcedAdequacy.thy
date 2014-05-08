theory ResourcedAdequacy
imports "ResourcedDenotational" "Launchbury" "AList-Utils" "CorrectnessResourced"
begin

lemma demand_not_0: "demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>) \<noteq> \<bottom>"
proof
  assume "demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>) = \<bottom>"
  with demand_suffices'[where n = 0, simplified, OF this]
  have "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>\<bottom> \<noteq> \<bottom>" by simp
  thus False by simp
qed

text {*
The semantics of an expression, given only @{term r} resources, will only use values from the
environment with less resources.
*}

lemma restr_can_restrict_env: "(\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>)|\<^bsub>r\<^esub> = (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)|\<^bsub>r\<^esub>"
proof(induction e arbitrary: \<rho> r rule: exp_induct)
  case (Var x)
  show ?case
  proof(rule C_restr_cong)
    fix r'
    assume "r' \<sqsubseteq> r"
    {
      fix r''
      assume "r' = C\<cdot>r''" with `r' \<sqsubseteq> r`
      have "(Cpred\<cdot>r \<sqinter> r'') = r''"
        by (metis Cpred.simps below_refl is_meetI monofun_cfun_arg)
      hence "\<rho> x\<cdot>r'' = (\<rho> x|\<^bsub>Cpred\<cdot>r\<^esub>)\<cdot>r''" by simp
    }
    thus "(\<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r' = (\<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r'"
      unfolding CESem_simps
      by -(rule C_case_cong, simp)
  qed
next
  case (Lam x e)
  show ?case
  proof(rule C_restr_cong)
    fix r'
    assume "r' \<sqsubseteq> r"
    {
      fix r''
      fix v
      assume "r' = C\<cdot>r''"
      with `r' \<sqsubseteq> r`
      have [simp]: "r'' \<sqinter> Cpred\<cdot>r = r''"
        by (metis C.inverts C_Cpred_id below_refl is_meetI meet_above_iff meet_bot2)

      have "r'' \<sqsubseteq> r" by (metis `r' = C\<cdot>r''` `r' \<sqsubseteq> r` below_C below_trans)
      hence "(\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x := v|\<^bsub>r''\<^esub>)\<^esub>)|\<^bsub>r''\<^esub> = (\<N>\<lbrakk> e \<rbrakk>\<^bsub>(\<rho>(x := v|\<^bsub>r''\<^esub>))|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)|\<^bsub>r''\<^esub>"
        by (rule C_restr_eq_lower[OF Lam])
      also have "(\<rho>(x := v|\<^bsub>r''\<^esub>))|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub> = (\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>)(x := v|\<^bsub>r''\<^esub>)"  by simp
      finally
      have "(\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x := v|\<^bsub>r''\<^esub>)\<^esub>)|\<^bsub>r''\<^esub> = (\<N>\<lbrakk> e \<rbrakk>\<^bsub>(\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>)(x := v|\<^bsub>r''\<^esub>)\<^esub>)|\<^bsub>r''\<^esub>".
    }
    thus "(\<N>\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r' = (\<N>\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r'"
      unfolding CESem_simps
      by -(rule C_case_cong, simp)
  qed
next
  case (App e x)
  show ?case
  proof (rule C_restr_cong)
    fix r'
    assume "r' \<sqsubseteq> r"
    {
      fix r''
      assume "r' = C\<cdot>r''" with `r' \<sqsubseteq> r`
      have ** : "(Cpred\<cdot>r \<sqinter> r'') = r''"
        by (metis Cpred.simps below_refl is_meetI monofun_cfun_arg)

      have "r'' \<sqsubseteq> r" by (metis `r' = C\<cdot>r''` `r' \<sqsubseteq> r` below_C below_trans)
      hence *: "(\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r'' = (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r''"
        by (rule C_restr_eqD[OF App])

      note * **
    }
    thus "(\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r' = (\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r'"
      unfolding CESem_simps
      by -(rule C_case_cong, simp)
  qed
next
  case (Let as e)

  txt {* The lemma, lifted to heaps *}
  have restr_can_restrict_env_heap : "\<And> r. (\<N>\<lbrace>as\<rbrace>\<rho>)|\<^sup>\<circ>\<^bsub>r\<^esub> = (\<N>\<lbrace>as\<rbrace>\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>)|\<^sup>\<circ>\<^bsub>r\<^esub>"
  proof(rule has_ESem.parallel_HSem_ind)
    fix \<rho>\<^sub>1 \<rho>\<^sub>2 :: CEnv and r :: C
    assume "\<rho>\<^sub>1|\<^sup>\<circ>\<^bsub>r\<^esub> = \<rho>\<^sub>2|\<^sup>\<circ>\<^bsub>r\<^esub>"
    hence "\<rho>\<^sub>1|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub> = \<rho>\<^sub>2|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>" by (metis env_restr_eq_Cpred)

    show " (\<rho> ++\<^bsub>domA as\<^esub> \<^bold>\<N>\<lbrakk> as \<^bold>\<rbrakk>\<^bsub>\<rho>\<^sub>1\<^esub>)|\<^sup>\<circ>\<^bsub>r\<^esub> = (\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub> ++\<^bsub>domA as\<^esub> \<^bold>\<N>\<lbrakk> as \<^bold>\<rbrakk>\<^bsub>\<rho>\<^sub>2\<^esub>)|\<^sup>\<circ>\<^bsub>r\<^esub>"
    proof(rule env_C_restr_cong)
      fix x and r'
      assume "r' \<sqsubseteq> r"

      show "(\<rho> ++\<^bsub>domA as\<^esub> \<^bold>\<N>\<lbrakk> as \<^bold>\<rbrakk>\<^bsub>\<rho>\<^sub>1\<^esub>) x\<cdot>r' = (\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub> ++\<^bsub>domA as\<^esub> \<^bold>\<N>\<lbrakk> as \<^bold>\<rbrakk>\<^bsub>\<rho>\<^sub>2\<^esub>) x\<cdot>r'"
      proof(cases "x \<in> domA as")
        case True
        have "(\<N>\<lbrakk> the (map_of as x) \<rbrakk>\<^bsub>\<rho>\<^sub>1\<^esub>)\<cdot>r' = (\<N>\<lbrakk> the (map_of as x) \<rbrakk>\<^bsub>\<rho>\<^sub>1|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r'"
          by (rule C_restr_eqD[OF Let(1)[OF True] `r' \<sqsubseteq> r`])
        also have "\<dots> = (\<N>\<lbrakk> the (map_of as x) \<rbrakk>\<^bsub>\<rho>\<^sub>2|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r'"
          unfolding `\<rho>\<^sub>1|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub> = \<rho>\<^sub>2|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>`..
        also have "\<dots>   = (\<N>\<lbrakk> the (map_of as x) \<rbrakk>\<^bsub>\<rho>\<^sub>2\<^esub>)\<cdot>r'"
          by (rule C_restr_eqD[OF Let(1)[OF True] `r' \<sqsubseteq> r`, symmetric])
        finally
        show ?thesis using True by (simp add: lookupEvalHeap)
      next
        case False
        from `r' \<sqsubseteq> r` have "(r \<sqinter> r') = r'" by (metis below_refl is_meetI)
        thus ?thesis using False by simp
      qed
    qed
  qed simp_all

  show ?case
  proof (rule C_restr_cong)
    fix r'
    assume "r' \<sqsubseteq> r"
    {
      fix r''
      assume "r' = C\<cdot>r''" with `r' \<sqsubseteq> r`
      have ** : "(Cpred\<cdot>r \<sqinter> r'') = r''"
        by (metis Cpred.simps below_refl is_meetI monofun_cfun_arg)

      have "r'' \<sqsubseteq> r" by (metis `r' = C\<cdot>r''` `r' \<sqsubseteq> r` below_C below_trans)

      have "(\<N>\<lbrace>as\<rbrace>\<rho>)|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub> = (\<N>\<lbrace>as\<rbrace>(\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>))|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>"
        by (rule restr_can_restrict_env_heap)
      hence "(\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>as\<rbrace>\<rho>\<^esub>)\<cdot>r'' = (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>as\<rbrace>\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r''"
        by (subst (1 2)  C_restr_eqD[OF Let(2) `r'' \<sqsubseteq> r`]) simp
    }
    thus " (\<N>\<lbrakk> Let as e \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r' = (\<N>\<lbrakk> Let as e \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r'"
      unfolding CESem_simps
      by -(rule C_case_cong, simp)
  qed
qed

lemma can_restrict_env:
  "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r =  (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>Cpred\<cdot>r\<^esub>\<^esub>)\<cdot>r"
  by (rule C_restr_eqD[OF restr_can_restrict_env below_refl])

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
  have [simp]: "x \<in> domA \<Gamma>" by (metis domIff dom_map_of_conv_domA not_Some_eq)

  have "(\<N>\<lbrace>\<Gamma>\<rbrace>)|\<^sup>\<circ>\<^bsub>Cpred\<cdot>?C\<^esub> \<sqsubseteq> \<N>\<lbrace>delete x \<Gamma>\<rbrace> \<and> \<N>\<lbrace>\<Gamma>\<rbrace> \<sqsubseteq> \<N>\<lbrace>\<Gamma>\<rbrace>"
    apply (rule HSem_ind) back back back back back back back back back
    apply (intro adm_lemmas cont2cont)
    apply (simp del: app_strict  del: env_C_restr_lookup)
    apply (erule conjE)
    apply rule
    apply (rule fun_belowI)
    apply (case_tac "xa = x")
    apply (subst (1) env_C_restr_lookup)
    apply (simp add: lookupEvalHeap lookup_HSem_other del: app_strict env_C_restr_lookup)
    apply (subst app_strict)
    apply (simp del: app_strict env_C_restr_lookup)
    apply (rule C_restr_bot_demand)
    apply (subst C_Cpred_id[OF demand_not_0])
    apply (erule demand_contravariant[OF monofun_cfun_arg])

    apply (case_tac "xa \<in> domA \<Gamma>")
    apply (simp add: lookupEvalHeap lookup_HSem_heap del: app_strict env_C_restr_lookup)
    apply (subst (1) env_C_restr_lookup)
    apply (simp add: lookupEvalHeap lookup_HSem_heap del: app_strict env_C_restr_lookup)
    apply (subst restr_can_restrict_env)
    apply (rule below_trans[OF C_restr_below])
    apply (rule below_trans[OF monofun_cfun_arg eq_imp_below])
    apply (erule below_trans[OF monofun_cfun_fun[OF monofun_cfun_arg[OF Cpred_below]]])
    apply (rule refl)
    
    apply (simp del: app_strict)

    apply (subst HSem_eq)
    apply (erule cont2monofunE[rotated])
    apply simp
    done
  hence heaps: "(\<N>\<lbrace>\<Gamma>\<rbrace>)|\<^sup>\<circ>\<^bsub>Cpred\<cdot>?C\<^esub> \<sqsubseteq> \<N>\<lbrace>delete x \<Gamma>\<rbrace>"..

  from assms(2)
  have "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>?C \<noteq> \<bottom>"
    by (rule demand_suffices[OF infinite_resources_suffice])
  also
  have "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>?C = (\<N>\<lbrakk>e\<rbrakk>\<^bsub>(\<N>\<lbrace>\<Gamma>\<rbrace>)|\<^sup>\<circ>\<^bsub>Cpred\<cdot>?C\<^esub>\<^esub>)\<cdot>?C"
    by (rule can_restrict_env)
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
  proof(cases e rule:exp_strong_exhaust(1)[where c = "(\<Gamma>,S)", case_names Var App Let Lam])
  case (Var x)
    let ?e = "the (map_of \<Gamma> x)"
    from Suc.prems[unfolded Var]
    have "x \<in> domA \<Gamma>" 
      by (auto intro: ccontr simp add: lookup_HSem_other)
    hence "map_of \<Gamma> x = Some ?e" by (induction \<Gamma>) auto
    moreover
    from Suc.prems[unfolded Var] `map_of \<Gamma> x = Some ?e` `x \<in> domA \<Gamma>`
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
    have prem: "((\<N>\<lbrakk> e' \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn (\<N>\<lbrace>\<Gamma>\<rbrace>) x|\<^bsub>C\<^bsup>n\<^esup>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by (auto simp del: app_strict)
    hence e'_not_bot: "(\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by auto
    from Suc.IH[OF this]
    obtain \<Delta> v where lhs': "\<Gamma> : e' \<Down>\<^bsub>x#S'\<^esub> \<Delta> : v" by blast 

    from result_evaluated_fresh[OF lhs']
    obtain y e'' where n': "v = (Lam [y]. e'')" and "atom y \<sharp> (x, \<Delta>)" by blast
    with lhs'
    have lhs: "\<Gamma> : e' \<Down>\<^bsub>x # S'\<^esub> \<Delta> : Lam [y]. e''" by simp

    from `atom y \<sharp> _` have "y \<notin> domA \<Delta>" by (metis (full_types) fresh_Pair domA_not_fresh)
   
    have "fv (\<Gamma>, e') \<subseteq> set (x # S')" using S' by auto
    from correctness_empty_env[OF lhs this]
    have correct1: "\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub> \<sqsubseteq> \<N>\<lbrakk>Lam [y]. e''\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>" and correct2: "\<N>\<lbrace>\<Gamma>\<rbrace> \<sqsubseteq> \<N>\<lbrace>\<Delta>\<rbrace>" by auto

    note e'_not_bot
    also note monofun_cfun_fun[OF correct1]
    finally have lam_not_bot: "(\<N>\<lbrakk>Lam [y]. e''\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>".

    have "((\<N>\<lbrakk> e' \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn (\<N>\<lbrace>\<Gamma>\<rbrace>) x|\<^bsub>C\<^bsup>n\<^esup>\<^esub>)\<cdot>C\<^bsup>n\<^esup>
          \<sqsubseteq> ((\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn ((\<N>\<lbrace>\<Gamma>\<rbrace>) x))\<cdot>C\<^bsup>n\<^esup>"
          by (rule cont2monofunE[OF _ C_restr_below], simp)
    also have "\<dots>  \<sqsubseteq> ((\<N>\<lbrakk>Lam [y]. e''\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn ((\<N>\<lbrace>\<Gamma>\<rbrace>) x))\<cdot>C\<^bsup>n\<^esup>"
      by (intro monofun_cfun_arg monofun_cfun_fun correct1)
    also have "\<dots> \<sqsubseteq> ((\<N>\<lbrakk>Lam [y]. e''\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<down>CFn ((\<N>\<lbrace>\<Delta>\<rbrace>) x))\<cdot>C\<^bsup>n\<^esup>"
      by (intro monofun_cfun_arg monofun_cfun_fun fun_belowD[OF correct2])
    also have "\<dots> \<sqsubseteq> (CFn\<cdot>(\<Lambda> v. \<N>\<lbrakk>e''\<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>)(y := v)\<^esub>) \<down>CFn ((\<N>\<lbrace>\<Delta>\<rbrace>) x))\<cdot>C\<^bsup>n\<^esup>"
      by (rule cont2monofunE[OF _ ESem_Lam_not_bot[OF lam_not_bot]]) simp
    also have "\<dots> = (\<N>\<lbrakk>e''\<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>)(y := ((\<N>\<lbrace>\<Delta>\<rbrace>) x))\<^esub>)\<cdot>C\<^bsup>n\<^esup>"
      using  `y \<notin> domA \<Delta>` by simp
    also have "\<dots> = (\<N>\<lbrakk>e''[y::=x]\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup>"
      apply (rule arg_cong[OF ESem_subst])
      using `atom y \<sharp> _` by (simp_all add: fresh_Pair fresh_at_base)
    finally
    have "\<dots> \<noteq> \<bottom>" using prem by auto
    then
    obtain \<Theta> v' where rhs: "\<Delta> : e''[y::=x] \<Down>\<^bsub>S'\<^esub> \<Theta> : v'" using Suc.IH by blast
    
    have "\<Gamma> : App e' x \<Down>\<^bsub>S'\<^esub> \<Theta> : v'"
      by (rule reds_ApplicationI[OF lhs rhs])
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
    have prem: "(\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>as\<rbrace>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" 
      by (simp add: fresh_star_Pair del: app_strict) 
    also have "\<N>\<lbrace>as\<rbrace>\<N>\<lbrace>\<Gamma>\<rbrace> = \<N>\<lbrace>as @ \<Gamma>\<rbrace>"
      apply (rule HSem_merge)
      using Let(1)
      by (auto simp add: fresh_star_Pair set_bn_to_atom_domA)
    finally 
    have "(\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>as @ \<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>".
    }
    then
    obtain \<Delta> v where "as @ \<Gamma> : e' \<Down>\<^bsub>S\<^esub> \<Delta> : v" using Suc.IH by blast
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
