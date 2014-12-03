theory RedsImprovesArityAnalysis
imports ArityAnalysisFix Launchbury
begin

context CorrectArityAnalysisAfix
begin
lemma Aexp'_Let: "Afix as\<cdot>(Aexp' e\<cdot>n) f|` (- domA as) \<sqsubseteq> Aexp' (Terms.Let as e)\<cdot>n"
  by (cases n) (simp_all add: Aexp_Let)

lemma  reds_improves_arity':
       "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : v \<Longrightarrow>
        edom ae \<subseteq> set L \<Longrightarrow> 
        Afix \<Delta> \<cdot> (Aexp' v \<cdot> n \<squnion> ae) f|` (- (domA \<Delta> - domA \<Gamma>)) \<sqsubseteq> Afix \<Gamma> \<cdot> (Aexp' e \<cdot> n \<squnion> ae) f|` (- (domA \<Delta> - domA \<Gamma>))"
proof(induct arbitrary: ae n rule: reds.induct)
case Lambda
  show ?case by simp
next
case (Variable \<Gamma> x e L \<Delta> z ae n)
  have reorder: "map_of ((x, e) # delete x \<Gamma>) = map_of \<Gamma>" by (rule map_of_delete_insert[OF Variable.hyps(1)])

  from `edom ae \<subseteq> set L`
  have prem: "edom ae \<subseteq> set (x#L)" by auto

  from `map_of \<Gamma> x = Some e` have [simp]: "x \<in> domA \<Gamma>" by (metis domA_from_set map_of_is_SomeD)

  have "x \<notin> domA \<Delta>" by (rule reds_avoids_live[OF Variable(2), where x = x]) simp_all
  hence [simp]:"delete x \<Delta> = \<Delta>" by simp

  note IH =  Variable(3)
  let "?S" = "(- (domA ((x, z) # \<Delta>) - domA \<Gamma>))"

  have "Afix ((x, z) # \<Delta>) \<cdot> (Aexp' z\<cdot>n \<squnion> ae)  f|` ?S = (\<mu> ae'. Aexp' z\<cdot>(ae' x) \<squnion> ABinds \<Delta> \<cdot> ae' \<squnion> Aexp' z\<cdot>n \<squnion> ae) f|` ?S"
    unfolding Afix_eq by simp
  also have "\<dots> \<sqsubseteq> (\<mu> ae'. ABinds \<Delta> \<cdot> ae' \<squnion> (Aexp' z\<cdot>(n \<squnion> ae' x) \<squnion> ae)) f|` ?S"
    by (auto intro!: env_restr_mono monofun_cfun_arg cfun_belowI join_mono[OF below_refl] join_mono[OF _ below_refl] cfun_join_below simp del: join_assoc)
  also have "\<dots> = (\<mu> ae'. Afix \<Delta> \<cdot> ae' \<squnion> (Aexp' z\<cdot>(n \<squnion> ae' x) \<squnion> ae))  f|` ?S"
    apply (rule arg_cong[where f = "\<lambda> x. x f|` ?S"] )
    apply (rule fix_eq_fix, simp_all)

    apply (subst fix_eq) back back apply simp_all
    apply (intro join_below)
    apply (simp add: below_trans[OF _ join_above2]  below_trans[OF _ join_above1])
    apply (simp add: below_trans[OF _ join_above2]  below_trans[OF _ join_above1] monofun_cfun_fun[OF Abinds_below_Afix])
    apply (simp add: below_trans[OF _ join_above2]  below_trans[OF _ join_above1])

    apply (intro join_below)
    apply (subst fix_eq, simp)
    apply (subst Afix_eq)
    apply (rule fix_least_below, simp)
    
    apply (subst fix_eq) back apply simp
    apply (simp add: below_trans[OF _ join_above2]  below_trans[OF _ join_above1])
    apply (subst fix_eq) back apply simp
    apply (simp add: below_trans[OF _ join_above2]  below_trans[OF _ join_above1])
    done
  also have "\<dots> = (\<mu> ae'. Afix \<Delta> \<cdot> (Aexp' z\<cdot>(n \<squnion> ae' x) \<squnion> ae)) f|` ?S"
    apply (rule arg_cong[where f = "\<lambda> x. x f|` ?S"] )
    apply (rule fix_eq_fix, simp_all)
    
    apply (subst fix_eq) back back apply simp_all
    apply (intro join_below)
    apply (simp add: below_trans[OF _ join_above2]  below_trans[OF _ join_above1]  below_trans[OF _ Afix_above_arg])
    
    apply (subst Afix_eq)
    apply (rule fix_least_below, simp)
    apply (rule join_below)
    apply (subst fix_eq, simp)
    
    apply (simp add: below_trans[OF _ join_above2]  below_trans[OF _ join_above1] monofun_cfun_fun[OF Abinds_below_Afix])

    apply (subst Afix_eq) back apply simp
    apply (subst fix_eq, simp) back
    apply (simp add: below_trans[OF _ join_above2]  below_trans[OF _ join_above1])

    apply (subst fix_eq, simp) back 
    apply (rule below_trans[OF _ join_above2])
    apply (rule below_trans[OF _ join_above1])
    apply (rule monofun_cfun_arg)
    apply (intro join_below)
    apply (subst fix_eq, simp)
    apply (subst fix_eq, simp) back
    apply (rule below_trans[OF _ join_above2])
    apply (rule below_trans[OF _ join_above2])
    apply rule
    done
    
  also have "\<dots> \<sqsubseteq> (\<mu> ae'. Afix (delete x \<Gamma>) \<cdot> (Aexp' e\<cdot>(n \<squnion> ae' x) \<squnion> ae)) f|` ?S"
  proof (induction rule: parallel_fix_ind[where P ="\<lambda> x y. x f|` ?S \<sqsubseteq> y f|` ?S"])
  case (goal3 aeL aeR)
    have "- (domA ((x, z) # \<Delta>) - domA \<Gamma>) \<subseteq> - (domA \<Delta> - domA (delete x \<Gamma>))"
      using `x \<notin> domA \<Delta>` by auto
    moreover
    note IH[OF prem]
    ultimately have "(Afix \<Delta>\<cdot>(Aexp' z\<cdot>(n \<squnion> aeL x) \<squnion> ae)) f|` ?S \<sqsubseteq> (Afix (delete x \<Gamma>)\<cdot>(Aexp' e\<cdot>(n \<squnion> aeL x) \<squnion> ae)) f|` ?S"
      by (rule env_restr_below_subset)
    also from goal3 have "aeL x \<sqsubseteq>  aeR x" by (rule env_restr_belowD) simp
    finally have "Afix \<Delta>\<cdot>(Aexp' z\<cdot>(n \<squnion> aeL x) \<squnion> ae) f|` ?S \<sqsubseteq> Afix (delete x \<Gamma>)\<cdot>(Aexp' e\<cdot>(n \<squnion> aeR x) \<squnion> ae) f|` ?S" by this simp_all
    thus ?case by simp
  qed simp_all
  also have "\<dots> \<sqsubseteq> (\<mu> ae'. Afix ((x,e)#delete x \<Gamma>) \<cdot> (AE_singleton x \<cdot> (n \<squnion> ae' x) \<squnion> ae))  f|` ?S"
    apply (rule env_restr_mono)
    apply (rule monofun_cfun_arg)
    apply (rule cfun_belowI, simp)
    apply (rule Afix_e_to_heap[simplified])
    done
  also have "\<dots> = Afix ((x,e)#delete x \<Gamma>) \<cdot> (AE_singleton x\<cdot>n \<squnion> ae)  f|` ?S" by (rule arg_cong[OF Afix_repeat_singleton])
  also have "\<dots> \<sqsubseteq> Afix ((x,e)#delete x \<Gamma>) \<cdot> (Aexp' (Var x) \<cdot> n \<squnion> ae)  f|` ?S" by (intro Aexp'_Var monofun_cfun env_restr_mono join_mono below_refl)
  also have "\<dots> = Afix \<Gamma> \<cdot> (Aexp' (Var x)\<cdot>n \<squnion> ae) f|` ?S" by (rule arg_cong[OF Afix_reorder[OF reorder]])
  finally show "Afix ((x, z) # \<Delta>)\<cdot>(Aexp' z\<cdot>n \<squnion> ae) f|` ?S \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp' (Var x)\<cdot>n \<squnion> ae) f|` ?S"
    by this simp_all
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> z e' ae n)
  note prem1 =  `edom ae \<subseteq> set L`
  hence prem2: "edom ae \<subseteq> set (x#L)" by auto
  hence prem3: "edom (AE_singleton x\<cdot>(up\<cdot>0) \<squnion> ae) \<subseteq> set (x#L)" by auto

  have subset1: " (- (domA \<Theta> - domA \<Gamma>)) \<subseteq> (- (domA \<Theta> - domA \<Delta>))"
    and subset2: "(- (domA \<Theta> - domA \<Gamma>)) \<subseteq> (- (domA \<Delta> - domA \<Gamma>))"
    using reds_doesnt_forget[OF Application(2)]  reds_doesnt_forget[OF Application(4)] by auto
  let "?S" = " (- (domA \<Theta> - domA \<Gamma>))"

  show "Afix \<Theta>\<cdot>(Aexp' z\<cdot>n \<squnion> ae) f|` ?S \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp' (App e x)\<cdot>n \<squnion> ae)  f|` ?S"
  proof(cases n)
    case bottom
    from env_restr_below_trans[OF env_restr_below_subset[OF subset1 Application(5)[OF prem1, where n = "\<bottom>"], simplified]
                                  env_restr_below_subset[OF subset2 Application(3)[OF prem2, where n = "\<bottom>"], simplified]]
    show ?thesis using bottom by simp
  next
    case (up n')
    note IH1 = env_restr_below_subset[OF subset2 Application(3)[OF prem3, where n = "inc\<^sub>\<bottom>\<cdot>n"], unfolded up Aexp'_simps inc_bot_simps] 
    note IH2 = env_restr_below_subset[OF subset1 Application(5)[OF prem1, where n = n], unfolded up Aexp'_simps]
    have "Afix \<Theta>\<cdot>(Aexp z\<cdot>n' \<squnion> ae)  f|` ?S  \<sqsubseteq> Afix \<Delta>\<cdot>(Aexp e'[y::=x]\<cdot>n' \<squnion> ae)  f|` ?S" by (rule IH2)
    also have "\<dots> \<sqsubseteq> Afix \<Delta>\<cdot>(env_delete y (Aexp e'\<cdot>n') \<squnion>  AE_singleton x \<cdot> (up\<cdot>0) \<squnion> ae)  f|` ?S"
      by (intro monofun_cfun_arg monofun_cfun_fun env_restr_mono Aexp_subst join_mono below_refl)  
    also have "\<dots> = Afix \<Delta>\<cdot>(env_delete y (Aexp e'\<cdot>(pred\<cdot>(inc\<cdot>n'))) \<squnion> (AE_singleton x \<cdot> (up\<cdot>0) \<squnion> ae))  f|` ?S" by simp
    also have "\<dots> \<sqsubseteq> Afix \<Delta>\<cdot>(Aexp (Lam [y]. e')\<cdot>(inc\<cdot>n') \<squnion> (AE_singleton x \<cdot> (up\<cdot>0) \<squnion> ae))  f|` ?S"
      by (intro monofun_cfun_arg monofun_cfun_fun env_restr_mono Aexp_Lam join_mono below_refl)  
    also have "\<dots> \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp e\<cdot>(inc\<cdot>n') \<squnion> (AE_singleton x\<cdot>(up\<cdot>0) \<squnion> ae)) f|` ?S" by (rule IH1)
    also have "\<dots> = Afix \<Gamma>\<cdot>(Aexp e\<cdot>(inc\<cdot>n') \<squnion> AE_singleton x\<cdot>(up\<cdot>0) \<squnion> ae)  f|` ?S" by simp
    also have "\<dots> \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp (App e x)\<cdot>n' \<squnion> ae)  f|` ?S" 
      by (intro monofun_cfun_arg monofun_cfun_fun env_restr_mono Aexp_App join_mono below_refl)  
    finally
    show ?thesis unfolding up by simp
  qed
next
case (Let as \<Gamma> L e \<Delta> z ae n)
  have *: "atom ` domA as \<sharp>* \<Gamma>" using Let(1) by (metis fresh_star_Pair)

  let ?S = "(- (domA \<Delta> - domA \<Gamma>))"
  have subset: "?S \<subseteq>  (- (domA \<Delta> - domA (as @ \<Gamma>)))" by auto

  note prem = `edom ae \<subseteq> set L`
  note IH = env_restr_below_subset[OF subset Let(3)[OF prem]]

  from `atom \` domA as \<sharp>* (\<Gamma>, L)`
  have "atom ` domA as \<sharp>* set L" by (auto simp add: fresh_star_Pair set_bn_to_atom_domA fresh_star_set)
  hence "domA as \<inter> set L = {}" by (metis Int_commute disjoint_iff_not_equal fresh_list_elem fresh_set fresh_star_def image_eqI not_self_fresh)
  with prem
  have **: "ae ` domA as \<subseteq> {\<bottom>}" by (auto simp add: edom_def)

  have [simp]: "ae f|` (-domA as) = ae" apply (rule env_restr_useless) using prem `domA as \<inter> set L = {}` by auto

  from `atom \` domA as \<sharp>* \<Gamma>` have "domA as \<inter> domA \<Gamma> = {}" by (metis fresh_distinct)
  moreover from reds_doesnt_forget[OF Let(2)] have "domA as \<subseteq> domA \<Delta>" by auto
  ultimately have ***: "((- domA \<Delta> \<union> domA \<Gamma>) \<inter> - domA as) = (- domA \<Delta> \<union> domA \<Gamma>)" by auto

  have "Afix \<Delta>\<cdot>(Aexp' z\<cdot>n \<squnion> ae)  f|` ?S \<sqsubseteq> Afix (as @ \<Gamma>)\<cdot>(Aexp' e\<cdot>n \<squnion> ae)  f|` ?S" by (rule IH)
  also have "\<dots> = Afix \<Gamma>\<cdot>(Afix as\<cdot>(Aexp' e\<cdot>n \<squnion> ae))  f|` ?S" by (rule arg_cong[OF Afix_append_fresh[OF *]])
  also have "\<dots> = Afix \<Gamma>\<cdot>(Afix as\<cdot>(Aexp' e\<cdot>n) \<squnion> ae)  f|` ?S" by (rule arg_cong[OF Afix_join_fresh[OF **]])
  also have "\<dots> = Afix \<Gamma>\<cdot>(Afix as\<cdot>(Aexp' e\<cdot>n) \<squnion> ae) f|` (- (domA as)) f|` ?S" by (simp add: ***)
  also have "\<dots> = Afix \<Gamma>\<cdot>((Afix as\<cdot>(Aexp' e\<cdot>n) \<squnion> ae) f|` (- (domA as))) f|` (- (domA as)) f|` ?S" by (rule arg_cong[OF Afix_restr_fresh[OF *]])
  also have "\<dots> = Afix \<Gamma>\<cdot>((Afix as\<cdot>(Aexp' e\<cdot>n) \<squnion> ae) f|` (- (domA as))) f|` ?S" by (simp add: ***)
  also have "\<dots> = Afix \<Gamma>\<cdot>((Afix as\<cdot>(Aexp' e\<cdot>n)  f|` (- (domA as))) \<squnion> ae) f|` ?S" by (simp add: env_restr_join)
  also have "\<dots> \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp' (Terms.Let as e)\<cdot>n \<squnion> ae) f|` ?S" by (intro monofun_cfun_arg join_mono env_restr_mono below_refl Aexp'_Let)
  finally
  show "Afix \<Delta>\<cdot>(Aexp' z\<cdot>n \<squnion> ae) f|` ?S \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp' (Terms.Let as e)\<cdot>n \<squnion> ae) f|` ?S" by this simp_all
qed

corollary  reds_improves_arity'':
       "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : v \<Longrightarrow>
        edom ae \<subseteq> set L \<Longrightarrow> 
        Afix \<Delta> \<cdot> (Aexp v \<cdot> n \<squnion> ae) f|` (- (domA \<Delta> - domA \<Gamma>)) \<sqsubseteq> Afix \<Gamma> \<cdot> (Aexp e \<cdot> n \<squnion> ae) f|` (- (domA \<Delta> - domA \<Gamma>))"
using reds_improves_arity'[OF assms, where n = "up\<cdot>n", simplified] by simp

corollary  reds_improves_arity:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : v"
  shows "Afix \<Delta> \<cdot> (Aexp' v \<cdot> n) f|` (- (domA \<Delta> - domA \<Gamma>)) \<sqsubseteq> Afix \<Gamma> \<cdot> (Aexp' e \<cdot> n) f|` (- (domA \<Delta> - domA \<Gamma>))"
  using reds_improves_arity'[where ae = \<bottom>, OF assms] by simp
end



end

