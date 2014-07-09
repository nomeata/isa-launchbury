theory ArityCorrect
imports ArityAnalysis Launchbury (* "Vars-Nominal-HOLCF" *)
begin

locale CorrectArityAnalysis = ArityAnalysis +
  assumes Aexp_Var: "Aexp (Var x) \<cdot> n = AE_singleton x \<cdot> (up \<cdot> n)"
  assumes Aexp_subst_App_Lam: "Aexp (e'[y::=x]) \<sqsubseteq> Aexp (App (Lam [y]. e') x)"
  assumes Aexp_App: "Aexp (App e x) \<cdot> n = Aexp e \<cdot>(inc\<cdot>n) \<squnion> AE_singleton x \<cdot> (up\<cdot>0)"
  assumes Aexp_Let: "Afix as\<cdot>(Aexp e\<cdot>n) \<sqsubseteq> Aexp (Terms.Let as e)\<cdot>n"
  assumes Aexp_lookup_fresh: "atom v \<sharp> e \<Longrightarrow> (Aexp e\<cdot>a) v = \<bottom>"
begin

lemma Aexp'_Var: "Aexp' (Var x) \<cdot> n = AE_singleton x \<cdot> n"
  by (cases n) (simp_all add: Aexp_Var)

lemma Aexp'_Let: "Afix as\<cdot>(Aexp' e\<cdot>n) \<sqsubseteq> Aexp' (Terms.Let as e)\<cdot>n"
  by (cases n) (simp_all add: Aexp_Let)

lemma Afix_reorder: "map_of \<Gamma> = map_of \<Delta> \<Longrightarrow> Afix \<Gamma> = Afix \<Delta>"
  by (intro cfun_eqI)(simp add: Afix_eq cong: Abinds_reorder)

lemma Afix_repeat_singleton: "(\<mu> xa. Afix \<Gamma>\<cdot>(AE_singleton x\<cdot>(n \<squnion> xa x) \<squnion> ae)) = Afix \<Gamma>\<cdot>(AE_singleton x\<cdot>n \<squnion> ae)"
  apply (rule below_antisym)
  defer
  apply (subst fix_eq, simp)
  apply (intro monofun_cfun_arg join_mono below_refl join_above1)

  apply (rule fix_least_below, simp)
  apply (rule Afix_least_below, simp)
  apply (intro join_below below_refl iffD2[OF AE_singleton_below_iff] below_trans[OF _ fun_belowD[OF Afix_above_arg]]  below_trans[OF _ Afix_above_arg] join_above2)
  apply simp
  done

lemma Abinds_join_fresh: "ae' ` (domA \<Delta>) \<subseteq> {\<bottom>} \<Longrightarrow>  ABinds \<Delta>\<cdot>(ae \<squnion> ae') = (ABinds \<Delta>\<cdot>ae) \<squnion> ae'"
proof (induct \<Delta> rule: ABinds.induct)
  case 1 thus ?case by simp
next
  case (2 v e \<Delta>)
  from 2(2)
  have "ae' v = \<bottom>" by auto
  moreover
  from 2(2) have  "ae' ` domA (delete v \<Delta>) \<subseteq> {\<bottom>}" by auto
  hence "ABinds (delete v \<Delta>)\<cdot>(ae \<squnion> ae') = ABinds (delete v \<Delta>)\<cdot>ae \<squnion> ae'" by (rule 2)
  ultimately
  show "ABinds ((v, e) # \<Delta>)\<cdot>(ae \<squnion> ae') = ABinds ((v, e) # \<Delta>)\<cdot>ae \<squnion> ae'"
    by simp
qed  

lemma Afix_join_fresh: "ae' ` (domA \<Delta>) \<subseteq> {\<bottom>}  \<Longrightarrow>  Afix \<Delta>\<cdot>(ae \<squnion> ae') = (Afix \<Delta>\<cdot>ae) \<squnion> ae'"
  apply (rule below_antisym)
  apply (rule Afix_least_below)
  apply (simp add: Abinds_join_fresh)
  apply (rule join_below)
  apply (rule below_trans[OF Afix_above_arg join_above1])
  apply (rule join_above2)
  apply (rule join_below[OF monofun_cfun_arg [OF join_above1]])
  apply (rule below_trans[OF join_above2 Afix_above_arg])
  done


lemma Aexp'_lookup_fresh: "atom v \<sharp> e \<Longrightarrow> (Aexp' e\<cdot>a) v = \<bottom>"
  by (cases a) (auto simp add: Aexp_lookup_fresh)

lemma ABinds_lookup_fresh:
  "atom v \<sharp> \<Gamma> \<Longrightarrow> (ABinds \<Gamma>\<cdot>ae) v = ae v"
by (induct \<Gamma> rule: ABinds.induct) (auto simp add: fresh_Cons fresh_Pair Aexp'_lookup_fresh fresh_delete)

lemma Afix_lookup_fresh:
  assumes "atom v \<sharp> \<Gamma>"
  shows "(Afix \<Gamma>\<cdot>ae) v = ae v"
  apply (rule below_antisym)
  apply (subst Afix_eq)
  apply (rule fix_ind[where  P = "\<lambda> ae'. ae' v \<sqsubseteq> ae v"])
  apply (auto simp add: ABinds_lookup_fresh[OF assms] fun_belowD[OF Afix_above_arg])
  done


lemma Abinds_append_fresh: "atom ` (domA \<Delta>) \<sharp>* \<Gamma> \<Longrightarrow>  ABinds (\<Delta> @ \<Gamma>)\<cdot>ae = ABinds \<Delta>\<cdot>(ABinds \<Gamma>\<cdot>ae)"
proof (induct \<Delta> rule: ABinds.induct)
  case 1 thus ?case by simp
next
  case (2 v e \<Delta>)
  from 2(2)
  have "atom v \<sharp> \<Gamma>" and  "atom ` domA (delete v \<Delta>) \<sharp>* \<Gamma>"
    by (auto simp add: fresh_star_def)
  from 2(1)[OF this(2)]
  have "ABinds (delete v \<Delta> @ \<Gamma>)\<cdot>ae = ABinds (delete v \<Delta>)\<cdot>(ABinds \<Gamma>\<cdot>ae)".
  moreover
  have "delete v \<Gamma> = \<Gamma>" by (metis `atom v \<sharp> \<Gamma>` delete_not_domA domA_not_fresh)
  moreover
  have "(ABinds \<Gamma>\<cdot>ae) v = ae v" by (rule ABinds_lookup_fresh[OF `atom v \<sharp> \<Gamma>`])
  ultimately
  show "ABinds (((v, e) # \<Delta>) @ \<Gamma>)\<cdot>ae = ABinds ((v, e) # \<Delta>)\<cdot>(ABinds \<Gamma>\<cdot>ae)"
    by simp
qed  

lemma Afix_comp2join_fresh:
  "atom ` (domA \<Delta>) \<sharp>* \<Gamma> \<Longrightarrow> ABinds \<Delta>\<cdot>(Afix \<Gamma>\<cdot>ae) = Afix \<Gamma> \<cdot> ae \<squnion> ABinds \<Delta>\<cdot>ae"
proof (induct \<Delta> rule: ABinds.induct)
  case 1 show ?case by (simp add: Afix_above_arg del: fun_meet_simp)
next
  case (2 v e \<Delta>)
  from 2(2)
  have "atom v \<sharp> \<Gamma>" and  "atom ` domA (delete v \<Delta>) \<sharp>* \<Gamma>"
    by (auto simp add: fresh_star_def)
  from 2(1)[OF this(2)]
  show ?case
    by (simp del: fun_meet_simp add: Afix_lookup_fresh[OF `atom v \<sharp> \<Gamma>`])
       (metis (hide_lams, no_types) join_assoc join_comm)
qed

lemma Afix_append_fresh:
  assumes "atom ` domA \<Delta> \<sharp>* \<Gamma>"
  shows "Afix (\<Delta> @ \<Gamma>)\<cdot>ae = Afix \<Gamma>\<cdot>(Afix \<Delta>\<cdot>ae)"
proof (rule below_antisym)
  show *: "Afix (\<Delta> @ \<Gamma>)\<cdot>ae \<sqsubseteq> Afix \<Gamma>\<cdot>(Afix \<Delta>\<cdot>ae)"
  by (rule Afix_least_below)
     (simp_all add:  Abinds_append_fresh[OF assms] Afix_comp2join_fresh[OF assms] Afix_above_arg below_trans[OF Afix_above_arg Afix_above_arg])
next
  show "Afix \<Gamma>\<cdot>(Afix \<Delta>\<cdot>ae) \<sqsubseteq> Afix (\<Delta> @ \<Gamma>)\<cdot>ae"
  proof (rule Afix_least_below)
    show "ABinds \<Gamma>\<cdot>(Afix (\<Delta> @ \<Gamma>)\<cdot>ae) \<sqsubseteq> Afix (\<Delta> @ \<Gamma>)\<cdot>ae"
      apply (subst Abinds_Afix[symmetric]) back
      apply (subst Abinds_append_fresh[OF assms])
      apply (rule ABinds_above_arg)
      done
    show "Afix \<Delta>\<cdot>ae \<sqsubseteq> Afix (\<Delta> @ \<Gamma>)\<cdot>ae"
      apply (rule Afix_least_below)
      apply (subst Abinds_Afix[symmetric]) back
      apply (subst Abinds_append_fresh[OF assms])
      apply (rule monofun_cfun_arg[OF ABinds_above_arg])
      apply (rule Afix_above_arg)
      done
  qed
qed

lemma Afix_e_to_heap:
   "Afix (delete x \<Gamma>)\<cdot>(Aexp' e\<cdot>n \<squnion> ae) \<sqsubseteq> Afix ((x, e) # delete x \<Gamma>)\<cdot>(AE_singleton x\<cdot>n \<squnion> ae)"
    apply (simp add: Afix_eq)
    apply (rule fix_least_below, simp)
    apply (intro join_below)
    apply (subst fix_eq, simp) back apply (simp add: below_trans[OF _ join_above2])
    apply (subst fix_eq, simp)
    apply (rule below_trans[OF monofun_cfun_arg join_above1])
    apply (subst fix_eq, simp)
    apply (rule below_trans[OF _ join_above2])
    apply (rule below_trans[OF _ join_above2])
    apply simp
    apply (subst fix_eq, simp)
    apply (rule below_trans[OF _ join_above2])
    apply (rule below_trans[OF _ join_above2])
    apply (rule below_trans[OF _ join_above2])
    apply simp
    done

lemma Afix_e_to_heap':
   "Afix (delete x \<Gamma>)\<cdot>(Aexp e\<cdot>n) \<sqsubseteq> Afix ((x, e) # delete x \<Gamma>)\<cdot>(AE_singleton x\<cdot>(up\<cdot>n))"
using Afix_e_to_heap[where ae = \<bottom> and n = "up\<cdot>n"] by simp


lemma  reds_improves_arity':
       "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : v \<Longrightarrow>
        ae -` (-{\<bottom>}) \<subseteq> set L \<Longrightarrow> 
        Afix \<Delta> \<cdot> (Aexp' v \<cdot> n \<squnion> ae) \<sqsubseteq> Afix \<Gamma> \<cdot> (Aexp' e \<cdot> n \<squnion> ae)"
proof(induct arbitrary: ae n rule: reds.induct)
case Lambda
  show ?case by simp
next
case (Variable \<Gamma> x e L \<Delta> z ae n)
  have reorder: "map_of ((x, e) # delete x \<Gamma>) = map_of \<Gamma>" by (rule map_of_delete_insert[OF Variable.hyps(1)])

  from `ae -\` (- {\<bottom>}) \<subseteq> set L`
  have prem: "ae -` (- {\<bottom>}) \<subseteq> set (x#L)" by auto

  have "x \<notin> domA \<Delta>" by (rule reds_avoids_live[OF Variable(2), where x = x]) simp_all
  hence [simp]:"delete x \<Delta> = \<Delta>" by simp

  note IH =  Variable(3)
  have "Afix ((x, z) # \<Delta>) \<cdot> (Aexp' z\<cdot>n \<squnion> ae) = (\<mu> ae'. Aexp' z\<cdot>(ae' x) \<squnion> ABinds \<Delta> \<cdot> ae' \<squnion> Aexp' z\<cdot>n \<squnion> ae)"
    unfolding Afix_eq by simp
  also have "\<dots> = (\<mu> ae'. ABinds \<Delta> \<cdot> ae' \<squnion> (Aexp' z\<cdot>n \<squnion> Aexp' z\<cdot>(ae' x) \<squnion> ae))" by (metis (hide_lams, no_types) join_assoc join_comm)
  also have "\<dots> \<sqsubseteq> (\<mu> ae'. ABinds \<Delta> \<cdot> ae' \<squnion> (Aexp' z\<cdot>(n \<squnion> ae' x) \<squnion> ae))" by (auto intro!: monofun_cfun_arg cfun_belowI join_mono[OF below_refl] join_mono[OF _ below_refl] cfun_join_below simp del: join_assoc)
  also have "\<dots> = (\<mu> ae'. Afix \<Delta> \<cdot> ae' \<squnion> (Aexp' z\<cdot>(n \<squnion> ae' x) \<squnion> ae))"
    apply (rule fix_eq_fix)
    apply simp
    apply (subst fix_eq) back back apply simp
    apply (rule join_mono[OF _ below_refl])
    apply (rule monofun_cfun_fun)
    apply (rule Abinds_below_Afix)

    apply simp
    apply (rule join_below)
    apply (subst Afix_eq)
    apply (rule fix_least_below)
    apply simp
    apply (subst fix_eq) back apply simp
    apply (subst fix_eq) back apply simp
    done
  also have "\<dots> = (\<mu> ae'. Afix \<Delta> \<cdot> (Aexp' z\<cdot>(n \<squnion> ae' x) \<squnion> ae))"
    apply (rule fix_eq_fix)
    apply simp
    apply (rule join_below)
    apply (subst Afix_eq)
    apply (rule fix_least_below, simp)
    apply (subst (1 2) fix_eq, simp)
    apply (subst fix_eq, simp)back
    apply (rule Afix_above_arg)

    apply simp
    apply (subst fix_eq, simp) back
    apply (rule below_trans[OF monofun_cfun_arg join_above1])
    apply (rule join_below)
    apply (subst fix_eq, simp) back
    apply (rule below_trans[OF _ join_above2], simp)
    
    apply (subst fix_eq)  apply simp
    apply (rule below_trans[OF _ join_above2], simp)
    done
    
  also have "\<dots> \<sqsubseteq> (\<mu> ae'. Afix (delete x \<Gamma>) \<cdot> (Aexp' e\<cdot>(n \<squnion> ae' x) \<squnion> ae))" by (auto intro!: monofun_cfun_arg cfun_belowI IH[OF prem])
  also have "\<dots> \<sqsubseteq> (\<mu> ae'. Afix ((x,e)#delete x \<Gamma>) \<cdot> (AE_singleton x \<cdot> (n \<squnion> ae' x) \<squnion> ae))"
    apply (rule monofun_cfun_arg)
    apply (rule cfun_belowI, simp)
    apply (rule Afix_e_to_heap)
    done
  also have "\<dots> = Afix ((x,e)#delete x \<Gamma>) \<cdot> (AE_singleton x\<cdot>n \<squnion> ae)" by (rule Afix_repeat_singleton)
  also have "\<dots> = Afix ((x,e)#delete x \<Gamma>) \<cdot> (Aexp' (Var x) \<cdot> n \<squnion> ae)" by (rule arg_cong[OF Aexp'_Var[symmetric]])
  also have "\<dots> = Afix \<Gamma> \<cdot> (Aexp' (Var x)\<cdot>n \<squnion> ae)" by (rule arg_cong[OF Afix_reorder[OF reorder]])
  finally show ?case by this simp_all
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> z e' ae n)
  note prem1 =  `ae -\` (- {\<bottom>}) \<subseteq> set L`
  hence prem2: "ae -` (- {\<bottom>}) \<subseteq> set (x#L)" by auto
  hence prem3: "(AE_singleton x\<cdot>(up\<cdot>0) \<squnion> ae) -` (- {\<bottom>}) \<subseteq> set (x#L)"  by auto

  show "Afix \<Theta>\<cdot>(Aexp' z\<cdot>n \<squnion> ae) \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp' (App e x)\<cdot>n \<squnion> ae)"
  proof(cases n)
    case bottom
    with below_trans[OF Application(5)[OF prem1, where n = "\<bottom>", simplified ]  Application(3)[OF prem2, where n = "\<bottom>", simplified] ]
    show ?thesis by (simp add: lambda_strict)
  next
    case (up n')
    note IH1 = Application(3)[OF prem3, where n = "inc\<^sub>\<bottom>\<cdot>n", unfolded up Aexp'_simps inc_bot_simps] 
    note IH2 = Application(5)[OF prem1, where n = n, unfolded up Aexp'_simps]
    have "Afix \<Theta>\<cdot>(Aexp z\<cdot>n' \<squnion> ae) \<sqsubseteq> Afix \<Delta>\<cdot>(Aexp e'[y::=x]\<cdot>n' \<squnion> ae)" by (rule IH2)
    also have "\<dots> \<sqsubseteq> Afix \<Delta>\<cdot>(Aexp (App (Lam [y]. e') x)\<cdot>n' \<squnion> ae)" by (intro monofun_cfun_arg monofun_cfun_fun Aexp_subst_App_Lam join_mono below_refl)
    also have "\<dots> = Afix \<Delta>\<cdot>(Aexp (Lam [y]. e')\<cdot>(inc\<cdot>n') \<squnion> AE_singleton x \<cdot> (up\<cdot>0) \<squnion> ae)"  by (rule arg_cong[OF Aexp_App])
    also have "\<dots> = Afix \<Delta>\<cdot>(Aexp (Lam [y]. e')\<cdot>(inc\<cdot>n') \<squnion> (AE_singleton x\<cdot>(up\<cdot>0) \<squnion> ae))"  by simp
    also have "\<dots> \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp e\<cdot>(inc\<cdot>n') \<squnion> (AE_singleton x\<cdot>(up\<cdot>0) \<squnion> ae))" by (rule IH1)
    also have "\<dots> = Afix \<Gamma>\<cdot>(Aexp e\<cdot>(inc\<cdot>n') \<squnion> AE_singleton x\<cdot>(up\<cdot>0) \<squnion> ae)" by simp
    also have "\<dots> = Afix \<Gamma>\<cdot>(Aexp (App e x)\<cdot>n' \<squnion> ae)" by (rule arg_cong[OF Aexp_App[symmetric]])
    finally
    show ?thesis unfolding up by simp
  qed
next
case (Let as \<Gamma> L e \<Delta> z ae n)
  have *: "atom ` domA as \<sharp>* \<Gamma>" using Let(1) by (metis fresh_star_Pair)
  note prem = `ae -\` (-{\<bottom>}) \<subseteq> set L`
  note IH = Let(3)[OF prem]

  from `atom \` domA as \<sharp>* (\<Gamma>, L)`
  have "atom ` domA as \<sharp>* set L" by (auto simp add: fresh_star_Pair set_bn_to_atom_domA fresh_star_set)
  hence "domA as \<inter> set L = {}" by (metis Int_commute disjoint_iff_not_equal fresh_list_elem fresh_set fresh_star_def image_eqI not_self_fresh)
  with prem
  have **: "ae ` domA as \<subseteq> {\<bottom>}" by auto 

  have "Afix \<Delta>\<cdot>(Aexp' z\<cdot>n \<squnion> ae) \<sqsubseteq> Afix (as @ \<Gamma>)\<cdot>(Aexp' e\<cdot>n \<squnion> ae)" by (rule IH)
  also have "\<dots> = Afix \<Gamma>\<cdot>(Afix as\<cdot>(Aexp' e\<cdot>n \<squnion> ae))" by (rule Afix_append_fresh[OF *])
  also have "\<dots> = Afix \<Gamma>\<cdot>(Afix as\<cdot>(Aexp' e\<cdot>n) \<squnion> ae)" by (rule arg_cong[OF Afix_join_fresh[OF **]])
  also have "\<dots> \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp' (Terms.Let as e)\<cdot>n \<squnion> ae)" by (intro monofun_cfun_arg join_mono below_refl Aexp'_Let)
  finally
  show "Afix \<Delta>\<cdot>(Aexp' z\<cdot>n \<squnion> ae) \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp' (Terms.Let as e)\<cdot>n \<squnion> ae)" by this simp_all
qed

corollary  reds_improves_arity'':
       "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : v \<Longrightarrow>
        ae -` (-{\<bottom>}) \<subseteq> set L \<Longrightarrow> 
        Afix \<Delta> \<cdot> (Aexp v \<cdot> n \<squnion> ae) \<sqsubseteq> Afix \<Gamma> \<cdot> (Aexp e \<cdot> n \<squnion> ae)"
using reds_improves_arity'[OF assms, where n = "up\<cdot>n", simplified].


corollary  reds_improves_arity:
 assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : v"
  shows "Afix \<Delta> \<cdot> (Aexp' v \<cdot> n) \<sqsubseteq> Afix \<Gamma> \<cdot> (Aexp' e \<cdot> n)"
proof-
  have simp: "\<bottom> -` (- {\<bottom>}) = {}" by auto
  show ?thesis by (rule reds_improves_arity'[where ae = \<bottom>, OF assms, simplified]) auto
qed


end

end
