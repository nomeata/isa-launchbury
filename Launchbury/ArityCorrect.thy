theory ArityCorrect
imports ArityAnalysis Launchbury "Nominal-HOLCF" "Vars-Nominal-HOLCF"
begin

instantiation Arity :: pure
begin
  definition "p \<bullet> (a::Arity) = a"
instance
  apply default
  apply (auto simp add: permute_Arity_def)
  done
end

instance Arity :: cont_pt
  by default (simp add: pure_permute_id)

locale CorrectArityAnalysis = ArityAnalysis +
  assumes Aexp_Var: "Aexp (Var x) \<cdot> n = AE_singleton x \<cdot> (up \<cdot> n)"
  assumes Aexp_subst_App_Lam: "Aexp (e'[y::=x]) \<sqsubseteq> Aexp (App (Lam [y]. e') x)"
  assumes Aexp_App: "Aexp (App e x) \<cdot> n = Aexp e \<cdot>(inc\<cdot>n) \<squnion> AE_singleton x \<cdot> (up\<cdot>0)"
  assumes Aexp_Lam: "Afix2 (asToHeap as)\<cdot>(Aexp e\<cdot>n) \<sqsubseteq> Aexp (Let as e)\<cdot>n"
begin

lemma Afix_bind_to_F: "Afix ((x, z) # \<Delta>) \<cdot> F = Afix (delete x \<Delta>) \<cdot> (ABind x z \<squnion> F)"
  apply (rule cfun_eqI)
  apply (simp add: Afix_eq)
  by (metis (hide_lams, no_types) join_assoc join_comm)

lemma Afix_duplicate_binds:
  assumes  "cont G"
  shows "Afix \<Gamma> \<cdot> ((\<Lambda> ae. G ae) \<squnion>  F) = Afix \<Gamma> \<cdot> ((\<Lambda> ae. Afix \<Gamma> \<cdot> ID \<cdot> (G ae)) \<squnion> F)"
proof-
  note cont_compose[OF assms, cont2cont, simp]
  show ?thesis
  apply (rule cfun_eqI)
  unfolding Afix_eq
  apply (rule below_antisym)
  apply (rule fix_least_below)
  apply (subst fix_eq) back back 
  apply simp

  apply (intro join_mono below_refl)
  apply (subst fix_eq) back back
  apply simp

  apply (simp add: below_trans[OF  _ join_above1] below_trans[OF _ join_above2])

  apply (rule fix_least_below, simp)
  apply (intro join_below)

  apply (subst fix_eq)  apply simp
  
  apply (subst fix_eq) back  apply simp
  apply (simp add: below_trans[OF  _ join_above1] below_trans[OF _ join_above2])

  apply (rule fix_least_below, simp)
  apply (intro join_below)
  apply (subst fix_eq) back apply simp
  apply (simp add: below_trans[OF  _ join_above1] below_trans[OF _ join_above2])

  apply (subst fix_eq) back apply simp
  apply (simp add: below_trans[OF  _ join_above1] below_trans[OF _ join_above2])

  apply simp

  apply (subst fix_eq) back apply simp
  apply (simp add: below_trans[OF  _ join_above1] below_trans[OF _ join_above2])
  done
qed

lemma Afix_const_to_F: "Afix \<Gamma> \<cdot> F \<cdot> (a \<squnion> b) = Afix \<Gamma> \<cdot> (F \<squnion> (\<Lambda> _. b)) \<cdot>a"
  unfolding Afix_eq
  apply simp
  by (metis (hide_lams, no_types) join_assoc join_comm)

lemma Aexp'_Var: "Aexp' (Var x) \<cdot> n = AE_singleton x \<cdot> n"
  by (cases n) (simp_all add: Aexp_Var)

lemma Aexp'_Lam: "Afix2 (asToHeap as)\<cdot>(Aexp' e\<cdot>n) \<sqsubseteq> Aexp' (Let as e)\<cdot>n"
  by (cases n) (simp_all add: Aexp_Lam)

lemma AFix_above_arg: "ae \<sqsubseteq> Afix \<Gamma> \<cdot> F \<cdot> ae"
  apply (simp add: Aexp_Var Afix_eq ABind_def AE_singleton_def)
  apply (subst fix_eq)
  apply simp
  done

lemma Afix_below_var: "Afix ((x,e) # \<Gamma>) \<cdot> F \<cdot> (Aexp' e\<cdot>n) \<sqsubseteq> Afix ((x,e) # \<Gamma>)\<cdot> F \<cdot>(Aexp' (Var x)\<cdot>n)"
proof-
  have "(\<mu> xa. Aexp' e\<cdot>n \<squnion> (Aexp' e\<cdot>(xa x) \<squnion> (ABinds (delete x \<Gamma>)\<cdot>xa \<squnion> F\<cdot>xa))) \<sqsubseteq> (\<mu> xa. AE_singleton x \<cdot> n \<squnion> (Aexp' e\<cdot>(xa x) \<squnion> (ABinds (delete x \<Gamma>)\<cdot>xa \<squnion> F\<cdot>xa)))" (is "fix\<cdot>?F1 \<sqsubseteq> fix\<cdot>?F2")
  proof(rule fix_least_below)
    have F2x: "n \<sqsubseteq> (fix \<cdot> ?F2) x" by (subst fix_eq) (simp add: AE_singleton_def)

    have "?F1 \<cdot> (fix \<cdot> ?F2) \<sqsubseteq> ?F2 \<cdot> (fix \<cdot> ?F2)"
      by (auto intro: join_below simp  add: below_trans[OF _ join_above2]  below_trans[OF _ join_above1] monofun_cfun_arg F2x)
    thus "?F1 \<cdot> (fix \<cdot> ?F2) \<sqsubseteq> (fix \<cdot> ?F2)" unfolding fix_eq[symmetric].
  qed
  thus ?thesis by (simp add: Aexp_Var Afix_eq ABind_def Aexp'_Var)
qed
  
lemma Afix_reorder: "map_of \<Gamma> = map_of \<Delta> \<Longrightarrow> Afix \<Gamma> = Afix \<Delta>"
  by (intro cfun_eqI)(simp add: Afix_eq cong: Abinds_reorder)

lemma Afix2_reorder: "map_of \<Gamma> = map_of \<Delta> \<Longrightarrow> Afix2 \<Gamma> = Afix2 \<Delta>"
  by (intro cfun_eqI)(simp add: Afix2_eq cong: Abinds_reorder)

lemma Afix2_repeat_singleton: "(\<mu> xa. Afix2 \<Gamma>\<cdot>(AE_singleton x\<cdot>(n \<squnion> xa x) \<squnion> ae)) = Afix2 \<Gamma>\<cdot>(AE_singleton x\<cdot>n \<squnion> ae)"
  apply (rule below_antisym)
  defer
  apply (subst fix_eq, simp)
  apply (intro monofun_cfun_arg join_mono below_refl join_above1)

  apply (rule fix_least_below, simp)
  apply (rule Afix2_least_below, simp)
  apply (intro join_below below_refl iffD2[OF AE_singleton_below_iff] below_trans[OF _ fun_belowD[OF Afix2_above_arg]]  below_trans[OF _ Afix2_above_arg] join_above2)
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

(* http://afp.sourceforge.net/browser_info/current/AFP/WorkerWrapper/FixedPointTheorems.html *)
lemma rolling_rule_ltr: "fix\<cdot>(g oo f) \<sqsubseteq> g\<cdot>(fix\<cdot>(f oo g))"
proof -
  have "g\<cdot>(fix\<cdot>(f oo g)) \<sqsubseteq> g\<cdot>(fix\<cdot>(f oo g))"
    by (rule below_refl) -- {* reflexivity *}
  hence "g\<cdot>((f oo g)\<cdot>(fix\<cdot>(f oo g))) \<sqsubseteq> g\<cdot>(fix\<cdot>(f oo g))"
    using fix_eq[where F="f oo g"] by simp -- {* computation *}
  hence "(g oo f)\<cdot>(g\<cdot>(fix\<cdot>(f oo g))) \<sqsubseteq> g\<cdot>(fix\<cdot>(f oo g))"
    by simp -- {* re-associate @{term "op oo"} *}
  thus "fix\<cdot>(g oo f) \<sqsubseteq> g\<cdot>(fix\<cdot>(f oo g))"
    using fix_least_below by blast -- {* induction *}
qed

lemma rolling_rule_rtl: "g\<cdot>(fix\<cdot>(f oo g)) \<sqsubseteq> fix\<cdot>(g oo f)"
proof -
  have "fix\<cdot>(f oo g) \<sqsubseteq> f\<cdot>(fix\<cdot>(g oo f))" by (rule rolling_rule_ltr)
  hence "g\<cdot>(fix\<cdot>(f oo g)) \<sqsubseteq> g\<cdot>(f\<cdot>(fix\<cdot>(g oo f)))"
    by (rule monofun_cfun_arg) -- {* g is monotonic *}
  thus "g\<cdot>(fix\<cdot>(f oo g)) \<sqsubseteq> fix\<cdot>(g oo f)"
    using fix_eq[where F="g oo f"] by simp -- {* computation *}
qed

lemma rolling_rule: "fix\<cdot>(g oo f) = g\<cdot>(fix\<cdot>(f oo g))"
  by (rule below_antisym[OF rolling_rule_ltr rolling_rule_rtl])

lemma rolling_rule2:
  assumes "cont F" and "cont G"
  shows "fix\<cdot>(\<Lambda> x. G (F x)) = G (fix\<cdot>(\<Lambda> x. F (G x)))"
  using cont_compose[OF assms(1), cont2cont] cont_compose[OF assms(2), cont2cont]
  using rolling_rule[where g = "\<Lambda> x. G x" and f = "\<Lambda> x. F x"]
  by (auto simp add: oo_def)

lemma Afix2_join_fresh: "ae' ` (domA \<Delta>) \<subseteq> {\<bottom>}  \<Longrightarrow>  Afix2 \<Delta>\<cdot>(ae \<squnion> ae') = (Afix2 \<Delta>\<cdot>ae) \<squnion> ae'"
  apply (rule below_antisym)
  apply (rule Afix2_least_below)
  apply (simp add: Abinds_join_fresh)
  apply (rule join_below)
  apply (rule below_trans[OF Afix2_above_arg join_above1])
  apply (rule join_above2)
  apply (rule join_below[OF monofun_cfun_arg [OF join_above1]])
  apply (rule below_trans[OF join_above2 Afix2_above_arg])
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
  have "delete v \<Gamma> = \<Gamma>" sorry
  moreover
  have "(ABinds \<Gamma>\<cdot>ae) v = ae v" sorry
  ultimately
  show "ABinds (((v, e) # \<Delta>) @ \<Gamma>)\<cdot>ae = ABinds ((v, e) # \<Delta>)\<cdot>(ABinds \<Gamma>\<cdot>ae)"
    by simp
qed  


lemma Afix2_append_fresh:
  assumes "atom ` domA \<Delta> \<sharp>* \<Gamma>"
  shows "Afix2 (\<Delta> @ \<Gamma>)\<cdot>ae = Afix2 \<Gamma>\<cdot>(Afix2 \<Delta>\<cdot>ae)"
apply (rule below_antisym)
apply (rule Afix2_least_below)
apply (simp add:  Abinds_append_fresh[OF assms])
sorry

    
lemma  "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : v \<Longrightarrow> 
        Afix2 \<Delta> \<cdot> (Aexp' v \<cdot> n \<squnion> ae) \<sqsubseteq> Afix2 \<Gamma> \<cdot> (Aexp' e \<cdot> n \<squnion> ae)"
proof(induct arbitrary: ae n rule: reds.induct)
case Lambda
  show ?case by simp
next
case (Variable \<Gamma> x e L \<Delta> z ae n)
  have reorder: "map_of ((x, e) # delete x \<Gamma>) = map_of \<Gamma>" by (rule map_of_delete_insert[OF Variable.hyps(1)])

  have "x \<notin> domA \<Delta>" by (rule reds_avoids_live[OF Variable(2), where x = x]) simp_all
  hence [simp]:"delete x \<Delta> = \<Delta>" by simp

  note IH =  Variable(3)
  have "Afix2 ((x, z) # \<Delta>) \<cdot> (Aexp' z\<cdot>n \<squnion> ae) = (\<mu> ae'. Aexp' z\<cdot>(ae' x) \<squnion> ABinds \<Delta> \<cdot> ae' \<squnion> Aexp' z\<cdot>n \<squnion> ae)"
    unfolding Afix2_eq by simp
  also have "\<dots> = (\<mu> ae'. ABinds \<Delta> \<cdot> ae' \<squnion> (Aexp' z\<cdot>n \<squnion> Aexp' z\<cdot>(ae' x) \<squnion> ae))" by (metis (hide_lams, no_types) join_assoc join_comm)
  also have "\<dots> \<sqsubseteq> (\<mu> ae'. ABinds \<Delta> \<cdot> ae' \<squnion> (Aexp' z\<cdot>(n \<squnion> ae' x) \<squnion> ae))" by (auto intro!: monofun_cfun_arg cfun_belowI join_mono[OF below_refl] join_mono[OF _ below_refl] cfun_join_below simp del: join_assoc)
  also have "\<dots> = (\<mu> ae'. Afix2 \<Delta> \<cdot> ae' \<squnion> (Aexp' z\<cdot>(n \<squnion> ae' x) \<squnion> ae))"
    apply (rule fix_eq_fix)
    apply simp
    apply (subst fix_eq) back back apply simp
    apply (rule join_mono[OF _ below_refl])
    apply (rule monofun_cfun_fun)
    apply (rule Abinds_below_Afix2)

    apply simp
    apply (rule join_below)
    apply (subst Afix2_eq)
    apply (rule fix_least_below)
    apply simp
    apply (rule join_below[OF _ below_refl])
    apply (subst fix_eq) back apply simp
    apply (subst fix_eq) back apply simp
    done
  also have "\<dots> = (\<mu> ae'. Afix2 \<Delta> \<cdot> (Aexp' z\<cdot>(n \<squnion> ae' x) \<squnion> ae))"
    apply (rule fix_eq_fix)
    apply simp
    apply (rule join_below)
    apply (subst Afix2_eq)
    apply (rule fix_least_below, simp)
    apply (rule join_below[OF _ below_refl])
    apply (subst (1 2) fix_eq, simp)
    apply (subst fix_eq, simp)back
    apply (rule Afix2_above_arg)

    apply simp
    apply (subst fix_eq, simp) back
    apply (rule below_trans[OF monofun_cfun_arg join_above1])
    apply (rule join_below)
    apply (subst fix_eq, simp) back
    apply (rule below_trans[OF _ join_above2], simp)
    
    apply (subst fix_eq)  apply simp
    apply (rule below_trans[OF _ join_above2], simp)
    done
    
  also have "\<dots> \<sqsubseteq> (\<mu> ae'. Afix2 (delete x \<Gamma>) \<cdot> (Aexp' e\<cdot>(n \<squnion> ae' x) \<squnion> ae))" by (auto intro!: monofun_cfun_arg cfun_belowI IH)
  also have "\<dots> \<sqsubseteq> (\<mu> ae'. Afix2 ((x,e)#delete x \<Gamma>) \<cdot> (AE_singleton x \<cdot> (n \<squnion> ae' x) \<squnion> ae))"
    apply (rule monofun_cfun_arg)
    apply (rule cfun_belowI, simp)
    apply (simp add: Afix2_eq)
    apply (rule fix_least_below, simp)
    apply (intro join_below)
    apply (subst fix_eq, simp) back back apply (simp add: below_trans[OF _ join_above2])
    apply (subst fix_eq, simp)
    apply (rule below_trans[OF monofun_cfun_arg join_above1])
    apply (subst fix_eq, simp)
    apply (rule below_trans[OF _ join_above2])
    apply (rule below_trans[OF _ join_above2])
    apply (rule join_mono[OF below_refl])
    apply simp
    apply (subst fix_eq, simp)
    apply (rule below_trans[OF _ join_above2])
    apply (rule below_trans[OF _ join_above2])
    apply (rule below_trans[OF _ join_above2])
    apply simp
    done
  also have "\<dots> = Afix2 ((x,e)#delete x \<Gamma>) \<cdot> (AE_singleton x\<cdot>n \<squnion> ae)" by (rule Afix2_repeat_singleton)
  also have "\<dots> = Afix2 ((x,e)#delete x \<Gamma>) \<cdot> (Aexp' (Var x) \<cdot> n \<squnion> ae)" by (rule arg_cong[OF Aexp'_Var[symmetric]])
  also have "\<dots> = Afix2 \<Gamma> \<cdot> (Aexp' (Var x)\<cdot>n \<squnion> ae)" by (rule arg_cong[OF Afix2_reorder[OF reorder]])
  finally show ?case.
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> z e' ae n)
  show "Afix2 \<Theta>\<cdot>(Aexp' z\<cdot>n \<squnion> ae) \<sqsubseteq> Afix2 \<Gamma>\<cdot>(Aexp' (App e x)\<cdot>n \<squnion> ae)"
  proof(cases n)
    case bottom
    with below_trans[OF Application(5)[where n = "\<bottom>" and ae = ae, simplified ]  Application(3)[where n = "\<bottom>" and ae = ae, simplified] ]
    show ?thesis by (simp add: lambda_strict)
  next
    case (up n')
    note IH = Application(3)[where n = "inc\<^sub>\<bottom>\<cdot>n", unfolded up Aexp'_simps inc_bot_simps] Application(5)[where n = n, unfolded up Aexp'_simps]
    have "Afix2 \<Theta>\<cdot>(Aexp z\<cdot>n' \<squnion> ae) \<sqsubseteq> Afix2 \<Delta>\<cdot>(Aexp e'[y::=x]\<cdot>n' \<squnion> ae)" by (rule IH)
    also have "\<dots> \<sqsubseteq> Afix2 \<Delta>\<cdot>(Aexp (App (Lam [y]. e') x)\<cdot>n' \<squnion> ae)" by (intro monofun_cfun_arg monofun_cfun_fun Aexp_subst_App_Lam join_mono below_refl)
    also have "\<dots> = Afix2 \<Delta>\<cdot>(Aexp (Lam [y]. e')\<cdot>(inc\<cdot>n') \<squnion> AE_singleton x \<cdot> (up\<cdot>0) \<squnion> ae)"  by (rule arg_cong[OF Aexp_App])
    also have "\<dots> = Afix2 \<Delta>\<cdot>(Aexp (Lam [y]. e')\<cdot>(inc\<cdot>n') \<squnion> (AE_singleton x\<cdot>(up\<cdot>0) \<squnion> ae))"  by simp
    also have "\<dots> \<sqsubseteq> Afix2 \<Gamma>\<cdot>(Aexp e\<cdot>(inc\<cdot>n') \<squnion> (AE_singleton x\<cdot>(up\<cdot>0) \<squnion> ae))" by (rule IH)
    also have "\<dots> = Afix2 \<Gamma>\<cdot>(Aexp e\<cdot>(inc\<cdot>n') \<squnion> AE_singleton x\<cdot>(up\<cdot>0) \<squnion> ae)" by simp
    also have "\<dots> = Afix2 \<Gamma>\<cdot>(Aexp (App e x)\<cdot>n' \<squnion> ae)" by (rule arg_cong[OF Aexp_App[symmetric]])
    finally
    show ?thesis unfolding up by simp
  qed
next
case (Let as \<Gamma> L e \<Delta> z ae n)
  hence *: "atom ` domA (asToHeap as) \<sharp>* \<Gamma>" by (metis fresh_star_Pair set_bn_to_atom_domA) 
  have **: "ae ` domA (asToHeap as) \<subseteq> {\<bottom>}" sorry 

  have "Afix2 \<Delta>\<cdot>(Aexp' z\<cdot>n \<squnion> ae) \<sqsubseteq> Afix2 (asToHeap as @ \<Gamma>)\<cdot>(Aexp' e\<cdot>n \<squnion> ae)" by (rule Let)
  also have "\<dots> = Afix2 \<Gamma>\<cdot>(Afix2 (asToHeap as)\<cdot>(Aexp' e\<cdot>n \<squnion> ae))" by (rule Afix2_append_fresh[OF *])
  also have "\<dots> = Afix2 \<Gamma>\<cdot>(Afix2 (asToHeap as)\<cdot>(Aexp' e\<cdot>n) \<squnion> ae)" by (rule arg_cong[OF Afix2_join_fresh[OF **]])
  also have "\<dots> \<sqsubseteq> Afix2 \<Gamma>\<cdot>(Aexp' (Let as e)\<cdot>n \<squnion> ae)" by (intro monofun_cfun_arg join_mono below_refl Aexp'_Lam)
  finally
  show "Afix2 \<Delta>\<cdot>(Aexp' z\<cdot>n \<squnion> ae) \<sqsubseteq> Afix2 \<Gamma>\<cdot>(Aexp' (Let as e)\<cdot>n \<squnion> ae)".
qed

(*
lemma  "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : v \<Longrightarrow> 
        Afix \<Delta> \<cdot> F \<cdot> (Aexp' v \<cdot> n) \<sqsubseteq> Afix \<Gamma> \<cdot> F \<cdot> (Aexp' e \<cdot> n)"
proof(induct arbitrary: F n rule: reds.induct)
case Lambda
  show ?case by simp
next
case (Variable \<Gamma> x e L \<Delta> z F n)
  have reorder: "map_of ((x, e) # delete x \<Gamma>) = map_of \<Gamma>" by (rule map_of_delete_insert[OF Variable.hyps(1)])

  have "x \<notin> domA \<Delta>" by (rule reds_avoids_live[OF Variable(2), where x = x]) simp_all
  hence "delete x \<Delta> = \<Delta>" by simp

  note IH =  Variable(3)
  have "Afix ((x, z) # \<Delta>) \<cdot> F \<cdot>(Aexp' z\<cdot>n) = Afix (delete x \<Delta>) \<cdot> (ABind x z \<squnion> F) \<cdot>(Aexp' z\<cdot>n)" unfolding Afix_bind_to_F..
  also have "\<dots> = Afix \<Delta> \<cdot> (ABind x z \<squnion> F) \<cdot>(Aexp' z\<cdot>n)" unfolding `delete x \<Delta> = \<Delta>`..
  also have "\<dots> = Afix \<Delta> \<cdot> ((\<Lambda> ae . Aexp' z \<cdot> (ae x)) \<squnion> F) \<cdot> (Aexp' z\<cdot>n)" unfolding ABind_def..
  also have "\<dots> = Afix \<Delta> \<cdot> ((\<Lambda> ae . Afix \<Delta> \<cdot> ID \<cdot> (Aexp' z \<cdot> (ae x))) \<squnion> F) \<cdot>(Aexp' z\<cdot>n)" by (rule arg_cong[OF Afix_duplicate_binds]) simp
  also have "\<dots> \<sqsubseteq> Afix (delete x \<Gamma>) \<cdot> ((\<Lambda> ae. Afix \<Delta> \<cdot> ID \<cdot> (Aexp' z \<cdot> (ae x))) \<squnion> F) \<cdot>(Aexp' e\<cdot>n)"
    by (rule IH)
  also have "\<dots> \<sqsubseteq> Afix (delete x \<Gamma>) \<cdot> ((\<Lambda> ae. Afix (delete x \<Gamma>) \<cdot> ID \<cdot> (Aexp' e \<cdot> (ae x))) \<squnion> F) \<cdot>(Aexp' e\<cdot>n)"
    by (intro monofun_cfun_fun monofun_cfun_arg)(auto intro: IH  join_mono simp add: cfun_below_iff)
  also have "\<dots> = Afix (delete x \<Gamma>) \<cdot> ((\<Lambda> ae. Aexp' e \<cdot> (ae x)) \<squnion> F)\<cdot>(Aexp' e\<cdot>n)" by (rule arg_cong[OF Afix_duplicate_binds, symmetric]) simp
  also have "\<dots> = Afix (delete x \<Gamma>) \<cdot> ((ABind x e) \<squnion> F) \<cdot>(Aexp' e\<cdot>n)" unfolding ABind_def..
  also have "\<dots> = Afix ((x,e) # delete x \<Gamma>) \<cdot> F \<cdot>(Aexp' e\<cdot>n)" unfolding Afix_bind_to_F delete_idem..
  also have "\<dots> \<sqsubseteq> Afix ((x,e) # delete x \<Gamma>) \<cdot> F \<cdot>(Aexp' (Var x)\<cdot>n)" by (rule Afix_below_var)
  also have "\<dots> = Afix \<Gamma> \<cdot> F \<cdot>(Aexp' (Var x)\<cdot>n)" by (rule arg_cong[OF Afix_reorder[OF reorder]])
  finally
  show "Afix ((x, z) # \<Delta>) \<cdot> F \<cdot>(Aexp' z\<cdot>n) \<sqsubseteq> Afix \<Gamma> \<cdot> F  \<cdot> (Aexp' (Var x)\<cdot>n)".
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> z e' F n)
  show "Afix \<Theta>\<cdot>F\<cdot>(Aexp' z\<cdot>n) \<sqsubseteq> Afix \<Gamma>\<cdot>F\<cdot>(Aexp' (App e x)\<cdot>n)"
  proof(cases n)
    case bottom
    with below_trans[OF Application(5)[where n = "\<bottom>" and F = F, simplified ]  Application(3)[where n = "\<bottom>" and F = F, simplified] ]
    show ?thesis by (simp add: lambda_strict)
  next
    case (up n')
    note IH = Application(3)[where n = "inc\<^sub>\<bottom>\<cdot>n", unfolded up Aexp'_simps inc_bot_simps] Application(5)[where n = n, unfolded up Aexp'_simps]
    have "Afix \<Theta>\<cdot>F\<cdot>(Aexp z\<cdot>n') \<sqsubseteq> Afix \<Delta>\<cdot>F\<cdot>(Aexp e'[y::=x]\<cdot>n')" by (rule IH)
    also have "\<dots> \<sqsubseteq>  Afix \<Delta>\<cdot>F\<cdot>(Aexp (App (Lam [y]. e') x)\<cdot>n')" by (intro monofun_cfun_arg monofun_cfun_fun Aexp_subst_App_Lam)
    also have "\<dots> =  Afix \<Delta>\<cdot>F\<cdot>(Aexp (Lam [y]. e')\<cdot>(inc\<cdot>n') \<squnion> AE_singleton x (up\<cdot>0))"  by (rule arg_cong[OF Aexp_App])
    also have "\<dots> =  Afix \<Delta>\<cdot>(F \<squnion> (\<Lambda> _. AE_singleton x (up\<cdot>0)))\<cdot>(Aexp (Lam [y]. e')\<cdot>(inc\<cdot>n'))" unfolding Afix_const_to_F..
    also have "\<dots> \<sqsubseteq> Afix \<Gamma>\<cdot>(F \<squnion> (\<Lambda> _. AE_singleton x (up\<cdot>0)))\<cdot>(Aexp e\<cdot>(inc\<cdot>n'))" by (rule IH)
    also have "\<dots> = Afix \<Gamma>\<cdot>F\<cdot>(Aexp e\<cdot>(inc\<cdot>n') \<squnion> AE_singleton x (up\<cdot>0))" unfolding Afix_const_to_F..
    also have "\<dots> = Afix \<Gamma>\<cdot>F\<cdot>(Aexp (App e x)\<cdot>n')"  by (rule arg_cong[OF Aexp_App[symmetric]])
    finally
    show "Afix \<Theta>\<cdot>F\<cdot>(Aexp' z\<cdot>n) \<sqsubseteq> Afix \<Gamma>\<cdot>F\<cdot>(Aexp' (App e x)\<cdot>n)" unfolding up by simp
  qed
next
case (Let as \<Gamma> L e \<Delta> z F n)
  have "Afix \<Delta>\<cdot>F\<cdot>(Aexp' z\<cdot>n) \<sqsubseteq> Afix (asToHeap as @ \<Gamma>)\<cdot>F\<cdot>(Aexp' e\<cdot>n)" by (rule Let)
  also have "\<dots> \<sqsubseteq> Afix \<Gamma>\<cdot>F\<cdot>(Aexp' (Terms.Let as e)\<cdot>n)" by (rule Aexp'_Lam)
  finally
  show "Afix \<Delta>\<cdot>F\<cdot>(Aexp' z\<cdot>n) \<sqsubseteq> Afix \<Gamma>\<cdot>F\<cdot>(Aexp' (Terms.Let as e)\<cdot>n)".
qed
*)

end

end
