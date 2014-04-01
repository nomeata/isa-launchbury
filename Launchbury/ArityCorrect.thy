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
  assumes Aexp_Var: "Aexp (Var x) \<cdot> n = AE_singleton x (up \<cdot> n)"
  assumes Aexp_subst_App_Lam: "Aexp (e'[y::=x]) \<sqsubseteq> Aexp (App (Lam [y]. e') x)"
  assumes Aexp_App: "Aexp (App e x) \<cdot> n = Aexp e \<cdot>(inc\<cdot>n) \<squnion> AE_singleton x (up\<cdot>0)"
  assumes Aexp_Lam: "Afix (asToHeap as @ \<Gamma>)\<cdot>F\<cdot>(Aexp e\<cdot>n) \<sqsubseteq> Afix \<Gamma>\<cdot>F\<cdot>(Aexp (Terms.Let as e)\<cdot>n)"
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

lemma Aexp'_Var: "Aexp' (Var x) \<cdot> n = AE_singleton x n"
  unfolding Aexp'_def
  by (cases n) (simp_all add: Aexp_Var)

lemma Aexp'_Lam: "Afix (asToHeap as @ \<Gamma>)\<cdot>F\<cdot>(Aexp' e\<cdot>n) \<sqsubseteq> Afix \<Gamma>\<cdot>F\<cdot>(Aexp' (Terms.Let as e)\<cdot>n)"
proof(cases n)
  case bottom
  moreover
  have "Afix (asToHeap as @ \<Gamma>)\<cdot>F\<cdot>\<bottom> \<sqsubseteq> Afix \<Gamma>\<cdot>F\<cdot>\<bottom>" sorry
  ultimately
  show ?thesis by simp
next
  case up
  thus ?thesis by (simp add: Aexp_Lam)
qed

lemma AFix_above_arg: "ae \<sqsubseteq> Afix \<Gamma> \<cdot> F \<cdot> ae"
  apply (simp add: Aexp_Var Afix_eq ABind_def AE_singleton_def)
  apply (subst fix_eq)
  apply simp
  done

lemma Afix_below_var: "Afix ((x,e) # \<Gamma>) \<cdot> F \<cdot> (Aexp' e\<cdot>n) \<sqsubseteq> Afix ((x,e) # \<Gamma>)\<cdot> F \<cdot>(Aexp' (Var x)\<cdot>n)"
proof-
  have "(\<mu> xa. Aexp' e\<cdot>n \<squnion> (Aexp' e\<cdot>(xa x) \<squnion> (ABinds (delete x \<Gamma>)\<cdot>xa \<squnion> F\<cdot>xa))) \<sqsubseteq> (\<mu> xa. AE_singleton x n \<squnion> (Aexp' e\<cdot>(xa x) \<squnion> (ABinds (delete x \<Gamma>)\<cdot>xa \<squnion> F\<cdot>xa)))" (is "fix\<cdot>?F1 \<sqsubseteq> fix\<cdot>?F2")
  proof(rule fix_least_below)
    have F2x: "n \<sqsubseteq> (fix \<cdot> ?F2) x" by (subst fix_eq) (simp add: AE_singleton_def cont_fun)

    have "?F1 \<cdot> (fix \<cdot> ?F2) \<sqsubseteq> ?F2 \<cdot> (fix \<cdot> ?F2)"
    apply (simp add: cont_fun)
    apply (auto intro: join_below simp  add: below_trans[OF _ join_above2]  below_trans[OF _ join_above1] monofun_cfun_arg F2x)
    done
    thus "?F1 \<cdot> (fix \<cdot> ?F2) \<sqsubseteq> (fix \<cdot> ?F2)" unfolding  fix_eq[symmetric].
  qed
  thus ?thesis by (simp add: Aexp_Var Afix_eq ABind_def cont_fun Aexp'_Var)
qed
  
lemma Afix_reorder: "map_of \<Gamma> = map_of \<Delta> \<Longrightarrow> Afix \<Gamma> = Afix \<Delta>"
  by (intro cfun_eqI)(simp add: Afix_eq cong: Abinds_reorder)

lemma  "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : v \<Longrightarrow> 
        supp F \<subseteq> supp (L, \<Delta>, v) \<Longrightarrow>
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
  also have "\<dots>  = Afix \<Delta> \<cdot> (ABind x z \<squnion> F) \<cdot>(Aexp' z\<cdot>n)" unfolding `delete x \<Delta> = \<Delta>`..
  also have "\<dots> = Afix \<Delta> \<cdot> ((\<Lambda> ae . Aexp' z \<cdot> (ae x)) \<squnion> F) \<cdot> (Aexp' z\<cdot>n)" unfolding ABind_def..
  also have "\<dots> = Afix \<Delta> \<cdot> ((\<Lambda> ae . Afix \<Delta> \<cdot> ID \<cdot> (Aexp' z \<cdot> (ae x))) \<squnion> F) \<cdot>(Aexp' z\<cdot>n)" by (rule arg_cong[OF Afix_duplicate_binds]) (simp add: cont_fun)
  also have "\<dots> \<sqsubseteq> Afix (delete x \<Gamma>) \<cdot> ((\<Lambda> ae. Afix \<Delta> \<cdot> ID \<cdot> (Aexp' z \<cdot> (ae x))) \<squnion> F) \<cdot>(Aexp' e\<cdot>n)"
    by (rule IH)
  also have "\<dots> \<sqsubseteq> Afix (delete x \<Gamma>) \<cdot> ((\<Lambda> ae. Afix (delete x \<Gamma>) \<cdot> ID \<cdot> (Aexp' e \<cdot> (ae x))) \<squnion> F) \<cdot>(Aexp' e\<cdot>n)"
    by (intro monofun_cfun_fun monofun_cfun_arg)(auto intro: IH  join_mono simp add: cfun_below_iff cont_fun)
  also have "\<dots> = Afix (delete x \<Gamma>) \<cdot> ((\<Lambda> ae. Aexp' e \<cdot> (ae x)) \<squnion> F)\<cdot>(Aexp' e\<cdot>n)" by (rule arg_cong[OF Afix_duplicate_binds, symmetric]) (simp add: cont_fun)
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


end

end
