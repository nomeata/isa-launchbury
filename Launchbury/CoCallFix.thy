theory CoCallFix
imports CoCallAnalysis ArityAnalysisFix
begin

locale CoCallArityAnalysis = CoCallAnalysis + ArityAnalysis

context CoCallArityAnalysis
begin

definition ccBind :: "var \<Rightarrow> exp \<Rightarrow> ((AEnv \<times> CoCalls) \<rightarrow> CoCalls)"
  where "ccBind v e = (\<Lambda> (ae, G).  if (v--v\<notin>G) \<or> \<not> isLam e then cc_restr (fv e) (ccExp' e \<cdot> (ae v)) else ccSquare (fv e))"
(* paper has:  \<or> ae v = up\<cdot>0, but that is not monotone! But should give the same result. *)

lemma ccBind_eq[simp]: "ccBind v e \<cdot> (ae, G) = (if (v--v\<notin>G) \<or> \<not> isLam e then cc_restr (fv e) (ccExp' e \<cdot> (ae v)) else ccSquare (fv e))"
  unfolding ccBind_def
  apply (rule cfun_beta_Pair)
  apply (rule cont_if_else_above)
  apply simp
  apply simp
  apply (auto dest: set_mp[OF ccFieldd_cc_restr])[1]
  (* Abstraction broken! Fix this. *)
  apply (case_tac p, auto, transfer, auto)[1]
  apply (rule adm_subst[OF cont_snd])
  apply (rule admI, thin_tac "chain ?x", transfer, auto)
  done

lemma ccBind_strict[simp]: "ccBind v e \<cdot> \<bottom> = \<bottom>"
  by (auto simp add: inst_prod_pcpo simp del: Pair_strict)

fun ccBinds :: "heap \<Rightarrow> ((AEnv \<times> CoCalls) \<rightarrow> CoCalls)"
  where "ccBinds [] = csnd"
     |  "ccBinds ((v,e)#binds) = ccBind v e \<squnion> ccBinds (delete v binds)"

lemma ccBinds_strict[simp]: "ccBinds \<Gamma>\<cdot>\<bottom>=\<bottom>"
  by (induct \<Gamma> rule: ccBinds.induct) auto

lemma ccBinds_strict'[simp]: "ccBinds \<Gamma>\<cdot>(\<bottom>,\<bottom>)=\<bottom>"
  by (induct \<Gamma> rule: ccBinds.induct) auto

lemma ccBinds_reorder1: "map_of \<Gamma> v = Some e \<Longrightarrow> ccBinds \<Gamma> = ccBind v e \<squnion> ccBinds (delete v \<Gamma>)"
proof (induction \<Gamma> rule: ccBinds.induct)
  case 1 thus ?case by simp
next
  case (2 v' e' \<Gamma>)
  thus ?case
  apply (cases "v' = v")
  apply auto
  apply (metis (hide_lams, no_types) join_assoc delete_twist join_comm)
  done
qed

definition ccBindsExtra :: "heap \<Rightarrow> ((AEnv \<times> CoCalls) \<rightarrow> CoCalls)"
  where "ccBindsExtra \<Gamma> = (\<Lambda> i.  ccBinds \<Gamma> \<cdot> i \<squnion> ccProd (fv \<Gamma> - domA \<Gamma>) (ccNeighbors (domA \<Gamma>) (ccBinds \<Gamma> \<cdot> i)))"

lemma ccBindsExtra_simp: "ccBindsExtra \<Gamma> \<cdot> i = ccBinds \<Gamma> \<cdot> i \<squnion> ccProd (fv \<Gamma> - domA \<Gamma>) (ccNeighbors (domA \<Gamma>) (ccBinds \<Gamma> \<cdot> i))"
  unfolding ccBindsExtra_def by simp

lemma ccBindsExtra_strict[simp]: "ccBindsExtra \<Gamma> \<cdot> \<bottom> = \<bottom>"
  by (auto simp add: ccBindsExtra_simp inst_prod_pcpo simp del: Pair_strict)

definition ccFix ::  "heap \<Rightarrow> ((AEnv \<times> CoCalls) \<rightarrow> (AEnv \<times> CoCalls))"
  where "ccFix \<Gamma> = (\<Lambda> i. (\<mu>  i'. (ABinds \<Gamma> \<cdot> (fst i'), ccBindsExtra \<Gamma> \<cdot> i') \<squnion> i))"

lemma ccFix_eq: "ccFix \<Gamma> \<cdot> i = (\<mu>  i'. (ABinds \<Gamma> \<cdot> (fst i'), ccBindsExtra \<Gamma> \<cdot> i') \<squnion> i)"
  unfolding ccFix_def by simp

lemma ccFix_strict[simp]: "ccFix \<Gamma> \<cdot> \<bottom> = \<bottom>"
  unfolding ccFix_eq
  by (rule fix_eqI) auto

(*
lemma ccFix_least_below: "Binds \<Gamma> \<cdot> (fst ae') \<sqsubseteq> fst ae' \<Longrightarrow> ae \<sqsubseteq> ae' \<Longrightarrow> ccFix \<Gamma> \<cdot> ae \<sqsubseteq> ae'"
  unfolding ccFix_eq
  by (auto intro: fix_least_below)

lemma Afix_unroll: "Afix \<Gamma>\<cdot>ae = ABinds \<Gamma> \<cdot> (Afix \<Gamma>\<cdot>ae) \<squnion> ae"
  unfolding Afix_eq
  apply (subst fix_eq)
  by simp

lemma Abinds_below_Afix: "ABinds \<Delta> \<sqsubseteq> Afix \<Delta>"
  apply (rule cfun_belowI)
  apply (simp add: Afix_eq)
  apply (subst fix_eq, simp)
  apply (rule below_trans[OF _ join_above1])
  apply (rule monofun_cfun_arg)
  apply (subst fix_eq, simp)
  done

lemma Afix_above_arg: "ae \<sqsubseteq> Afix \<Gamma> \<cdot> ae"
  by (metis (hide_lams, no_types) Abinds_below_Afix ArityAnalysis.ABinds_above_arg below_refl box_below monofun_cfun_fun)


lemma Abinds_Afix[simp]: "ABinds \<Gamma>\<cdot>(Afix \<Gamma>\<cdot>ae) = Afix \<Gamma>\<cdot>ae"
  unfolding Afix_eq
  apply (subst fix_eq) back apply simp
  apply (rule below_trans[OF ABinds_above_arg monofun_cfun_arg])
  apply (subst fix_eq) apply simp
  done

lemma Afix_reorder: "map_of \<Gamma> = map_of \<Delta> \<Longrightarrow> Afix \<Gamma> = Afix \<Delta>"
  by (intro cfun_eqI)(simp add: Afix_eq cong: Abinds_reorder)
*)

end

end
