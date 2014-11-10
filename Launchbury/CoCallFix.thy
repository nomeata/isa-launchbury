theory CoCallFix
imports CoCallAnalysis AEnv ArityCorrect
begin

locale CoCallArityAnalysis =
  fixes cccExp :: "exp \<Rightarrow> (Arity \<rightarrow> AEnv \<times> CoCalls)"
begin
sublocale ArityAnalysis  "\<lambda> e. (\<Lambda> a. fst (cccExp e \<cdot> a))".
sublocale CoCallAnalysis  "\<lambda> e. (\<Lambda> a. snd (cccExp e \<cdot> a))".

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

definition cccFix ::  "heap \<Rightarrow> ((AEnv \<times> CoCalls) \<rightarrow> (AEnv \<times> CoCalls))"
  where "cccFix \<Gamma> = (\<Lambda> i. (\<mu>  i'. (ABinds \<Gamma> \<cdot> (fst i'), ccBindsExtra \<Gamma> \<cdot> i') \<squnion> i))"

lemma cccFix_eq: "cccFix \<Gamma> \<cdot> i = (\<mu>  i'. (ABinds \<Gamma> \<cdot> (fst i'), ccBindsExtra \<Gamma> \<cdot> i') \<squnion> i)"
  unfolding cccFix_def by simp

lemma cccFix_strict[simp]: "cccFix \<Gamma> \<cdot> \<bottom> = \<bottom>"
  unfolding cccFix_eq
  by (rule fix_eqI) auto

(*
lemma cccFix_least_below: "Binds \<Gamma> \<cdot> (fst ae') \<sqsubseteq> fst ae' \<Longrightarrow> ae \<sqsubseteq> ae' \<Longrightarrow> cccFix \<Gamma> \<cdot> ae \<sqsubseteq> ae'"
  unfolding cccFix_eq
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

lemma ccBind_eqvt[eqvt]: "\<pi> \<bullet> (CoCallArityAnalysis.ccBind cccExp x e) = CoCallArityAnalysis.ccBind (\<pi> \<bullet> cccExp) (\<pi> \<bullet> x) (\<pi> \<bullet> e)"
proof-
  {
  fix \<pi> ae G
  have "\<pi> \<bullet> ((CoCallArityAnalysis.ccBind cccExp x e) \<cdot> (ae,G)) = CoCallArityAnalysis.ccBind (\<pi> \<bullet> cccExp) (\<pi> \<bullet> x) (\<pi> \<bullet> e) \<cdot> (\<pi> \<bullet> ae, \<pi> \<bullet> G)"
    unfolding CoCallArityAnalysis.ccBind_eq
    by perm_simp (simp add: Abs_cfun_eqvt)
  }
  thus ?thesis by (auto intro: cfun_eqvtI)
qed

lemma ccBinds_eqvt[eqvt]: "\<pi> \<bullet> (CoCallArityAnalysis.ccBinds cccExp \<Gamma>) = CoCallArityAnalysis.ccBinds (\<pi> \<bullet> cccExp) (\<pi> \<bullet> \<Gamma>)"
  apply (rule cfun_eqvtI)
  apply (induction \<Gamma> rule: CoCallArityAnalysis.ccBinds.induct)
  apply (simp add: CoCallArityAnalysis.ccBinds.simps)
  apply (simp add: CoCallArityAnalysis.ccBinds.simps, perm_simp, simp)
  done

lemma ccBindsExtra_eqvt[eqvt]: "\<pi> \<bullet> (CoCallArityAnalysis.ccBindsExtra cccExp \<Gamma>) = CoCallArityAnalysis.ccBindsExtra (\<pi> \<bullet> cccExp) (\<pi> \<bullet> \<Gamma>)"
  by (rule cfun_eqvtI) (simp add: CoCallArityAnalysis.ccBindsExtra_def)

lemma cccFix_eqvt[eqvt]: "\<pi> \<bullet> (CoCallArityAnalysis.cccFix cccExp \<Gamma>) = CoCallArityAnalysis.cccFix  (\<pi> \<bullet> cccExp) (\<pi> \<bullet> \<Gamma>)"
  unfolding CoCallArityAnalysis.cccFix_def
  by perm_simp (simp add: Abs_cfun_eqvt)

lemma ccExp'_cong: 
  "cccexp1 e = cccexp2 e \<Longrightarrow> CoCallAnalysis.ccExp' cccexp1 e = CoCallAnalysis.ccExp' cccexp2 e"
  unfolding CoCallAnalysis.ccExp'_def by simp
  
lemma ccBind_cong[fundef_cong]:
  "cccexp1 e = cccexp2 e \<Longrightarrow> CoCallArityAnalysis.ccBind cccexp1 x e = CoCallArityAnalysis.ccBind cccexp2 x e "
  apply (rule cfun_eqI)
  apply (case_tac xa)
  apply (auto simp add: CoCallArityAnalysis.ccBind_eq cong: ccExp'_cong)
  done

lemma ccBinds_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> cccexp1 e = cccexp2 e); heap1 = heap2 \<rbrakk>
      \<Longrightarrow> CoCallArityAnalysis.ccBinds cccexp1 heap1 = CoCallArityAnalysis.ccBinds cccexp2 heap2"
  apply simp
  apply (induction heap2 arbitrary: heap1 rule: CoCallArityAnalysis.ccBinds.induct)
  apply (simp add: CoCallArityAnalysis.ccBinds.simps)
  apply (simp add: CoCallArityAnalysis.ccBinds.simps)
  by (metis "AList-Utils.dom_delete_subset" ccBind_cong contra_subsetD)


lemma ccBindsExtra_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> cccexp1 e = cccexp2 e); heap1 = heap2 \<rbrakk>
      \<Longrightarrow> CoCallArityAnalysis.ccBindsExtra cccexp1 heap1 = CoCallArityAnalysis.ccBindsExtra cccexp2 heap2"
  unfolding CoCallArityAnalysis.ccBindsExtra_def
  by (metis (mono_tags, hide_lams) ccBinds_cong)


lemma cccFix_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> cccexp1 e = cccexp2 e); heap1 = heap2 \<rbrakk>
      \<Longrightarrow> CoCallArityAnalysis.cccFix cccexp1 heap1 = CoCallArityAnalysis.cccFix cccexp2 heap2"
   unfolding CoCallArityAnalysis.cccFix_def
   apply (rule cong) back back
   defer
   apply (metis ccBindsExtra_cong)
   apply (rule arg_cong[OF Abinds_cong])
   apply metis
   apply metis
   done
  
end
