theory CoCallAnalysisBinds
imports CoCallAnalysis AEnv
begin

context CoCallAnalysis
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
  by (cases "v' = v") (auto simp add: delete_twist)
qed

definition ccBindsExtra :: "heap \<Rightarrow> ((AEnv \<times> CoCalls) \<rightarrow> CoCalls)"
  where "ccBindsExtra \<Gamma> = (\<Lambda> i.  ccBinds \<Gamma> \<cdot> i \<squnion> ccProd (fv \<Gamma> - domA \<Gamma>) (ccNeighbors (domA \<Gamma>) (ccBinds \<Gamma> \<cdot> i)))"

lemma ccBindsExtra_simp: "ccBindsExtra \<Gamma> \<cdot> i = ccBinds \<Gamma> \<cdot> i \<squnion> ccProd (fv \<Gamma> - domA \<Gamma>) (ccNeighbors (domA \<Gamma>) (ccBinds \<Gamma> \<cdot> i))"
  unfolding ccBindsExtra_def by simp

lemma ccBindsExtra_strict[simp]: "ccBindsExtra \<Gamma> \<cdot> \<bottom> = \<bottom>"
  by (auto simp add: ccBindsExtra_simp inst_prod_pcpo simp del: Pair_strict)
end

lemma ccBind_eqvt[eqvt]: "\<pi> \<bullet> (CoCallAnalysis.ccBind cccExp x e) = CoCallAnalysis.ccBind (\<pi> \<bullet> cccExp) (\<pi> \<bullet> x) (\<pi> \<bullet> e)"
proof-
  {
  fix \<pi> ae G
  have "\<pi> \<bullet> ((CoCallAnalysis.ccBind cccExp x e) \<cdot> (ae,G)) = CoCallAnalysis.ccBind (\<pi> \<bullet> cccExp) (\<pi> \<bullet> x) (\<pi> \<bullet> e) \<cdot> (\<pi> \<bullet> ae, \<pi> \<bullet> G)"
    unfolding CoCallAnalysis.ccBind_eq
    by perm_simp (simp add: Abs_cfun_eqvt)
  }
  thus ?thesis by (auto intro: cfun_eqvtI)
qed

lemma ccBinds_eqvt[eqvt]: "\<pi> \<bullet> (CoCallAnalysis.ccBinds cccExp \<Gamma>) = CoCallAnalysis.ccBinds (\<pi> \<bullet> cccExp) (\<pi> \<bullet> \<Gamma>)"
  apply (rule cfun_eqvtI)
  apply (induction \<Gamma> rule: CoCallAnalysis.ccBinds.induct)
  apply (simp add: CoCallAnalysis.ccBinds.simps)
  apply (simp add: CoCallAnalysis.ccBinds.simps, perm_simp, simp)
  done

lemma ccBindsExtra_eqvt[eqvt]: "\<pi> \<bullet> (CoCallAnalysis.ccBindsExtra cccExp \<Gamma>) = CoCallAnalysis.ccBindsExtra (\<pi> \<bullet> cccExp) (\<pi> \<bullet> \<Gamma>)"
  by (rule cfun_eqvtI) (simp add: CoCallAnalysis.ccBindsExtra_def)

lemma ccExp'_cong: 
  "cccexp1 e = cccexp2 e \<Longrightarrow> CoCallAnalysis.ccExp' cccexp1 e = CoCallAnalysis.ccExp' cccexp2 e"
  unfolding CoCallAnalysis.ccExp'_def by simp

lemma ccBind_cong[fundef_cong]:
  "cccexp1 e = cccexp2 e \<Longrightarrow> CoCallAnalysis.ccBind cccexp1 x e = CoCallAnalysis.ccBind cccexp2 x e "
  apply (rule cfun_eqI)
  apply (case_tac xa)
  apply (auto simp add: CoCallAnalysis.ccBind_eq  cong: ccExp'_cong)
  done

lemma ccBinds_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> cccexp1 e = cccexp2 e); heap1 = heap2 \<rbrakk>
      \<Longrightarrow> CoCallAnalysis.ccBinds cccexp1 heap1 = CoCallAnalysis.ccBinds cccexp2 heap2"
  apply simp
  apply (induction heap2 arbitrary: heap1 rule: CoCallAnalysis.ccBinds.induct)
  apply (simp add: CoCallAnalysis.ccBinds.simps)
  apply (simp add: CoCallAnalysis.ccBinds.simps)
  by (metis "AList-Utils.dom_delete_subset" ccBind_cong contra_subsetD)
 
lemma ccBindsExtra_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> cccexp1 e = cccexp2 e); heap1 = heap2 \<rbrakk>
      \<Longrightarrow> CoCallAnalysis.ccBindsExtra cccexp1 heap1 = CoCallAnalysis.ccBindsExtra cccexp2 heap2"
  unfolding CoCallAnalysis.ccBindsExtra_def
  by (metis (mono_tags, hide_lams) ccBinds_cong)



end
