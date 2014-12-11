theory CoCallAnalysisBinds
imports CoCallAnalysis AEnv  "AList-Utils-HOLCF"
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

(*
fun ccBinds :: "heap \<Rightarrow> ((AEnv \<times> CoCalls) \<rightarrow> CoCalls)"
  where "ccBinds [] = csnd"
     |  "ccBinds ((v,e)#binds) = ccBind v e \<squnion> ccBinds (delete v binds)"
*)
term lub
definition ccBinds :: "heap \<Rightarrow> ((AEnv \<times> CoCalls) \<rightarrow> CoCalls)"
  where "ccBinds \<Gamma> = (\<Lambda> i. (\<Squnion>v\<mapsto>e\<in>map_of \<Gamma>. ccBind v e\<cdot>i))"
lemma ccBinds_eq:
  "ccBinds \<Gamma>\<cdot>i = (\<Squnion>v\<mapsto>e\<in>map_of \<Gamma>. ccBind v e\<cdot>i)" sorry

lemma ccBinds_strict[simp]: "ccBinds \<Gamma>\<cdot>\<bottom>=\<bottom>"
  unfolding ccBinds_eq
  by (cases "\<Gamma> = []") simp_all

lemma ccBinds_strict'[simp]: "ccBinds \<Gamma>\<cdot>(\<bottom>,\<bottom>)=\<bottom>"
  by (metis CoCallAnalysis.ccBinds_strict Pair_bottom_iff)

lemma ccBinds_fun_upd[simp]:
  "(\<Squnion>k\<mapsto>v\<in>m(k' \<mapsto> v'). e k v) = e k' v' \<squnion> (\<Squnion>k\<mapsto>v\<in>m(k':=None). e k v)"
 sorry

lemma ccBinds_reorder1:
  assumes "map_of \<Gamma> v = Some e"
  shows "ccBinds \<Gamma> = ccBind v e \<squnion> ccBinds (delete v \<Gamma>)"
proof-
  from assms 
  have "map_of \<Gamma> = map_of ((v,e) # delete v \<Gamma>)" by (metis map_of_delete_insert)
  thus ?thesis
    by (auto intro: cfun_eqI simp add: ccBinds_eq delete_set_none)
qed

lemma ccBind_below_ccBinds: "map_of \<Gamma> x = Some e \<Longrightarrow> ccBind x e\<cdot>ae \<sqsubseteq> (ccBinds \<Gamma>\<cdot>ae)"
  by (auto simp add: ccBinds_eq)

(*
lemma ccBinds_lub: "ccBinds \<Gamma>\<cdot>(ae,G) = lub {ccBind x e\<cdot>(ae,G) | x e . map_of \<Gamma> x = Some e} \<squnion> G"
proof (induction rule: ccBinds.induct[case_names Nil Cons])
  case Nil thus ?case by simp
next
  case (Cons v e \<Gamma>)
  have "{ccBind x ea\<cdot>(ae, G) |x ea. map_of ((v, e) # \<Gamma>) x = Some ea} =
        insert (ccBind v e\<cdot>(ae, G)) {ccBind x ea\<cdot>(ae, G) |x ea. map_of (delete v \<Gamma>) x = Some ea}"
    by auto
  hence "lub {ccBind x ea\<cdot>(ae, G) |x ea. map_of ((v, e) # \<Gamma>) x = Some ea}
     = ccBind v e\<cdot>(ae, G) \<squnion> lub {ccBind x ea\<cdot>(ae, G) |x ea. map_of (delete v \<Gamma>) x = Some ea}"
     by (simp only: lub_insert)
  thus ?case
    using Cons by simp
qed
*)     

definition ccBindsExtra :: "heap \<Rightarrow> ((AEnv \<times> CoCalls) \<rightarrow> CoCalls)"
  where "ccBindsExtra \<Gamma> = (\<Lambda> i.  snd i \<squnion> ccBinds \<Gamma> \<cdot> i  \<squnion> (\<Squnion>x\<mapsto>e\<in>map_of \<Gamma>. ccProd (fv e) (ccNeighbors (domA \<Gamma>) (snd i))))"


lemma ccBindsExtra_simp: "ccBindsExtra \<Gamma> \<cdot> i = snd i \<squnion> ccBinds \<Gamma> \<cdot> i \<squnion> (\<Squnion>x\<mapsto>e\<in>map_of \<Gamma>. ccProd (fv e) (ccNeighbors (domA \<Gamma>) (snd i)))"
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
  unfolding CoCallAnalysis.ccBinds_eq
  apply (perm_simp) 
  apply rule
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
  apply (rule cfun_eqI)
  unfolding CoCallAnalysis.ccBinds_eq
  apply (rule arg_cong[OF mapCollect_cong])
  apply (rule arg_cong[OF ccBind_cong])
  apply auto
  by (metis imageI map_of_is_SomeD snd_conv)

lemma ccBindsExtra_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> cccexp1 e = cccexp2 e); heap1 = heap2 \<rbrakk>
      \<Longrightarrow> CoCallAnalysis.ccBindsExtra cccexp1 heap1 = CoCallAnalysis.ccBindsExtra cccexp2 heap2"
  apply (rule cfun_eqI)
  unfolding CoCallAnalysis.ccBindsExtra_simp
  apply (rule arg_cong2[OF ccBinds_cong mapCollect_cong]) 
  apply simp+
  (*
  apply (rule arg_cong[OF ccBinds_cong])
  apply simp+
  *)
  done


end
