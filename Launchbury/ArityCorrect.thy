theory ArityCorrect
imports ArityAnalysis Launchbury (* "Vars-Nominal-HOLCF" *)
begin

locale EdomArityAnalysis = ArityAnalysis + 
  assumes Aexp_edom: "edom (Aexp e\<cdot>a) \<subseteq> fv e"
begin

lemma Aexp'_edom: "edom (Aexp' e\<cdot>a) \<subseteq> fv e"
  by (cases a) (auto dest:set_mp[OF Aexp_edom])

lemma ABinds_edom: "edom (ABinds \<Gamma> \<cdot> ae) \<subseteq> fv \<Gamma> \<union> edom ae"
  apply (induct rule: ABinds.induct)
  apply simp
  apply (auto dest: set_mp[OF Aexp'_edom] simp del: fun_meet_simp)
  apply (drule (1) set_mp)
  apply (auto dest: set_mp[OF fv_delete_subset])
  done

end

locale CorrectArityAnalysis = EdomArityAnalysis +
  assumes Aexp_eqvt[eqvt]: "\<pi> \<bullet> Aexp = Aexp"
  assumes Aexp_Var: "up \<cdot> n \<sqsubseteq> (Aexp (Var x) \<cdot> n) x"
  assumes Aexp_subst_App_Lam: "Aexp (e[y::=x]) \<sqsubseteq> Aexp (App (Lam [y]. e) x)"
  assumes Aexp_Lam: "Aexp (Lam [y]. e) \<cdot> n = env_delete y (Aexp e \<cdot>(pred\<cdot>n))"
  assumes Aexp_App: "Aexp (App e x) \<cdot> n = Aexp e \<cdot>(inc\<cdot>n) \<squnion> AE_singleton x \<cdot> (up\<cdot>0)"
  assumes Aexp_subst_restr: "x \<notin> S \<Longrightarrow> y \<notin> S \<Longrightarrow> (Aexp e[x::=y] \<cdot> a) f|` S = (Aexp e\<cdot>a) f|` S"

locale CorrectArityAnalysisAheap = CorrectArityAnalysis + 
  fixes Aheap :: "heap \<Rightarrow> AEnv \<rightarrow> AEnv"
  assumes Aheap_eqvt[eqvt]: "\<pi> \<bullet> Aheap = Aheap"
  assumes edom_Aheap: "edom (Aheap \<Gamma> \<cdot> ae) \<subseteq> domA \<Gamma>"
  assumes Aheap_heap: "map_of \<Gamma> x = Some e' \<Longrightarrow> Aexp' e'\<cdot>((Aheap \<Gamma>\<cdot>ae) x) f|` domA \<Gamma> \<sqsubseteq> Aheap \<Gamma>\<cdot>ae"
  assumes Aheap_heap3: "map_of \<Gamma> x = Some e' \<Longrightarrow> \<not> isLam e' \<Longrightarrow> (Aheap \<Gamma>\<cdot>ae) x = up\<cdot>0"
  assumes Aheap_above_arg: "ae f|` domA \<Gamma> \<sqsubseteq> Aheap \<Gamma>\<cdot>ae"
  assumes Aheap_subst: "x \<notin> domA \<Gamma> \<Longrightarrow> y \<notin> domA \<Gamma> \<Longrightarrow> Aheap \<Gamma>[x::h=y] = Aheap \<Gamma>"
  assumes Aheap_cong: "ae f|` domA \<Gamma> = ae' f|` domA \<Gamma> \<Longrightarrow> Aheap \<Gamma>\<cdot>ae = Aheap \<Gamma>\<cdot>ae'"

locale CorrectArityAnalysisLet = CorrectArityAnalysisAheap +
  assumes Aheap_heap2: "map_of \<Gamma> x = Some e' \<Longrightarrow> Aexp' e'\<cdot>((Aheap \<Gamma>\<cdot>(Aexp e\<cdot>a)) x) f|` (- domA \<Gamma>) \<sqsubseteq>  Aexp (Let \<Gamma> e)\<cdot>a"
  assumes Aexp_Let_above: "Aexp e\<cdot>a f|` (- domA \<Gamma>) \<sqsubseteq> Aexp (Let \<Gamma> e)\<cdot>a"


context CorrectArityAnalysis
begin

lemma Aexp_Var_singleton: "AE_singleton x \<cdot> (up\<cdot>n) \<sqsubseteq> Aexp (Var x) \<cdot> n"
  by (simp add: Aexp_Var)

lemma Aexp'_Var: "AE_singleton x \<cdot> n \<sqsubseteq> Aexp' (Var x) \<cdot> n"
  by (cases n) (simp_all add: Aexp_Var)


lemma Aexp_lookup_fresh: "atom v \<sharp> e \<Longrightarrow> (Aexp e\<cdot>a) v = \<bottom>"
  using set_mp[OF Aexp_edom] unfolding edom_def by (auto simp add: fv_def fresh_def)

lemma Aexp'_lookup_fresh: "atom v \<sharp> e \<Longrightarrow> (Aexp' e\<cdot>a) v = \<bottom>"
  by (cases a) (auto simp add: Aexp_lookup_fresh)

lemma ABinds_lookup_fresh:
  "atom v \<sharp> \<Gamma> \<Longrightarrow> (ABinds \<Gamma>\<cdot>ae) v = ae v"
by (induct \<Gamma> rule: ABinds.induct) (auto simp add: fresh_Cons fresh_Pair Aexp'_lookup_fresh fresh_delete)

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
end

(*
context CorrectArityAnalysisAfix 
begin

sublocale CorrectArityAnalysisAheap Aexp "\<lambda> \<Gamma>. \<Lambda> ae. (Afix \<Gamma> \<cdot> ae f|` domA \<Gamma>)"
apply default
  defer

  apply simp

  apply simp
  apply (subst Env.lookup_env_restr)
  apply (metis domI dom_map_of_conv_domA)
  apply (rule env_restr_mono)
  apply (metis (erased, hide_lams) "HOLCF-Join-Classes.join_above2" ABind_eq ArityAnalysis.Abinds_Afix ArityAnalysis.Abinds_reorder1 join_comm monofun_cfun_fun)

  apply simp
  apply (subst Env.lookup_env_restr)
  apply (metis domI dom_map_of_conv_domA)
  apply (rule below_trans[OF _ Aexp_Let])
  apply (rule env_restr_mono)
  apply (metis (erased, hide_lams) "HOLCF-Join-Classes.join_above2" ABind_eq ArityAnalysis.Abinds_Afix ArityAnalysis.Abinds_reorder1 join_comm monofun_cfun_fun)
  defer

  apply simp
  apply (metis ArityAnalysis.Afix_above_arg env_restr_mono)

  apply (rule below_trans[OF _ Aexp_Let])
  apply (metis ArityAnalysis.Afix_above_arg env_restr_mono)
  done
  sor ry
end
*)

end
