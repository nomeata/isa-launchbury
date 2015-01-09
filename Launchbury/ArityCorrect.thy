theory ArityCorrect
imports ArityAnalysisAbinds (* "Vars-Nominal-HOLCF" *)
begin

locale EdomArityAnalysis = ArityAnalysis + 
  assumes Aexp_edom: "edom (Aexp e\<cdot>a) \<subseteq> fv e"
begin

  lemma Aexp'_edom: "edom (Aexp' e\<cdot>a) \<subseteq> fv e"
    by (cases a) (auto dest:set_mp[OF Aexp_edom])

  lemma fup_Aexp_edom: "edom (fup\<cdot>(Aexp e)\<cdot>a) \<subseteq> fv e"
    by (cases a) (auto dest:set_mp[OF Aexp_edom])
  
  lemma Aexp_fresh_bot[simp]: assumes "atom v \<sharp> e" shows "(Aexp e\<cdot>a) v = \<bottom>"
  proof-
    from assms have "v \<notin> fv e" by (metis fv_not_fresh)
    with Aexp_edom have "v \<notin> edom (Aexp e\<cdot>a)" by auto
    thus ?thesis unfolding edom_def by simp
  qed

end

locale SubstArityAnalysis = EdomArityAnalysis + 
  assumes Aexp_subst_restr: "x \<notin> S \<Longrightarrow> y \<notin> S \<Longrightarrow> (Aexp e[x::=y] \<cdot> a) f|` S = (Aexp e\<cdot>a) f|` S"

locale CorrectArityAnalysis' = SubstArityAnalysis +
(*  assumes Aexp_eqvt: "\<pi> \<bullet> Aexp = Aexp" *)
  assumes Aexp_Var: "up \<cdot> n \<sqsubseteq> (Aexp (Var x)\<cdot>n) x"
  assumes Aexp_App: "Aexp e \<cdot>(inc\<cdot>n) \<squnion> esing x \<cdot> (up\<cdot>0) \<sqsubseteq>  Aexp (App e x) \<cdot> n"
  assumes Aexp_Lam: "env_delete y (Aexp e \<cdot>(pred\<cdot>n)) \<sqsubseteq> Aexp (Lam [y]. e) \<cdot> n"

locale CorrectArityAnalysisAheap' = CorrectArityAnalysis' + 
  fixes Aheap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> AEnv"
  assumes Aheap_eqvt[eqvt]: "\<pi> \<bullet> Aheap = Aheap"
  assumes edom_Aheap: "edom (Aheap \<Gamma> e\<cdot> a) \<subseteq> domA \<Gamma>"
  assumes Aheap_subst: "x \<notin> domA \<Gamma> \<Longrightarrow> y \<notin> domA \<Gamma> \<Longrightarrow> Aheap \<Gamma>[x::h=y] e[x ::=y]  = Aheap \<Gamma> e"

locale CorrectArityAnalysisLet' = CorrectArityAnalysisAheap' +
  assumes Aexp_Let: "ABinds \<Gamma>\<cdot>(Aheap \<Gamma> e\<cdot>a) \<squnion> Aexp e\<cdot>a \<sqsubseteq> Aheap \<Gamma> e\<cdot>a \<squnion> Aexp (Let \<Gamma> e)\<cdot>a"

locale CorrectArityAnalysisLetNoCard = CorrectArityAnalysisLet' +
  assumes Aheap_heap3: "x \<in> thunks \<Gamma> \<Longrightarrow> (Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0"

context EdomArityAnalysis
begin
lemma Aexp'_lookup_fresh: "atom v \<sharp> e \<Longrightarrow> (Aexp' e\<cdot>a) v = \<bottom>"
  by (cases a) auto

lemma edom_AnalBinds: "edom (ABinds \<Gamma>\<cdot>ae) \<subseteq> fv \<Gamma>"
  by (induction \<Gamma> rule: ABinds.induct)
     (auto simp del: fun_meet_simp dest: set_mp[OF Aexp'_edom] dest: set_mp[OF fv_delete_subset])
end 

context SubstArityAnalysis
begin
  lemma Aexp_subst_upd: "(Aexp e[y::=x]\<cdot>n) \<sqsubseteq> (Aexp e\<cdot>n)(y := \<bottom>, x := up\<cdot>0)"
  proof-
    have "Aexp e[y::=x]\<cdot>n f|`(-{x,y}) = Aexp e\<cdot>n f|` (-{x,y})" by (rule Aexp_subst_restr) auto
  
    show ?thesis
    proof (rule fun_belowI)
    fix x'
      have "x' = x \<or> x' = y \<or> x' \<in> (-{x,y})" by auto
      thus "(Aexp e[y::=x]\<cdot>n) x' \<sqsubseteq> ((Aexp e\<cdot>n)(y := \<bottom>, x := up\<cdot>0)) x'"
      proof(elim disjE)
        assume "x' \<in> (-{x,y})"
        moreover
        have "Aexp e[y::=x]\<cdot>n f|`(-{x,y}) = Aexp e\<cdot>n f|` (-{x,y})" by (rule Aexp_subst_restr) auto
        note fun_cong[OF this, where x = x']
        ultimately
        show ?thesis by auto
      next
        assume "x' = x"
        thus ?thesis by simp
      next
        assume "x' = y"
        thus ?thesis
        using [[simp_trace]]
        by simp
     qed
   qed
  qed

  lemma Aexp_subst: "Aexp (e[y::=x])\<cdot>a \<sqsubseteq> env_delete y ((Aexp e)\<cdot>a) \<squnion> esing x\<cdot>(up\<cdot>0)"
    apply (rule below_trans[OF Aexp_subst_upd])
    apply (rule fun_belowI)
    apply auto
    done
end

context CorrectArityAnalysis'
begin

lemma Aexp_Var_singleton: "esing x \<cdot> (up\<cdot>n) \<sqsubseteq> Aexp (Var x) \<cdot> n"
  by (simp add: Aexp_Var)

lemma Aexp'_Var: "esing x \<cdot> n \<sqsubseteq> Aexp' (Var x) \<cdot> n"
  by (cases n) (simp_all add: Aexp_Var)

end


context CorrectArityAnalysisLet'
begin
lemma Aheap_nonrec:
  assumes "nonrec \<Delta>"
  shows "Aexp e\<cdot>a f|` domA \<Delta> \<sqsubseteq> Aheap \<Delta> e\<cdot>a"
proof-
  have "ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a \<sqsubseteq> Aheap \<Delta> e\<cdot>a \<squnion> Aexp (Let \<Delta> e)\<cdot>a" by (rule Aexp_Let)
  note env_restr_mono[where S = "domA \<Delta>", OF this]
  moreover
  from assms
  have "ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) f|` domA \<Delta> = \<bottom>"
    by (rule nonrecE) (auto simp add: fv_def fresh_def dest!: set_mp[OF Aexp'_edom])
  moreover
  have "Aheap \<Delta> e\<cdot>a f|` domA \<Delta> = Aheap \<Delta> e\<cdot>a" 
    by (rule env_restr_useless[OF edom_Aheap])
  moreover
  have "(Aexp (Let \<Delta> e)\<cdot>a) f|` domA \<Delta> = \<bottom>" 
    by (auto dest!: set_mp[OF Aexp_edom])
  ultimately
  show "Aexp e\<cdot>a f|` domA \<Delta> \<sqsubseteq> Aheap \<Delta> e\<cdot>a"
    by (simp add: env_restr_join)
qed
end


end
