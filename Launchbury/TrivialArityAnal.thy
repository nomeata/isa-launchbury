theory TrivialArityAnal
imports ArityCorrect "Arity-Nominal" "Env-Nominal"
begin

definition Trivial_Aexp :: "exp \<Rightarrow> Arity \<rightarrow> AEnv"
  where "Trivial_Aexp e = (\<Lambda> n. (\<lambda> x. up\<cdot>0) f|` fv e)"

lemma Trivial_Aexp_eqvt[eqvt]: "\<pi> \<bullet>  (Trivial_Aexp e) = Trivial_Aexp (\<pi> \<bullet> e)"
  unfolding Trivial_Aexp_def
  apply perm_simp
  apply (simp add: Abs_cfun_eqvt)
  done

lemma Trivial_Aexp_simp: "Trivial_Aexp e \<cdot> n = (\<lambda> x. up\<cdot>0) f|` fv e"
  unfolding Trivial_Aexp_def by simp

lemma edom_Trivial_Aexp[simp]: "edom (Trivial_Aexp e \<cdot> n) = fv e"
  by (auto simp add: edom_def env_restr_def Trivial_Aexp_def) 

lemma Trivial_Aexp_eq[iff]: "Trivial_Aexp e \<cdot> n = Trivial_Aexp e' \<cdot> n' \<longleftrightarrow> fv e = (fv e' :: var set)"
  apply (auto simp add: Trivial_Aexp_simp env_restr_def)
  apply (metis up_defined)+
  done
  
lemma below_Trivial_Aexp[simp]: "(ae \<sqsubseteq> Trivial_Aexp e \<cdot> n) \<longleftrightarrow> edom ae \<subseteq> fv e"
  by (auto dest:fun_belowD intro!: fun_belowI  simp add: Trivial_Aexp_def env_restr_def edom_def split:if_splits)


interpretation ArityAnalysis Trivial_Aexp.
interpretation EdomArityAnalysis Trivial_Aexp  by default simp


interpretation CorrectArityAnalysis Trivial_Aexp
proof default
  fix \<pi>
  show "\<pi> \<bullet> Trivial_Aexp = Trivial_Aexp" by perm_simp rule
next
  fix n x
  show "up\<cdot>n \<sqsubseteq> (Trivial_Aexp (Var x)\<cdot>n) x"
    by (simp add: Trivial_Aexp_simp)
next
  fix e' y x
  show "Trivial_Aexp e'[y::=x] \<sqsubseteq> Trivial_Aexp (App (Lam [y]. e') x)"
    by (fastforce intro: cfun_belowI env_restr_mono2 dest: set_mp[OF fv_subst_subset])
next
  fix e x n
  show "Trivial_Aexp (App e x)\<cdot>n = Trivial_Aexp e\<cdot>(inc\<cdot>n) \<squnion> AE_singleton x\<cdot>(up\<cdot>0)"
    by (auto simp add: Trivial_Aexp_def env_restr_def )
next
  fix y e n
  show "Trivial_Aexp (Lam [y]. e)\<cdot>n = env_delete y (Trivial_Aexp e\<cdot>(pred\<cdot>n))"
    by (auto simp add: Trivial_Aexp_simp env_delete_restr Diff_eq inf_commute)
next
  fix x y :: var and S e a
  assume "x \<notin> S" and "y \<notin> S"
  thus "Trivial_Aexp e[x::=y]\<cdot>a f|` S = Trivial_Aexp e\<cdot>a f|` S"
    by (auto simp add: Trivial_Aexp_simp fv_subst_eq intro!: arg_cong[where f = "\<lambda> S. env_restr S e" for e])
qed

end

