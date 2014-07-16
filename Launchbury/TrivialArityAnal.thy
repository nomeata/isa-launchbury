theory TrivialArityAnal
imports ArityCorrect
begin

definition Trivial_Aexp :: "exp \<Rightarrow> Arity \<rightarrow> AEnv"
  where "Trivial_Aexp e = (\<Lambda> n. (\<lambda> x. up\<cdot>0) f|` fv e)"

lemma Trivial_Aexp_simp: "Trivial_Aexp e \<cdot> n = (\<lambda> x. up\<cdot>0) f|` fv e"
  unfolding Trivial_Aexp_def by simp

lemma edom_Trivial_Aexp[simp]: "edom (Trivial_Aexp e \<cdot> n) = fv e"
  by (auto simp add: edom_def env_restr_def Trivial_Aexp_def) 

lemma below_Trivial_Aexp[simp]: "(ae \<sqsubseteq> Trivial_Aexp e \<cdot> n) \<longleftrightarrow> edom ae \<subseteq> fv e"
  by (auto dest:fun_belowD intro!: fun_belowI  simp add: Trivial_Aexp_def env_restr_def edom_def split:if_splits)


interpretation ArityAnalysis Trivial_Aexp.
interpretation EdomArityAnalysis Trivial_Aexp  by default simp


interpretation CorrectArityAnalysis Trivial_Aexp
proof default
  fix e' y x
  show "Trivial_Aexp e'[y::=x] \<sqsubseteq> Trivial_Aexp (App (Lam [y]. e') x)"
    by (fastforce intro: cfun_belowI env_restr_mono2 dest: set_mp[OF fv_subst_subset])
next
  fix e x n
  show "Trivial_Aexp (App e x)\<cdot>n = Trivial_Aexp e\<cdot>(inc\<cdot>n) \<squnion> AE_singleton x\<cdot>(up\<cdot>0)"
    by (auto simp add: Trivial_Aexp_def env_restr_def )
next
  fix as e n
  show "Afix as\<cdot>(Trivial_Aexp e\<cdot>n) f|` (- domA as) \<sqsubseteq> Trivial_Aexp (Terms.Let as e)\<cdot>n"
  by (auto dest: set_mp[OF Afix_edom])
next
  fix n x
  show "up\<cdot>n \<sqsubseteq> (Trivial_Aexp (Var x)\<cdot>n) x"
    by (simp add: Trivial_Aexp_def)
qed

