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

definition Trivial_Aheap :: "heap \<Rightarrow> AEnv \<rightarrow> AEnv" where
  "Trivial_Aheap \<Gamma> = (\<Lambda> ae. (\<lambda> x. up\<cdot>0) f|` domA \<Gamma>)"

lemma Trivial_Aheap_eqvt[eqvt]: "\<pi> \<bullet>  (Trivial_Aheap \<Gamma>) = Trivial_Aheap (\<pi> \<bullet> \<Gamma>)"
  unfolding Trivial_Aheap_def
  apply perm_simp
  apply (simp add: Abs_cfun_eqvt)
  done

lemma Trivial_Aheap_simp: "Trivial_Aheap \<Gamma> \<cdot> ae = (\<lambda> x. up\<cdot>0) f|` domA \<Gamma>"
  unfolding Trivial_Aheap_def by simp

interpretation CorrectArityAnalysisLet Trivial_Aexp Trivial_Aheap
proof default
  fix \<pi>
  show "\<pi> \<bullet> Trivial_Aheap = Trivial_Aheap" by perm_simp rule  
next
  fix \<Gamma> ae show "edom (Trivial_Aheap \<Gamma>\<cdot>ae) \<subseteq> domA \<Gamma>"
  by (simp add: Trivial_Aheap_simp)
next
  fix \<Gamma> :: heap and x :: var and  e' :: exp and  ae :: AEnv
  assume "map_of \<Gamma> x = Some e'"
  show "Aexp' e'\<cdot>((Trivial_Aheap \<Gamma>\<cdot>ae) x) f|` domA \<Gamma> \<sqsubseteq> Trivial_Aheap \<Gamma>\<cdot>ae"
    by (auto intro: env_restr_belowI simp add: Trivial_Aheap_simp)
next
  fix \<Gamma> :: heap and x :: var and  e' :: exp and  ae :: AEnv
  assume "\<not> isLam e'" 
  assume "map_of \<Gamma> x = Some e'"
  hence "x \<in> domA \<Gamma>" by (metis domI dom_map_of_conv_domA)
  thus "(Trivial_Aheap \<Gamma>\<cdot>ae) x = up\<cdot>0" by (simp add: Trivial_Aheap_simp)
next
  fix \<Gamma> ae
  show "ae f|` domA \<Gamma> \<sqsubseteq> Trivial_Aheap \<Gamma>\<cdot>ae"
    by (auto intro: env_restr_belowI simp add: Trivial_Aheap_simp)
next
  fix x y :: var and \<Gamma> :: heap
  assume "x \<notin> domA \<Gamma>" and "y \<notin> domA \<Gamma>"
  thus "Trivial_Aheap \<Gamma>[x::h=y] = Trivial_Aheap \<Gamma>"
    by (auto intro: cfun_eqI simp add: Trivial_Aheap_simp)
next
  fix \<Gamma> :: heap and ae ae' :: AEnv
  assume "ae f|` domA \<Gamma> = ae' f|` domA \<Gamma>"
  show "Trivial_Aheap \<Gamma>\<cdot>ae = Trivial_Aheap \<Gamma>\<cdot>ae'"
    by (simp add: Trivial_Aheap_simp)
next
  fix \<Gamma> :: heap and x :: var and  e' e :: exp and a :: Arity
  assume "map_of \<Gamma> x = Some e'"
  hence "x \<in> domA \<Gamma>" and "fv e' \<subseteq> fv \<Gamma>" 
    apply -
    apply (metis domI dom_map_of_conv_domA)
    apply (metis domA_from_set map_of_fv_subset map_of_is_SomeD option.sel)
    done
  thus "Aexp' e'\<cdot>((Trivial_Aheap \<Gamma>\<cdot>(Trivial_Aexp e\<cdot>a)) x) f|` (- domA \<Gamma>) \<sqsubseteq> Trivial_Aexp (Terms.Let \<Gamma> e)\<cdot>a"
    by (auto intro: env_restr_mono2 simp add: Trivial_Aheap_simp Trivial_Aexp_simp)
next
  fix \<Gamma> e a
  show "Trivial_Aexp e\<cdot>a f|` (- domA \<Gamma>) \<sqsubseteq> Trivial_Aexp (Terms.Let \<Gamma> e)\<cdot>a"
    by (auto intro: env_restr_mono2 simp add: Trivial_Aexp_simp)
qed

end

