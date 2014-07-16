theory ArityAnalysisImpl
imports ArityCorrect "Arity-Nominal" "Nominal-HOLCF" "Env-Nominal" "Env-HOLCF"
begin

(*
locale CorrectArityAnalysis = ArityAnalysis +
  assumes Aexp_Var: "Aexp (Var x) \<cdot> n = AE_singleton x \<cdot> (up \<cdot> n)"
  assumes Aexp_subst_App_Lam: "Aexp (e'[y::=x]) \<sqsubseteq> Aexp (App (Lam [y]. e') x)"
  assumes Aexp_App: "Aexp (App e x) \<cdot> n = Aexp e \<cdot>(inc\<cdot>n) \<squnion> AE_singleton x \<cdot> (up\<cdot>0)"
  assumes Aexp_Let: "Afix as\<cdot>(Aexp e\<cdot>n) \<sqsubseteq> Aexp (Terms.Let as e)\<cdot>n"
  assumes Aexp_lookup_fresh: "atom v \<sharp> e \<Longrightarrow> (Aexp e\<cdot>a) v = \<bottom>"
begin
*)

nominal_function
  Aexp :: "exp \<Rightarrow> (Arity \<rightarrow> AEnv)"
where
  "Aexp (Var x) = (\<Lambda> n . AE_singleton x \<cdot> (up \<cdot> n))"
| "Aexp (Lam [x]. e) = (\<Lambda> n . (Aexp e \<cdot> (pred \<cdot> n)  f|` (fv (Lam [x]. e))))"
| "Aexp (App e x) = (\<Lambda> n . Aexp e  \<cdot> (inc \<cdot> n) \<squnion> (AE_singleton x \<cdot> (up \<cdot> 0)))"
| "Aexp (Terms.Let as e) = (\<Lambda> n . (ArityAnalysis.Afix Aexp as \<cdot> (Aexp e \<cdot> n)) f|` (fv (Terms.Let as e)))"
proof-
case goal1 show ?case
    unfolding eqvt_def Aexp_graph_aux_def
    apply rule
    apply (perm_simp)
    apply (simp add: Abs_cfun_eqvt)
    done
next
case goal3 thus ?case by (metis Terms.exp_strong_exhaust)
next
case (goal8 x e x' e')
  from goal8(5)
  show ?case
  proof(rule eqvt_lam_case)
    fix \<pi> :: perm
    assume *: "supp (-\<pi>) \<sharp>* (fv (Lam [x]. e) :: var set)" 
    {
    fix n
    have "Aexp_sumC (\<pi> \<bullet> e)\<cdot>(pred\<cdot>n)  f|` fv  (Lam [x]. e) = (-\<pi> \<bullet> Aexp_sumC (\<pi> \<bullet> e)\<cdot>(pred\<cdot>n)) f|` fv  (Lam [x]. e)"
      by (rule env_restr_perm[symmetric, OF *]) simp
    also have "\<dots> = ((Aexp_sumC e)\<cdot>(pred\<cdot>n)) f|` fv  (Lam [x]. e)"
      by (simp add: eqvt_at_apply[OF goal8(1)] pemute_minus_self)
    also note calculation
    }
    thus "(\<Lambda> n. Aexp_sumC (\<pi> \<bullet> e)\<cdot>(pred\<cdot>n) f|` fv (Lam [x]. e)) = (\<Lambda> n. Aexp_sumC e\<cdot>(pred\<cdot>n) f|` fv (Lam [x]. e))" by simp
  qed
next
case (goal13 as body as' body')
  from goal13(9)
  show ?case
  proof (rule eqvt_let_case)
    fix \<pi> :: perm
    assume *: "supp (-\<pi>) \<sharp>* (fv (Terms.Let as body) :: var set)"
    
    { fix n
      have "ArityAnalysis.Afix Aexp_sumC (\<pi> \<bullet> as)\<cdot>(Aexp_sumC (\<pi> \<bullet> body)\<cdot>n) f|` fv (Terms.Let as body)
      =  (- \<pi> \<bullet> ArityAnalysis.Afix Aexp_sumC (\<pi> \<bullet> as)\<cdot>(Aexp_sumC (\<pi> \<bullet> body)\<cdot>n)) f|` fv (Terms.Let as body)"
        by (rule env_restr_perm[OF *, symmetric]) simp
      also have "- \<pi> \<bullet> ArityAnalysis.Afix Aexp_sumC (\<pi> \<bullet> as)\<cdot>(Aexp_sumC (\<pi> \<bullet> body)\<cdot>n) = 
                       ArityAnalysis.Afix (- \<pi> \<bullet> Aexp_sumC) as\<cdot>((- \<pi> \<bullet> Aexp_sumC) body\<cdot>n)"
        by (simp add: pemute_minus_self)
      also have "ArityAnalysis.Afix (- \<pi> \<bullet> Aexp_sumC) as = ArityAnalysis.Afix Aexp_sumC as"
        by (rule Afix_cong[OF eqvt_at_apply[OF goal13(1)] refl])
      also have "(- \<pi> \<bullet> Aexp_sumC) body = Aexp_sumC body"
        by (rule eqvt_at_apply[OF goal13(2)])
      also note calculation
    }
    thus "(\<Lambda> n. ArityAnalysis.Afix Aexp_sumC (\<pi> \<bullet> as)\<cdot>(Aexp_sumC (\<pi> \<bullet> body)\<cdot>n) f|` fv (Terms.Let as body)) =
         (\<Lambda> n. ArityAnalysis.Afix Aexp_sumC as\<cdot>(Aexp_sumC body\<cdot>n) f|` fv (Terms.Let as body))" by (simp only:)
  qed
qed auto

nominal_termination by lexicographic_order

interpretation ArityAnalysis Aexp.

lemma Aexp_edom: "edom (Aexp e\<cdot>a) \<subseteq> fv e"
  by (nominal_induct arbitrary: a rule: exp_strong_induct) auto

lemma Aexp'_edom: "edom (Aexp' e\<cdot>a) \<subseteq> fv e"
  by (cases a) (auto dest:set_mp[OF Aexp_edom])

lemma ABinds_edom: "edom (ABinds \<Gamma> \<cdot> ae) \<subseteq> fv \<Gamma> \<union> edom ae"
  apply (induct rule: ABinds.induct)
  apply simp
  apply (auto dest: set_mp[OF Aexp'_edom] simp del: fun_meet_simp)
  apply (drule (1) set_mp)
  apply (auto dest: set_mp[OF fv_delete_subset])
  done
  

lemma Afix_edom: "edom (Afix \<Gamma> \<cdot> ae) \<subseteq> fv \<Gamma> \<union> edom ae"
  unfolding Afix_eq
  by (rule fix_ind[where P = "\<lambda> ae' . edom ae' \<subseteq> fv \<Gamma> \<union> edom ae"] )
     (auto dest: set_mp[OF ABinds_edom])

lemma Aexp_lam_simp[simp]: "Aexp (Lam [x]. e) \<cdot> n = env_delete x (Aexp e \<cdot> (pred \<cdot> n))"
proof-
  have "Aexp (Lam [x]. e) \<cdot> n = Aexp e\<cdot>(pred\<cdot>n) f|` (fv e - {x})" by simp
  also have "... = env_delete x (Aexp e\<cdot>(pred\<cdot>n)) f|` (fv e - {x})" by simp
  also have "\<dots> = env_delete x (Aexp e\<cdot>(pred\<cdot>n))"
     by (rule env_restr_useless) (auto dest: set_mp[OF Aexp_edom])
  finally show ?thesis.
qed
declare Aexp.simps(2)[simp del]

lemma Aexp_let_simp[simp]: "Aexp (Terms.Let \<Gamma> e) \<cdot> n = Afix \<Gamma>\<cdot>(Aexp e\<cdot>n) f|` (- domA \<Gamma>)"
proof-
  have "Aexp (Terms.Let \<Gamma> e) \<cdot> n  = Afix \<Gamma>\<cdot>(Aexp e\<cdot>n) f|` fv (Terms.Let \<Gamma> e)" by simp
  also have "\<dots> =  Afix \<Gamma>\<cdot>(Aexp e\<cdot>n) f|` (- domA \<Gamma>) f|` fv (Terms.Let \<Gamma> e)" by auto (metis Diff_eq Diff_idemp)
  also have "\<dots> = Afix \<Gamma>\<cdot>(Aexp e\<cdot>n) f|` (- domA \<Gamma>)"
     by (rule env_restr_useless) (auto dest: set_mp[OF Aexp_edom] set_mp[OF Afix_edom])
  finally show ?thesis.
qed
declare Aexp.simps(4)[simp del]


lemma edom_Afix: "(\<And>ea. ea \<in> snd ` set as \<Longrightarrow> \<forall>n. edom (Aexp_sum ea\<cdot>n) \<subseteq> fv ea) \<Longrightarrow>
   edom (ArityAnalysis.Afix Aexp_sum as\<cdot>x) \<subseteq> edom x \<union> \<Union>{ fv e | e.  e \<in> snd ` set as}"
   oops


lemma Aexp_fresh_bot[simp]: assumes "atom v \<sharp> e" shows "(Aexp e\<cdot>a) v = \<bottom>"
proof-
  from assms have "v \<notin> fv e" by (metis fv_not_fresh)
  with Aexp_edom have "v \<notin> edom (Aexp e\<cdot>a)" by auto
  thus ?thesis unfolding edom_def by simp
qed

lemma env_delete_below_cong[intro]:
  assumes "x \<noteq> v \<Longrightarrow> e1 x \<sqsubseteq> e2 x"
  shows "env_delete v e1  x \<sqsubseteq> env_delete v e2 x"
  using assms unfolding env_delete_def by auto

lemma Aexp_subst: "(Aexp e[y::=x]\<cdot>n) \<sqsubseteq> (Aexp e\<cdot>n)(y := \<bottom>, x := up\<cdot>0)"
proof (nominal_induct e avoiding: x y  arbitrary: n rule: exp_strong_induct)
  case (Var v) 
  thus ?case by auto
next
  case (App e v x y n)
  have "Aexp (App e v)[y::=x]\<cdot>n \<sqsubseteq> (Aexp e[y::=x]\<cdot>(inc\<cdot>n)) \<squnion> (AE_singleton (v[y::v=x])\<cdot>(up\<cdot>0))" by simp
  also have "Aexp e[y::=x]\<cdot>(inc\<cdot>n) \<sqsubseteq> (Aexp e\<cdot>(inc\<cdot>n))(y := \<bottom>, x := up\<cdot>0)" by (rule App.hyps)
  also have "(AE_singleton (v[y::v=x])\<cdot>(up\<cdot>0)) \<sqsubseteq> (AE_singleton v\<cdot>(up\<cdot>0))(y := \<bottom>, x := up\<cdot>0)" by simp
  also have "(Aexp e\<cdot>(inc\<cdot>n))(y := \<bottom>, x := up\<cdot>0) \<squnion> (AE_singleton v\<cdot>(up\<cdot>0))(y := \<bottom>, x := up\<cdot>0) 
    = (Aexp (App e v)\<cdot>n)(y := \<bottom>, x := up\<cdot>0)" by auto
  finally show ?case by this simp_all
next
  case (Lam v e)
  note Lam(1,2)[simp]
  have "Aexp (Lam [v]. e)[y::=x]\<cdot>n = env_delete v (Aexp e[y::=x]\<cdot>(pred\<cdot>n))" by simp
  also have "\<dots> \<sqsubseteq> env_delete v ((Aexp e\<cdot>(pred\<cdot>n))(y := \<bottom>, x := up\<cdot>0))"
    by (rule cont2monofunE[OF env_delete_cont Lam(3)])
  also have "\<dots> = (env_delete v (Aexp e\<cdot>(pred\<cdot>n)))(y := \<bottom>, x := up\<cdot>0)"
    using Lam(1,2) by (auto simp add: fresh_at_base)
  also have "\<dots> = (Aexp (Lam [v]. e)\<cdot>n)(y := \<bottom>, x := up\<cdot>0)" by simp
  finally show ?case.
next
  case (Let \<Gamma> e)
  hence "x \<notin> domA \<Gamma> " and "y \<notin> domA \<Gamma>"
    by (metis (erased, hide_lams) bn_subst domA_not_fresh fresh_def fresh_star_at_base fresh_star_def obtain_fresh subst_is_fresh(2))+
  
  note this[simp] Let(1,2)[simp]

  have "Aexp (Terms.Let \<Gamma> e)[y::=x]\<cdot>n \<sqsubseteq> Afix \<Gamma>[y::h=x]\<cdot>(Aexp e[y::=x]\<cdot>n) f|` ( - domA \<Gamma>)" by (simp add: fresh_star_Pair)
  also have "(Aexp e[y::=x]\<cdot>n) \<sqsubseteq> (Aexp e\<cdot>n)(y := \<bottom>, x := up\<cdot>0)" by fact
  also have "Afix \<Gamma>[y::h=x]\<cdot>((Aexp e\<cdot>n)(y := \<bottom>, x := up\<cdot>0)) \<sqsubseteq> (Afix \<Gamma>\<cdot>(Aexp e\<cdot>n))(y := \<bottom>, x := up\<cdot>0)"
    by (rule Afix_subst_approx[OF Let(3) `x \<notin> domA \<Gamma>` `y \<notin> domA \<Gamma>`])
  also have "(Afix \<Gamma>\<cdot>(Aexp e\<cdot>n))(y := \<bottom>, x := up\<cdot>0) f|` (- domA \<Gamma>) = (Afix \<Gamma>\<cdot>(Aexp e\<cdot>n) f|` (- domA \<Gamma>)) (y := \<bottom>, x := up\<cdot>0)" by auto
  also have "(Afix \<Gamma>\<cdot>(Aexp e\<cdot>n) f|` (- domA \<Gamma>)) = Aexp (Terms.Let \<Gamma> e)\<cdot>n" by simp
  finally show ?case by this simp_all
qed

interpretation CorrectArityAnalysis Aexp
proof default
  fix e' y x
  show "Aexp e'[y::=x] \<sqsubseteq> Aexp (App (Lam [y]. e') x)"
    apply (rule cfun_belowI)
    apply (rule below_trans[OF Aexp_subst])
    apply (rule fun_belowI)
    apply auto
    done
qed simp_all

end
