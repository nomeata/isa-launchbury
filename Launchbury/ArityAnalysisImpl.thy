theory ArityAnalysisImpl
imports ArityAnalysisFix "Arity-Nominal" "Nominal-HOLCF" "Env-Nominal" "Env-HOLCF"
begin


fun thunks :: "heap \<Rightarrow> AEnv" where
  "thunks [] = \<bottom>"
  | "thunks ((x,e)#\<Gamma>) = (if isLam e then \<bottom> else AE_singleton x\<cdot>(up\<cdot>0)) \<squnion> thunks \<Gamma>"

lemma edom_thunks: "edom (thunks \<Gamma>) \<subseteq> domA \<Gamma>"
  by (induction \<Gamma> rule:thunks.induct) (auto simp del: fun_meet_simp)

lemma thunks_eqvt[eqvt]:
  "\<pi> \<bullet> thunks \<Gamma> = thunks (\<pi> \<bullet> \<Gamma>)"
  by (induction \<Gamma> rule:thunks.induct) (auto simp add: join_eqvt simp del: fun_meet_simp)

lemma thunks_subst[simp]:
  "thunks \<Gamma>[y::h=x] = thunks \<Gamma>"
  by (induction \<Gamma> rule:thunks.induct)  (auto simp del: fun_meet_simp app_strict )

lemma thunks_subst_approx:
  "y \<notin> domA \<Gamma> \<Longrightarrow> thunks \<Gamma>[y::h=x] \<sqsubseteq> (thunks \<Gamma>)(y := \<bottom>, x := up\<cdot>0)"
  by (auto intro!: fun_belowI dest!: contra_subsetD[OF edom_thunks] simp add: edomIff)
  

nominal_function
  Aexp :: "exp \<Rightarrow> (Arity \<rightarrow> AEnv)"
where
  "Aexp (GVar b x) = (\<Lambda> n . AE_singleton x \<cdot> (up \<cdot> n))"
| "Aexp (Lam [x]. e) = (\<Lambda> n . (Aexp e \<cdot> (pred \<cdot> n)  f|` (fv (Lam [x]. e))))"
| "Aexp (App e x) = (\<Lambda> n . Aexp e  \<cdot> (inc \<cdot> n) \<squnion> (AE_singleton x \<cdot> (up \<cdot> 0)))"
| "Aexp (Terms.Let as e) = (\<Lambda> n . (ArityAnalysis.Afix Aexp as \<cdot> (Aexp e \<cdot> n \<squnion> thunks as)) f|` (fv (Terms.Let as e)))"
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
      have "ArityAnalysis.Afix Aexp_sumC (\<pi> \<bullet> as)\<cdot>(Aexp_sumC (\<pi> \<bullet> body)\<cdot>n \<squnion> thunks (\<pi> \<bullet> as)) f|` fv (Terms.Let as body)
      =  (- \<pi> \<bullet> ArityAnalysis.Afix Aexp_sumC (\<pi> \<bullet> as)\<cdot>(Aexp_sumC (\<pi> \<bullet> body)\<cdot>n \<squnion> thunks (\<pi> \<bullet> as))) f|` fv (Terms.Let as body)"
        by (rule env_restr_perm[OF *, symmetric]) simp
      also have "- \<pi> \<bullet> ArityAnalysis.Afix Aexp_sumC (\<pi> \<bullet> as)\<cdot>(Aexp_sumC (\<pi> \<bullet> body)\<cdot>n \<squnion> thunks (\<pi> \<bullet> as)) = 
                       ArityAnalysis.Afix (- \<pi> \<bullet> Aexp_sumC) as\<cdot>((- \<pi> \<bullet> Aexp_sumC) body\<cdot>n \<squnion> thunks as)"
        by (simp add: pemute_minus_self)
      also have "ArityAnalysis.Afix (- \<pi> \<bullet> Aexp_sumC) as = ArityAnalysis.Afix Aexp_sumC as"
        by (rule Afix_cong[OF eqvt_at_apply[OF goal13(1)] refl])
      also have "(- \<pi> \<bullet> Aexp_sumC) body = Aexp_sumC body"
        by (rule eqvt_at_apply[OF goal13(2)])
      also note calculation
    }
    thus "(\<Lambda> n. ArityAnalysis.Afix Aexp_sumC (\<pi> \<bullet> as)\<cdot>(Aexp_sumC (\<pi> \<bullet> body)\<cdot>n \<squnion> thunks (\<pi> \<bullet> as)) f|` fv (Terms.Let as body)) =
         (\<Lambda> n. ArityAnalysis.Afix Aexp_sumC as\<cdot>(Aexp_sumC body\<cdot>n \<squnion> thunks as) f|` fv (Terms.Let as body))" by (simp only:)
  qed
qed auto

nominal_termination (eqvt) by lexicographic_order

interpretation ArityAnalysis Aexp.

lemma Aexp_edom': "edom (Aexp e\<cdot>a) \<subseteq> fv e"
  by (nominal_induct arbitrary: a rule: exp_strong_induct) auto

interpretation EdomArityAnalysis Aexp by default (rule Aexp_edom')

lemma Aexp_lam_simp[simp]: "Aexp (Lam [x]. e) \<cdot> n = env_delete x (Aexp e \<cdot> (pred \<cdot> n))"
proof-
  have "Aexp (Lam [x]. e) \<cdot> n = Aexp e\<cdot>(pred\<cdot>n) f|` (fv e - {x})" by simp
  also have "... = env_delete x (Aexp e\<cdot>(pred\<cdot>n)) f|` (fv e - {x})" by simp
  also have "\<dots> = env_delete x (Aexp e\<cdot>(pred\<cdot>n))"
     by (rule env_restr_useless) (auto dest: set_mp[OF Aexp_edom])
  finally show ?thesis.
qed
declare Aexp.simps(2)[simp del]

lemma Aexp_let_simp[simp]: "Aexp (Terms.Let \<Gamma> e) \<cdot> n = Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks \<Gamma>) f|` (- domA \<Gamma>)"
proof-
  have "Aexp (Terms.Let \<Gamma> e) \<cdot> n  = Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks \<Gamma>) f|` fv (Terms.Let \<Gamma> e)" by simp
  also have "\<dots> = Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks \<Gamma>) f|` (- domA \<Gamma>) f|` fv (Terms.Let \<Gamma> e)" by auto (metis Diff_eq Diff_idemp)
  also have "\<dots> = Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks \<Gamma>) f|` (- domA \<Gamma>)"
     by (rule env_restr_useless)
        (auto dest!: set_mp[OF Aexp_edom] set_mp[OF Afix_edom] set_mp[OF edom_thunks])
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

  have "Aexp (Terms.Let \<Gamma> e)[y::=x]\<cdot>n \<sqsubseteq> Afix \<Gamma>[y::h=x]\<cdot>(Aexp e[y::=x]\<cdot>n \<squnion> thunks \<Gamma>[y::h=x]) f|` ( - domA \<Gamma>)" by (simp add: fresh_star_Pair)
  also have "(Aexp e[y::=x]\<cdot>n) \<sqsubseteq> (Aexp e\<cdot>n)(y := \<bottom>, x := up\<cdot>0)" by fact
  also have "thunks \<Gamma>[y::h=x] \<sqsubseteq> (thunks \<Gamma>)(y := \<bottom>, x := up\<cdot>0)" by (rule thunks_subst_approx[OF `y \<notin> domA \<Gamma>`])
  also have "(Aexp e\<cdot>n)(y := \<bottom>, x := up\<cdot>0) \<squnion> (thunks \<Gamma>)(y := \<bottom>, x := up\<cdot>0) = (Aexp e\<cdot>n \<squnion> thunks \<Gamma>)(y := \<bottom>, x := up\<cdot>0)" by simp
  also have "Afix \<Gamma>[y::h=x]\<cdot>((Aexp e\<cdot>n \<squnion> thunks \<Gamma>)(y := \<bottom>, x := up\<cdot>0)) \<sqsubseteq> (Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks \<Gamma>))(y := \<bottom>, x := up\<cdot>0)"
    by (rule Afix_subst_approx[OF Let(3) `x \<notin> domA \<Gamma>` `y \<notin> domA \<Gamma>`])
  also have "(Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks \<Gamma>))(y := \<bottom>, x := up\<cdot>0) f|` (- domA \<Gamma>) = (Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks \<Gamma>) f|` (- domA \<Gamma>)) (y := \<bottom>, x := up\<cdot>0)" by auto
  also have "(Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks \<Gamma>) f|` (- domA \<Gamma>)) = Aexp (Terms.Let \<Gamma> e)\<cdot>n" by simp
  finally show ?case by this simp_all
qed

lemma env_delete_env_restr_swap:
  "env_delete x (env_restr S e) = env_restr S (env_delete x e)"
  by (metis (erased, hide_lams) env_delete_def env_restr_fun_upd env_restr_fun_upd_other fun_upd_triv lookup_env_restr_eq)

lemma Aexp_restr_subst:
  assumes "x \<notin> S" and "y \<notin> S"
  shows "(Aexp e[x::=y]\<cdot>a) f|` S = (Aexp e\<cdot>a) f|` S"
using assms
proof (nominal_induct e avoiding: x y  arbitrary: a  S rule: exp_strong_induct_set)
  case (Var v) 
  thus ?case by auto
next
  case (App e v)
  thus ?case by (auto simp add: env_restr_join simp del: fun_meet_simp)
next
  case (Lam v e)
  thus ?case
  by (auto simp add: env_restr_join env_delete_env_restr_swap[symmetric]  simp del: fun_meet_simp)
next
  case (Let \<Gamma> e)
  hence "x \<notin> domA \<Gamma> " and "y \<notin> domA \<Gamma>"
    by (metis (erased, hide_lams) bn_subst domA_not_fresh fresh_def fresh_star_at_base fresh_star_def obtain_fresh subst_is_fresh(2))+
  
  note this[simp] Let(1,2)[simp]

  from Let
  have "ArityAnalysis.Afix Aexp \<Gamma>[x::h=y]\<cdot>(Aexp e[x::=y]\<cdot>a \<squnion> thunks \<Gamma>) f|` (S \<union> domA \<Gamma>) = ArityAnalysis.Afix Aexp \<Gamma>\<cdot>(Aexp e\<cdot>a \<squnion> thunks \<Gamma>) f|` (S \<union> domA \<Gamma>)"
    apply (auto simp add: fresh_star_Pair)
    apply (subst Afix_restr_subst')
    apply auto[1]
    apply auto[3]
    apply (simp add: env_restr_join)
    apply (subst Afix_restr) back
    apply auto[1]
    apply (simp add: env_restr_join)
    done
  thus ?case using Let(1,2) by (auto simp add: fresh_star_Pair elim:env_restr_eq_subset[rotated])
qed

interpretation CorrectArityAnalysis Aexp
proof default
  fix \<pi> show "\<pi> \<bullet> Aexp = Aexp" by perm_simp rule
next
  fix e' y x
  show "Aexp e'[y::=x] \<sqsubseteq> Aexp (App (Lam [y]. e') x)"
    apply (rule cfun_belowI)
    apply (rule below_trans[OF Aexp_subst])
    apply (rule fun_belowI)
    apply auto
    done
next
  fix x y :: var and e :: exp and S and a 
  assume "x \<notin> S" and "y \<notin> S"
  thus "(Aexp e[x::=y]\<cdot>a) f|` S = (Aexp e\<cdot>a) f|` S" by (rule Aexp_restr_subst)
qed simp_all

definition Aheap where
  "Aheap \<Gamma> = (\<Lambda> ae. (Afix \<Gamma> \<cdot> (ae \<squnion> thunks \<Gamma>) f|` domA \<Gamma>))"

lemma Aheap_eqvt'[eqvt]:
  "\<pi> \<bullet> (Aheap \<Gamma>) = Aheap (\<pi> \<bullet> \<Gamma>)"
  unfolding Aheap_def
  apply perm_simp
  apply (subst Abs_cfun_eqvt)
  apply simp
  apply rule
  done

interpretation CorrectArityAnalysisLet Aexp Aheap
proof default
  fix \<pi> show "\<pi> \<bullet> Aheap = Aheap" by perm_simp rule
next
  fix x y :: var and \<Gamma> :: heap
  assume assms: "x \<notin> domA \<Gamma>"  "y \<notin> domA \<Gamma>"
  show "Aheap \<Gamma>[x::h=y] = Aheap \<Gamma>"
    apply (rule cfun_eqI)
    unfolding Aheap_def
    apply simp
    apply (subst Afix_restr_subst[OF assms subset_refl])
    apply (subst Afix_restr[OF  subset_refl]) back
    apply simp
    done
next
  fix \<Gamma> ae
  show "edom (Aheap \<Gamma>\<cdot>ae) \<subseteq> domA \<Gamma>"  unfolding Aheap_def by simp

  fix x e
  assume "map_of \<Gamma> x = Some e"
  hence [simp]: "x \<in> domA \<Gamma>" by (metis domI dom_map_of_conv_domA)

  show "ArityAnalysis.Aexp' Aexp e\<cdot>((Aheap \<Gamma>\<cdot>ae) x) f|` domA \<Gamma> \<sqsubseteq> Aheap \<Gamma>\<cdot>ae"
    using `map_of \<Gamma> x = Some e`
    unfolding Aheap_def
    apply simp
    apply (rule env_restr_mono)
    apply (metis (erased, hide_lams) "HOLCF-Join-Classes.join_above2" ABind_eq ArityAnalysis.Abinds_Afix ArityAnalysis.Abinds_reorder1 join_comm monofun_cfun_fun)
    done
  
  fix a e'
  show "ArityAnalysis.Aexp' Aexp e\<cdot>((Aheap \<Gamma>\<cdot>(Aexp e'\<cdot>a)) x) f|` (- domA \<Gamma>) \<sqsubseteq> Aexp (Terms.Let \<Gamma> e')\<cdot>a"
    using `map_of \<Gamma> x = Some e`
    unfolding Aheap_def
    apply simp
    apply (rule env_restr_mono)
    apply (metis (erased, hide_lams) "HOLCF-Join-Classes.join_above2" ABind_eq ArityAnalysis.Abinds_Afix ArityAnalysis.Abinds_reorder1 join_comm monofun_cfun_fun)
    done

   assume "\<not> isLam e"
   with `map_of \<Gamma> x = Some e` have "thunks \<Gamma> x = up\<cdot>0" by (induction \<Gamma> rule: thunks.induct) (auto split: if_splits)
   hence "(ae \<squnion> thunks \<Gamma>) x = up \<cdot> 0" by simp
   moreover have "(ae \<squnion> thunks \<Gamma>) \<sqsubseteq> Afix \<Gamma>\<cdot>(ae \<squnion> thunks \<Gamma>)" by (rule Afix_above_arg)
   ultimately have "(Afix \<Gamma>\<cdot>(ae \<squnion> thunks \<Gamma>)) x = up\<cdot>0" by (metis Arity_above_up_top  fun_belowD) 
   thus "(Aheap \<Gamma>\<cdot>ae) x = up\<cdot>0" unfolding Aheap_def by simp
next
  fix \<Gamma> ae
  have "ae \<sqsubseteq> ArityAnalysis.Afix Aexp \<Gamma>\<cdot>(ae \<squnion> thunks \<Gamma>)" by (rule  below_trans[OF join_above1 Afix_above_arg])
  thus "ae f|` domA \<Gamma> \<sqsubseteq> Aheap \<Gamma>\<cdot>ae"
    unfolding Aheap_def by (simp add: env_restr_mono)
next
  fix \<Gamma> e a
  show "Aexp e\<cdot>a f|` (- domA \<Gamma>) \<sqsubseteq> Aexp (Terms.Let \<Gamma> e)\<cdot>a"
    apply simp
    apply (rule env_restr_mono)
    apply (rule below_trans[OF join_above1 Afix_above_arg])
    done
next
  fix \<Gamma> :: heap and ae ae' :: AEnv
  assume [simp]: "ae f|` domA \<Gamma> = ae' f|` domA \<Gamma>"
  show "Aheap \<Gamma>\<cdot>ae = Aheap \<Gamma>\<cdot>ae'"
    unfolding Aheap_def
    apply simp
    apply (subst Afix_restr[OF subset_refl])
    apply (subst Afix_restr[OF subset_refl]) back
    apply (simp add: env_restr_join)
    done
qed

end
