theory ArityAnalysisImpl
imports ArityAnalysisFix ArityAnalysisPreImpl "Arity-Nominal" "Nominal-HOLCF" "Env-HOLCF"
begin

definition Real_Aexp where "Real_Aexp = ArityAnalysisPreImpl.Aexp ArityAnalysis.Afix"

lemma heap_exp_are_smaller:  "e \<in> snd ` set \<Gamma> \<Longrightarrow> size e \<le> size_list (\<lambda>p. size (snd p)) \<Gamma>"
  by (metis (mono_tags) imageE order_refl size_list_estimation')

interpretation ArityAnalysisPreImpl ArityAnalysis.Afix where "Aexp = ArityAnalysisImpl.Real_Aexp"
  unfolding Real_Aexp_def atomize_conj
  apply (rule conjI[OF _ refl])
  apply default
  apply (perm_simp, rule)
  apply (rule ArityAnalysisFix.Afix_cong)
  apply (metis heap_exp_are_smaller)
  apply assumption
  done

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

lemma Aexp_let_simp[simp]: "Aexp (Terms.Let \<Gamma> e) \<cdot> n = Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks_AE \<Gamma>) f|` (- domA \<Gamma>)"
proof-
  have "Aexp (Terms.Let \<Gamma> e) \<cdot> n  = Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks_AE \<Gamma>) f|` fv (Terms.Let \<Gamma> e)" by simp
  also have "\<dots> = Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks_AE \<Gamma>) f|` (- domA \<Gamma>) f|` fv (Terms.Let \<Gamma> e)" by auto (metis Diff_eq Diff_idemp)
  also have "\<dots> = Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks_AE \<Gamma>) f|` (- domA \<Gamma>)"
     by (rule env_restr_useless)
        (auto dest!: set_mp[OF Aexp_edom] set_mp[OF Afix_edom] set_mp[OF edom_thunks_AE])
  finally show ?thesis.
qed
declare Aexp.simps(4)[simp del]

lemma Aexp_subst_upd: "(Aexp e[y::=x]\<cdot>n) \<sqsubseteq> (Aexp e\<cdot>n)(y := \<bottom>, x := up\<cdot>0)"
proof (nominal_induct e avoiding: x y  arbitrary: n rule: exp_strong_induct)
  case (Var v) 
  thus ?case by auto
next
  case (App e v x y n)
  have "Aexp (App e v)[y::=x]\<cdot>n \<sqsubseteq> (Aexp e[y::=x]\<cdot>(inc\<cdot>n)) \<squnion> (esing (v[y::v=x])\<cdot>(up\<cdot>0))" by simp
  also have "Aexp e[y::=x]\<cdot>(inc\<cdot>n) \<sqsubseteq> (Aexp e\<cdot>(inc\<cdot>n))(y := \<bottom>, x := up\<cdot>0)" by (rule App.hyps)
  also have "(esing (v[y::v=x])\<cdot>(up\<cdot>0)) \<sqsubseteq> (esing v\<cdot>(up\<cdot>0))(y := \<bottom>, x := up\<cdot>0)" by simp
  also have "(Aexp e\<cdot>(inc\<cdot>n))(y := \<bottom>, x := up\<cdot>0) \<squnion> (esing v\<cdot>(up\<cdot>0))(y := \<bottom>, x := up\<cdot>0) 
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

  have "Aexp (Let \<Gamma> e)[y::=x]\<cdot>n \<sqsubseteq> Afix \<Gamma>[y::h=x]\<cdot>(Aexp e[y::=x]\<cdot>n \<squnion> thunks_AE \<Gamma>[y::h=x]) f|` ( - domA \<Gamma>)" by (simp add: fresh_star_Pair)
  also have "(Aexp e[y::=x]\<cdot>n) \<sqsubseteq> (Aexp e\<cdot>n)(y := \<bottom>, x := up\<cdot>0)" by fact
  also have "thunks_AE \<Gamma>[y::h=x] \<sqsubseteq> (thunks_AE \<Gamma>)(y := \<bottom>, x := up\<cdot>0)" by (rule thunks_AE_subst_approx[OF `y \<notin> domA \<Gamma>`])
  also have "(Aexp e\<cdot>n)(y := \<bottom>, x := up\<cdot>0) \<squnion> (thunks_AE \<Gamma>)(y := \<bottom>, x := up\<cdot>0) = (Aexp e\<cdot>n \<squnion> thunks_AE \<Gamma>)(y := \<bottom>, x := up\<cdot>0)" by simp
  also have "Afix \<Gamma>[y::h=x]\<cdot>((Aexp e\<cdot>n \<squnion> thunks_AE \<Gamma>)(y := \<bottom>, x := up\<cdot>0)) \<sqsubseteq> (Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks_AE \<Gamma>))(y := \<bottom>, x := up\<cdot>0)"
    by (rule Afix_subst_approx[OF Let(3) `x \<notin> domA \<Gamma>` `y \<notin> domA \<Gamma>`])
  also have "(Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks_AE \<Gamma>))(y := \<bottom>, x := up\<cdot>0) f|` (- domA \<Gamma>) = (Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks_AE \<Gamma>) f|` (- domA \<Gamma>)) (y := \<bottom>, x := up\<cdot>0)" by auto
  also have "(Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> thunks_AE \<Gamma>) f|` (- domA \<Gamma>)) = Aexp (Terms.Let \<Gamma> e)\<cdot>n" by simp
  finally show ?case by this simp_all
qed

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
  have "Afix \<Gamma>[x::h=y]\<cdot>(Aexp e[x::=y]\<cdot>a \<squnion> thunks_AE \<Gamma>) f|` (S \<union> domA \<Gamma>) = Afix \<Gamma>\<cdot>(Aexp e\<cdot>a \<squnion> thunks_AE \<Gamma>) f|` (S \<union> domA \<Gamma>)"
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

interpretation CorrectArityAnalysis' Aexp
proof default
(*
  fix \<pi>
  show "\<pi> \<bullet> Aexp = Aexp"
    by (rule fun_eqvtI[OF Aexp.eqvt])
next
*)
  fix x y :: var and e :: exp  and a 
  show "Aexp e[y::=x]\<cdot>a \<sqsubseteq> env_delete y (Aexp e\<cdot>a) \<squnion> esing x\<cdot>(up\<cdot>0)"
    apply (rule below_trans[OF Aexp_subst_upd])
    apply (rule fun_belowI)
    apply auto
    done
qed (simp_all add:Aexp_restr_subst)

definition Aheap where
  "Aheap \<Gamma> e = (\<Lambda> a. (Afix \<Gamma> \<cdot> (Aexp e\<cdot>a \<squnion> thunks_AE \<Gamma>) f|` domA \<Gamma>))"

lemma Aheap_eqvt'[eqvt]:
  "\<pi> \<bullet> (Aheap \<Gamma> e) = Aheap (\<pi> \<bullet> \<Gamma>) (\<pi> \<bullet> e)"
  unfolding Aheap_def
  apply perm_simp
  apply (subst Abs_cfun_eqvt)
  apply simp
  apply rule
  done

interpretation CorrectArityAnalysisLet' Aexp Aheap
proof default
  fix \<pi> show "\<pi> \<bullet> Aheap = Aheap"
    by perm_simp rule
next
  fix \<Gamma> e a
  show "edom (Aheap \<Gamma> e\<cdot>a) \<subseteq> domA \<Gamma>"
   unfolding Aheap_def by simp
next
  fix x y :: var and \<Gamma> :: heap and e :: exp
  assume assms: "x \<notin> domA \<Gamma>"  "y \<notin> domA \<Gamma>"
  show "Aheap \<Gamma>[x::h=y] e[x::=y] = Aheap \<Gamma> e"
    apply (rule cfun_eqI)
    unfolding Aheap_def
    apply simp
    apply (subst Afix_restr_subst[OF assms subset_refl])
    apply (subst Afix_restr[OF  subset_refl]) back
    apply (simp add: env_restr_join)
    apply (subst Aexp_restr_subst[OF assms])
    apply rule
    done
next
  fix \<Gamma> e a
  show "ABinds \<Gamma>\<cdot>(Aheap \<Gamma> e\<cdot>a) \<squnion> Aexp e\<cdot>a \<sqsubseteq> Aheap \<Gamma> e\<cdot>a \<squnion> Aexp (Let \<Gamma> e)\<cdot>a"
    by (auto simp add: Aheap_def join_below_iff env_restr_join2 Compl_partition intro:  below_trans[OF _ Afix_above_arg])
qed


interpretation CorrectArityAnalysisLetNoCard Aexp Aheap
proof default
  fix x \<Gamma> e a
  assume "x \<in> thunks \<Gamma>"
  hence "up\<cdot>0 \<sqsubseteq> thunks_AE \<Gamma> x" by (metis  thunks_AE_def up_zero_top)
  also have "thunks_AE \<Gamma> \<sqsubseteq> Real_Aexp e\<cdot>a \<squnion> thunks_AE \<Gamma>"
    by simp
  also have "\<dots> \<sqsubseteq> Afix \<Gamma>\<cdot>(Real_Aexp e\<cdot>a \<squnion> thunks_AE \<Gamma>)"
    by (rule Afix_above_arg)
  also have "(Afix \<Gamma>\<cdot>(Real_Aexp e\<cdot>a \<squnion> thunks_AE \<Gamma>)) x = (Aheap \<Gamma> e\<cdot>a) x"
    using set_mp[OF thunks_domA `x \<in> thunks \<Gamma>`] by (simp add: Aheap_def)
  finally
  have "up\<cdot>0 \<sqsubseteq> (Aheap \<Gamma> e\<cdot>a) x" by this simp_all
  thus "(Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0" by (metis Arity_above_up_top)
qed

end
