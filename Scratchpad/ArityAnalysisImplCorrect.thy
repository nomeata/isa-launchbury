theory ArityAnalysisImplSafe
imports ArityAnalysisFixProps ArityAnalysisImpl
begin

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
next
  case (IfThenElse \<Gamma> e)
  then show ?case by (auto simp add: env_restr_join simp del: fun_meet_simp)
qed auto

interpretation ArityAnalysisSafe Aexp
  by default (simp_all add:Aexp_restr_subst)
(*
  fix \<pi>
  show "\<pi> \<bullet> Aexp = Aexp"
    by (rule fun_eqvtI[OF Aexp.eqvt])
next
*)

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

interpretation ArityAnalysisLetSafe Aexp Aheap
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


interpretation ArityAnalysisLetSafeNoCard Aexp Aheap
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
