theory ArityAnalysisFix
imports ArityAnalysisSig ArityAnalysisAbinds
begin

context ArityAnalysis
begin

definition Afix ::  "heap \<Rightarrow> (AEnv \<rightarrow> AEnv)"
  where "Afix \<Gamma> = (\<Lambda> ae. (\<mu>  ae'. ABinds \<Gamma> \<cdot> ae' \<squnion> ae))"

lemma Afix_eq: "Afix \<Gamma> \<cdot> ae = (\<mu>  ae'. (ABinds \<Gamma> \<cdot> ae') \<squnion> ae)"
  unfolding Afix_def by simp

lemma Afix_strict[simp]: "Afix \<Gamma> \<cdot> \<bottom> = \<bottom>"
  unfolding Afix_eq
  by (rule fix_eqI) auto

lemma Afix_least_below: "ABinds \<Gamma> \<cdot> ae' \<sqsubseteq> ae' \<Longrightarrow> ae \<sqsubseteq> ae' \<Longrightarrow> Afix \<Gamma> \<cdot> ae \<sqsubseteq> ae'"
  unfolding Afix_eq
  by (auto intro: fix_least_below)

lemma Afix_unroll: "Afix \<Gamma>\<cdot>ae = ABinds \<Gamma> \<cdot> (Afix \<Gamma>\<cdot>ae) \<squnion> ae"
  unfolding Afix_eq
  apply (subst fix_eq)
  by simp

lemma Abinds_below_Afix: "ABinds \<Delta> \<sqsubseteq> Afix \<Delta>"
  apply (rule cfun_belowI)
  apply (simp add: Afix_eq)
  apply (subst fix_eq, simp)
  apply (rule below_trans[OF _ join_above2])
  apply (rule monofun_cfun_arg)
  apply (subst fix_eq, simp)
  done

lemma Afix_above_arg: "ae \<sqsubseteq> Afix \<Gamma> \<cdot> ae"
  by (subst Afix_unroll) simp

lemma Abinds_Afix_below[simp]: "ABinds \<Gamma>\<cdot>(Afix \<Gamma>\<cdot>ae) \<sqsubseteq> Afix \<Gamma>\<cdot>ae"
  apply (subst Afix_unroll) back
  apply simp
  done


(*lemma Abinds_Afix[simp]: "ABinds \<Gamma>\<cdot>(Afix \<Gamma>\<cdot>ae) = Afix \<Gamma>\<cdot>ae"
  unfolding Afix_eq
  apply (subst fix_eq) back apply simp
  apply (rule below_trans[OF ABinds_above_arg monofun_cfun_arg])
  apply (subst fix_eq) apply simp
  done
*)

lemma Afix_reorder: "map_of \<Gamma> = map_of \<Delta> \<Longrightarrow> Afix \<Gamma> = Afix \<Delta>"
  by (intro cfun_eqI)(simp add: Afix_eq cong: Abinds_reorder)

lemma Afix_repeat_singleton: "(\<mu> xa. Afix \<Gamma>\<cdot>(esing x\<cdot>(n \<squnion> xa x) \<squnion> ae)) = Afix \<Gamma>\<cdot>(esing x\<cdot>n \<squnion> ae)"
  apply (rule below_antisym)
  defer
  apply (subst fix_eq, simp)
  apply (intro monofun_cfun_arg join_mono below_refl join_above1)

  apply (rule fix_least_below, simp)
  apply (rule Afix_least_below, simp)
  apply (intro join_below below_refl iffD2[OF esing_below_iff] below_trans[OF _ fun_belowD[OF Afix_above_arg]]  below_trans[OF _ Afix_above_arg] join_above1)
  apply simp
  done

lemma Afix_join_fresh: "ae' ` (domA \<Delta>) \<subseteq> {\<bottom>}  \<Longrightarrow>  Afix \<Delta>\<cdot>(ae \<squnion> ae') = (Afix \<Delta>\<cdot>ae) \<squnion> ae'"
  apply (rule below_antisym)
  apply (rule Afix_least_below)
  apply (subst Abinds_join_fresh, simp)
  apply (rule below_trans[OF Abinds_Afix_below join_above1])
  apply (rule join_below)
  apply (rule below_trans[OF Afix_above_arg join_above1])
  apply (rule join_above2)
  apply (rule join_below[OF monofun_cfun_arg [OF join_above1]])
  apply (rule below_trans[OF join_above2 Afix_above_arg])
  done


lemma Afix_restr_fresh:
  assumes "atom ` S \<sharp>* \<Gamma>"
  shows "Afix \<Gamma>\<cdot>ae f|` (- S) = Afix \<Gamma>\<cdot>(ae  f|` (- S)) f|` (- S)"
unfolding Afix_eq
proof (rule parallel_fix_ind[where P = "\<lambda> x y . x f|` (- S) = y  f|` (- S)"])
  case goal1 show ?case by simp
next
  case goal2 show ?case..
next
  case (goal3 aeL aeR)
  have "(ABinds \<Gamma>\<cdot>aeL \<squnion> ae) f|` (- S) = ABinds \<Gamma>\<cdot>aeL  f|` (- S) \<squnion> ae  f|` (- S)" by (simp add: env_restr_join)
  also have "\<dots> = ABinds \<Gamma>\<cdot>(aeL  f|` (- S)) f|` (- S) \<squnion> ae  f|` (- S)" by (rule arg_cong[OF ABinds_restr_fresh[OF assms]])
  also have "\<dots> = ABinds \<Gamma>\<cdot>(aeR  f|` (- S)) f|` (- S) \<squnion> ae  f|` (- S)" unfolding goal3..
  also have "\<dots> = ABinds \<Gamma>\<cdot>aeR f|` (- S) \<squnion> ae  f|` (- S)" by (rule arg_cong[OF ABinds_restr_fresh[OF assms, symmetric]])
  also have "\<dots> = (ABinds \<Gamma>\<cdot>aeR \<squnion> ae f|` (- S)) f|` (- S)" by (simp add: env_restr_join)
  finally show ?case by simp
qed

lemma Afix_restr:
  assumes "domA \<Gamma> \<subseteq> S"
  shows "Afix \<Gamma>\<cdot>ae f|` S = Afix \<Gamma>\<cdot>(ae  f|` S) f|` S"
  unfolding Afix_eq
  apply (rule parallel_fix_ind[where P = "\<lambda> x y . x f|`S = y  f|` S"])
  apply simp
  apply rule
  apply (auto   simp add: env_restr_join)
  apply (metis  ABinds_restr[OF assms, symmetric])
  done

lemma Afix_restr_subst':
  assumes "\<And> x' e a. (x',e) \<in> set \<Gamma> \<Longrightarrow> Aexp e[x::=y]\<cdot>a f|` S = Aexp e\<cdot>a f|` S"
  assumes "x \<notin> S"
  assumes "y \<notin> S"
  assumes "domA \<Gamma> \<subseteq> S"
  shows "Afix \<Gamma>[x::h=y]\<cdot>ae f|` S = Afix \<Gamma>\<cdot>(ae f|` S) f|` S"
  unfolding Afix_eq
  apply (rule parallel_fix_ind[where P = "\<lambda> x y . x f|`S = y  f|` S"])
  apply simp
  apply rule
  apply (auto   simp add: env_restr_join)
  apply (subst ABinds_restr_subst[OF assms]) apply assumption
  apply (subst ABinds_restr[OF assms(4)]) back
  apply simp
  done

 
lemma Afix_subst_approx:
  assumes "\<And> v n. v \<in> domA \<Gamma> \<Longrightarrow> Aexp (the (map_of \<Gamma> v))[y::=x]\<cdot>n \<sqsubseteq> (Aexp (the (map_of \<Gamma> v))\<cdot>n)(y := \<bottom>, x := up\<cdot>0)"
  assumes "x \<notin> domA \<Gamma>"
  assumes "y \<notin> domA \<Gamma>"
  shows "Afix \<Gamma>[y::h= x]\<cdot>(ae(y := \<bottom>, x := up\<cdot>0)) \<sqsubseteq> (Afix \<Gamma>\<cdot>ae)(y := \<bottom>, x := up\<cdot>0)"
unfolding Afix_eq
proof (rule parallel_fix_ind[where P = "\<lambda> aeL aeR . aeL \<sqsubseteq> aeR(y := \<bottom>, x := up\<cdot>0)"])
  case goal1 show ?case by simp
next
  case goal2 show ?case..
next
  case (goal3 aeL aeR)
  hence "ABinds \<Gamma>[y::h=x]\<cdot>aeL \<sqsubseteq> ABinds \<Gamma>[y::h=x]\<cdot>(aeR (y := \<bottom>, x := up\<cdot>0))" by (rule monofun_cfun_arg)
  also have "\<dots>  \<sqsubseteq> (ABinds \<Gamma>\<cdot>aeR)(y := \<bottom>, x := up\<cdot>0)"
  using assms
  proof(induction  rule: ABinds.induct)
  case goal1 thus ?case by simp
  next
  case (goal2 v e \<Gamma>)
    have "\<And> n. Aexp e[y::=x]\<cdot>n \<sqsubseteq> (Aexp e\<cdot>n)(y := \<bottom>, x := up\<cdot>0)" using goal2(2)[where v = v] by auto
    hence IH1: "\<And> n. fup\<cdot>(Aexp e[y::=x])\<cdot>n \<sqsubseteq> (fup\<cdot>(Aexp e)\<cdot>n)(y := \<bottom>, x := up\<cdot>0)"  by (case_tac n) auto

    have "ABinds (delete v \<Gamma>)[y::h=x]\<cdot>(aeR(y := \<bottom>, x := up\<cdot>0)) \<sqsubseteq> (ABinds (delete v \<Gamma>)\<cdot>aeR)(y := \<bottom>, x := up\<cdot>0)"
      apply (rule goal2) using goal2(2,3,4) by fastforce+
    hence IH2: "ABinds (delete v \<Gamma>[y::h=x])\<cdot>(aeR(y := \<bottom>, x := up\<cdot>0)) \<sqsubseteq> (ABinds (delete v \<Gamma>)\<cdot>aeR)(y := \<bottom>, x := up\<cdot>0)"
       unfolding subst_heap_delete.
    
    have [simp]: "(aeR(y := \<bottom>, x := up\<cdot>0)) v = aeR v" using goal2(3,4) by auto
   
    show ?case by (simp del: fun_upd_apply join_comm) (rule join_mono[OF IH1 IH2])
  qed
  finally
  have "ABinds \<Gamma>[y::h=x]\<cdot>aeL \<sqsubseteq> (ABinds \<Gamma>\<cdot>aeR)(y := \<bottom>, x := up\<cdot>0)" by this simp
  thus ?case
    by (auto simp add: join_below_iff elim: below_trans)
qed

end

lemma Afix_eqvt[eqvt]: "\<pi> \<bullet> (ArityAnalysis.Afix Aexp \<Gamma>) = ArityAnalysis.Afix  (\<pi> \<bullet> Aexp) (\<pi> \<bullet> \<Gamma>)"
  unfolding ArityAnalysis.Afix_def
  by perm_simp (simp add: Abs_cfun_eqvt)


lemma Afix_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> aexp1 e = aexp2 e); heap1 = heap2 \<rbrakk>
      \<Longrightarrow> ArityAnalysis.Afix aexp1 heap1 = ArityAnalysis.Afix aexp2 heap2"
   unfolding ArityAnalysis.Afix_def by (metis Abinds_cong)

end

