theory ArityAnalysisFix
imports ArityAnalysis ArityCorrect
begin

context ArityAnalysis
begin

subsection {* Lifting arity analysis to recursive groups *}

definition ABind :: "var \<Rightarrow> exp \<Rightarrow> (AEnv \<rightarrow> AEnv)"
  where "ABind v e = (\<Lambda> ae. Aexp' e \<cdot> (ae v))"

lemma ABind_eq[simp]: "ABind v e \<cdot> ae = Aexp' e \<cdot> (ae v)"
  unfolding ABind_def by (simp add: cont_fun)

fun ABinds :: "heap \<Rightarrow> (AEnv \<rightarrow> AEnv)"
  where "ABinds [] = ID"
     |  "ABinds ((v,e)#binds) = ABind v e \<squnion> ABinds (delete v binds)"

lemma ABinds_strict[simp]: "ABinds \<Gamma>\<cdot>\<bottom>=\<bottom>"
  by (induct \<Gamma> rule: ABinds.induct) auto

lemma Abinds_reorder1: "map_of \<Gamma> v = Some e \<Longrightarrow> ABinds \<Gamma> = ABind v e \<squnion> ABinds (delete v \<Gamma>)"
proof (induction \<Gamma> rule: ABinds.induct)
  case 1 thus ?case by simp
next
  case (2 v' e' \<Gamma>)
  thus ?case
  apply (cases "v' = v")
  apply auto
  apply (metis (hide_lams, no_types) join_assoc delete_twist join_comm)
  done
qed

lemma Abinds_reorder: "map_of \<Gamma> = map_of \<Delta> \<Longrightarrow> ABinds \<Gamma> = ABinds \<Delta>"
proof (induction  \<Gamma> arbitrary: \<Delta> rule: ABinds.induct)
  case 1 thus ?case by simp
next
  case (2 v e \<Gamma> \<Delta>)
  from `map_of ((v, e) # \<Gamma>) = map_of \<Delta>`
  have "(map_of ((v, e) # \<Gamma>))(v := None) = (map_of \<Delta>)(v := None)" by simp
  hence "map_of (delete v \<Gamma>) = map_of (delete v \<Delta>)" unfolding delete_set_none by simp
  hence "ABinds (delete v \<Gamma>) = ABinds (delete v \<Delta>)" by (rule 2)
  moreover
  from `map_of ((v, e) # \<Gamma>) = map_of \<Delta>`
  have "map_of \<Delta> v = Some e" by (metis map_of_Cons_code(2))
  hence "ABinds \<Delta> = ABind v e \<squnion> ABinds (delete v \<Delta>)" by (rule Abinds_reorder1)
  ultimately
  show ?case by auto
qed

lemma ABinds_above_arg: "ae \<sqsubseteq> ABinds \<Gamma> \<cdot> ae"
proof (induction rule:ABinds.induct)
  show "ae \<sqsubseteq> ABinds []\<cdot>ae" by auto
next
  fix v e \<Gamma>
  assume assm: "ae \<sqsubseteq> ABinds (delete v \<Gamma>)\<cdot>ae"
  also have "\<dots> \<sqsubseteq> ABinds ((v, e) # \<Gamma>)\<cdot>ae"  by auto
  finally show "ae \<sqsubseteq> ABinds ((v, e) # \<Gamma>)\<cdot>ae" by this simp
qed

lemma Abinds_join_fresh: "ae' ` (domA \<Delta>) \<subseteq> {\<bottom>} \<Longrightarrow>  ABinds \<Delta>\<cdot>(ae \<squnion> ae') = (ABinds \<Delta>\<cdot>ae) \<squnion> ae'"
proof (induct \<Delta> rule: ABinds.induct)
  case 1 thus ?case by simp
next
  case (2 v e \<Delta>)
  from 2(2)
  have "ae' v = \<bottom>" by auto
  moreover
  from 2(2) have  "ae' ` domA (delete v \<Delta>) \<subseteq> {\<bottom>}" by auto
  hence "ABinds (delete v \<Delta>)\<cdot>(ae \<squnion> ae') = ABinds (delete v \<Delta>)\<cdot>ae \<squnion> ae'" by (rule 2)
  ultimately
  show "ABinds ((v, e) # \<Delta>)\<cdot>(ae \<squnion> ae') = ABinds ((v, e) # \<Delta>)\<cdot>ae \<squnion> ae'"
    by simp
qed

lemma ABinds_restr_fresh:
  assumes "atom ` S \<sharp>* \<Gamma>"
  shows "ABinds \<Gamma>\<cdot>ae f|` (- S) = ABinds \<Gamma>\<cdot>(ae  f|` (- S)) f|` (- S)"
  using assms
  apply (induction \<Gamma> rule:ABinds.induct)
  apply simp
  apply (auto simp del: fun_meet_simp simp add: env_restr_join fresh_star_Pair fresh_star_Cons fresh_star_delete)
  apply (subst lookup_env_restr)
  apply (metis (no_types, hide_lams) ComplI fresh_at_base(2) fresh_star_def imageI)
  apply rule
  done

lemma ABinds_restr:
  assumes "domA \<Gamma> \<subseteq> S"
  shows "ABinds \<Gamma>\<cdot>ae f|` S = ABinds \<Gamma>\<cdot>(ae  f|` S) f|` S"
  using assms
  by (induction \<Gamma> rule:ABinds.induct) (fastforce simp del: fun_meet_simp simp add: env_restr_join)+

lemma ABinds_restr_subst:
  assumes "\<And> x' e a. (x',e) \<in> set \<Gamma> \<Longrightarrow> Aexp e[x::=y]\<cdot>a f|` S = Aexp e\<cdot>a f|` S"
  assumes "x \<notin> S"
  assumes "y \<notin> S"
  assumes "domA \<Gamma> \<subseteq> S"
  shows "ABinds \<Gamma>[x::h=y]\<cdot>ae f|` S = ABinds \<Gamma>\<cdot>(ae  f|` S) f|` S"
  using assms
  apply (induction \<Gamma> rule:ABinds.induct)
  apply (auto simp del: fun_meet_simp simp add: env_restr_join)
  apply (rule arg_cong2[where f = join])
  apply (case_tac "ae v")
  apply (auto dest:  set_mp[OF set_delete_subset])
  done

end


lemma ABind_eqvt[eqvt]: "\<pi> \<bullet> (ArityAnalysis.ABind Aexp v e) = ArityAnalysis.ABind (\<pi> \<bullet> Aexp) (\<pi> \<bullet> v) (\<pi> \<bullet> e)"
  unfolding ArityAnalysis.ABind_def
  by perm_simp (simp add: Abs_cfun_eqvt)

lemma ABinds_eqvt[eqvt]: "\<pi> \<bullet> (ArityAnalysis.ABinds Aexp \<Gamma>) = ArityAnalysis.ABinds (\<pi> \<bullet> Aexp) (\<pi> \<bullet> \<Gamma>)"
  apply (induction \<Gamma> rule: ArityAnalysis.ABinds.induct)
  apply (simp add: ArityAnalysis.ABinds.simps)
  apply (simp add: ArityAnalysis.ABinds.simps)
  apply perm_simp
  apply simp
  done

lemma Abinds_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> aexp1 e = aexp2 e) ; heap1 = heap2 \<rbrakk>
      \<Longrightarrow> ArityAnalysis.ABinds aexp1 heap1 = ArityAnalysis.ABinds aexp2 heap2"    
proof (induction heap1 arbitrary:heap2 rule:ArityAnalysis.ABinds.induct)
case goal1 thus ?case by (auto simp add: ArityAnalysis.ABinds.simps)
next
case (goal2  v e as heap2)
  have "snd ` set (delete v as) \<subseteq> snd ` set as" by (rule dom_delete_subset)
  also have "\<dots> \<subseteq> snd `set ((v, e) # as)" by auto
  also note goal2(3)
  finally
  have "(\<And>e. e \<in> snd ` set (delete v as) \<Longrightarrow> aexp1 e = aexp2 e)" by -(rule goal2, auto)
  note goal2(1)[OF this refl] with goal2
  show ?case by (auto simp add: ArityAnalysis.ABinds.simps ArityAnalysis.ABind_def ArityAnalysis.Aexp'_def)
qed

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
  apply (rule below_trans[OF _ join_above1])
  apply (rule monofun_cfun_arg)
  apply (subst fix_eq, simp)
  done

lemma Afix_above_arg: "ae \<sqsubseteq> Afix \<Gamma> \<cdot> ae"
  by (metis (hide_lams, no_types) Abinds_below_Afix ArityAnalysis.ABinds_above_arg below_refl box_below monofun_cfun_fun)


lemma Abinds_Afix[simp]: "ABinds \<Gamma>\<cdot>(Afix \<Gamma>\<cdot>ae) = Afix \<Gamma>\<cdot>ae"
  unfolding Afix_eq
  apply (subst fix_eq) back apply simp
  apply (rule below_trans[OF ABinds_above_arg monofun_cfun_arg])
  apply (subst fix_eq) apply simp
  done

lemma Afix_reorder: "map_of \<Gamma> = map_of \<Delta> \<Longrightarrow> Afix \<Gamma> = Afix \<Delta>"
  by (intro cfun_eqI)(simp add: Afix_eq cong: Abinds_reorder)

lemma Afix_repeat_singleton: "(\<mu> xa. Afix \<Gamma>\<cdot>(AE_singleton x\<cdot>(n \<squnion> xa x) \<squnion> ae)) = Afix \<Gamma>\<cdot>(AE_singleton x\<cdot>n \<squnion> ae)"
  apply (rule below_antisym)
  defer
  apply (subst fix_eq, simp)
  apply (intro monofun_cfun_arg join_mono below_refl join_above1)

  apply (rule fix_least_below, simp)
  apply (rule Afix_least_below, simp)
  apply (intro join_below below_refl iffD2[OF AE_singleton_below_iff] below_trans[OF _ fun_belowD[OF Afix_above_arg]]  below_trans[OF _ Afix_above_arg] join_above2)
  apply simp
  done

lemma Afix_join_fresh: "ae' ` (domA \<Delta>) \<subseteq> {\<bottom>}  \<Longrightarrow>  Afix \<Delta>\<cdot>(ae \<squnion> ae') = (Afix \<Delta>\<cdot>ae) \<squnion> ae'"
  apply (rule below_antisym)
  apply (rule Afix_least_below)
  apply (simp add: Abinds_join_fresh)
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
    hence IH1: "\<And> n. Aexp' e[y::=x]\<cdot>n \<sqsubseteq> (Aexp' e\<cdot>n)(y := \<bottom>, x := up\<cdot>0)" unfolding Aexp'_def by (case_tac n) auto

    have "ABinds (delete v \<Gamma>)[y::h=x]\<cdot>(aeR(y := \<bottom>, x := up\<cdot>0)) \<sqsubseteq> (ABinds (delete v \<Gamma>)\<cdot>aeR)(y := \<bottom>, x := up\<cdot>0)"
      apply (rule goal2) using goal2(2,3,4) by fastforce+
    hence IH2: "ABinds (delete v \<Gamma>[y::h=x])\<cdot>(aeR(y := \<bottom>, x := up\<cdot>0)) \<sqsubseteq> (ABinds (delete v \<Gamma>)\<cdot>aeR)(y := \<bottom>, x := up\<cdot>0)"
       unfolding subst_heap_delete.
    
    have [simp]: "(aeR(y := \<bottom>, x := up\<cdot>0)) v = aeR v" using goal2(3,4) by auto
   
    show ?case by (simp del: fun_upd_apply) (rule join_mono[OF IH1 IH2])
  qed
  finally
  have "ABinds \<Gamma>[y::h=x]\<cdot>aeL \<sqsubseteq> (ABinds \<Gamma>\<cdot>aeR)(y := \<bottom>, x := up\<cdot>0)" by this simp
  thus ?case by (simp add: join_mono)
qed

end

lemma Afix_eqvt[eqvt]: "\<pi> \<bullet> (ArityAnalysis.Afix Aexp \<Gamma>) = ArityAnalysis.Afix  (\<pi> \<bullet> Aexp) (\<pi> \<bullet> \<Gamma>)"
  unfolding ArityAnalysis.Afix_def
  by perm_simp (simp add: Abs_cfun_eqvt)


lemma Afix_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> aexp1 e = aexp2 e); heap1 = heap2 \<rbrakk>
      \<Longrightarrow> ArityAnalysis.Afix aexp1 heap1 = ArityAnalysis.Afix aexp2 heap2"
   unfolding ArityAnalysis.Afix_def by (metis Abinds_cong)

context EdomArityAnalysis
begin

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
end

context CorrectArityAnalysis
begin

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

lemma Afix_lookup_fresh:
  assumes "atom v \<sharp> \<Gamma>"
  shows "(Afix \<Gamma>\<cdot>ae) v = ae v"
  apply (rule below_antisym)
  apply (subst Afix_eq)
  apply (rule fix_ind[where  P = "\<lambda> ae'. ae' v \<sqsubseteq> ae v"])
  apply (auto simp add: ABinds_lookup_fresh[OF assms] fun_belowD[OF Afix_above_arg])
  done

lemma Afix_restr_subst:
  assumes "x \<notin> S"
  assumes "y \<notin> S"
  assumes "domA \<Gamma> \<subseteq> S"
  shows "Afix \<Gamma>[x::h=y]\<cdot>ae f|` S = Afix \<Gamma>\<cdot>(ae f|` S) f|` S"
  by (rule Afix_restr_subst'[OF Aexp_subst_restr[OF assms(1,2)] assms])

lemma Afix_comp2join_fresh:
  "atom ` (domA \<Delta>) \<sharp>* \<Gamma> \<Longrightarrow> ABinds \<Delta>\<cdot>(Afix \<Gamma>\<cdot>ae) = Afix \<Gamma> \<cdot> ae \<squnion> ABinds \<Delta>\<cdot>ae"
proof (induct \<Delta> rule: ABinds.induct)
  case 1 show ?case by (simp add: Afix_above_arg del: fun_meet_simp)
next
  case (2 v e \<Delta>)
  from 2(2)
  have "atom v \<sharp> \<Gamma>" and  "atom ` domA (delete v \<Delta>) \<sharp>* \<Gamma>"
    by (auto simp add: fresh_star_def)
  from 2(1)[OF this(2)]
  show ?case
    by (simp del: fun_meet_simp add: Afix_lookup_fresh[OF `atom v \<sharp> \<Gamma>`])
       (metis (hide_lams, no_types) join_assoc join_comm)
qed

lemma Afix_append_fresh:
  assumes "atom ` domA \<Delta> \<sharp>* \<Gamma>"
  shows "Afix (\<Delta> @ \<Gamma>)\<cdot>ae = Afix \<Gamma>\<cdot>(Afix \<Delta>\<cdot>ae)"
proof (rule below_antisym)
  show *: "Afix (\<Delta> @ \<Gamma>)\<cdot>ae \<sqsubseteq> Afix \<Gamma>\<cdot>(Afix \<Delta>\<cdot>ae)"
  by (rule Afix_least_below)
     (simp_all add:  Abinds_append_fresh[OF assms] Afix_comp2join_fresh[OF assms] Afix_above_arg below_trans[OF Afix_above_arg Afix_above_arg])
next
  show "Afix \<Gamma>\<cdot>(Afix \<Delta>\<cdot>ae) \<sqsubseteq> Afix (\<Delta> @ \<Gamma>)\<cdot>ae"
  proof (rule Afix_least_below)
    show "ABinds \<Gamma>\<cdot>(Afix (\<Delta> @ \<Gamma>)\<cdot>ae) \<sqsubseteq> Afix (\<Delta> @ \<Gamma>)\<cdot>ae"
      apply (subst Abinds_Afix[symmetric]) back
      apply (subst Abinds_append_fresh[OF assms])
      apply (rule ABinds_above_arg)
      done
    show "Afix \<Delta>\<cdot>ae \<sqsubseteq> Afix (\<Delta> @ \<Gamma>)\<cdot>ae"
      apply (rule Afix_least_below)
      apply (subst Abinds_Afix[symmetric]) back
      apply (subst Abinds_append_fresh[OF assms])
      apply (rule monofun_cfun_arg[OF ABinds_above_arg])
      apply (rule Afix_above_arg)
      done
  qed
qed

lemma Afix_e_to_heap:
   "Afix (delete x \<Gamma>)\<cdot>(Aexp' e\<cdot>n \<squnion> ae) \<sqsubseteq> Afix ((x, e) # delete x \<Gamma>)\<cdot>(AE_singleton x\<cdot>n \<squnion> ae)"
    apply (simp add: Afix_eq)
    apply (rule fix_least_below, simp)
    apply (intro join_below)
    apply (subst fix_eq, simp) back apply (simp add: below_trans[OF _ join_above2])
    apply (subst fix_eq, simp)
    apply (rule below_trans[OF monofun_cfun_arg join_above1])
    apply (subst fix_eq, simp)
    apply (rule below_trans[OF _ join_above2])
    apply (rule below_trans[OF _ join_above2])
    apply simp
    apply (subst fix_eq, simp)
    apply (rule below_trans[OF _ join_above2])
    apply (rule below_trans[OF _ join_above2])
    apply (rule below_trans[OF _ join_above2])
    apply simp
    done

lemma Afix_e_to_heap':
   "Afix (delete x \<Gamma>)\<cdot>(Aexp e\<cdot>n) \<sqsubseteq> Afix ((x, e) # delete x \<Gamma>)\<cdot>(AE_singleton x\<cdot>(up\<cdot>n))"
using Afix_e_to_heap[where ae = \<bottom> and n = "up\<cdot>n"] by simp

end

locale CorrectArityAnalysisAfix = CorrectArityAnalysis + 
  assumes Aexp_Let: "Afix as\<cdot>(Aexp e\<cdot>n) f|` (- domA as) \<sqsubseteq> Aexp (Let as e)\<cdot>n"

end

