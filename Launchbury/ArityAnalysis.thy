theory ArityAnalysis
imports Terms AEnv "Arity-Nominal" "Nominal-HOLCF"  "Substitution"
begin

locale ArityAnalysis =
  fixes Aexp :: "exp \<Rightarrow> Arity \<rightarrow> AEnv"
begin

definition Aexp' :: "exp \<Rightarrow> Arity\<^sub>\<bottom> \<rightarrow> AEnv"
  where "Aexp' e = fup \<cdot> (Aexp e)"

lemma Aexp'_simps[simp]:
  "Aexp' e \<cdot> \<bottom> = \<bottom>"
  "Aexp' e \<cdot> (up\<cdot>n) = Aexp e \<cdot> n"
  unfolding Aexp'_def by simp_all

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

lemma env_restr_join:
  fixes m1 m2 :: "'a::type \<Rightarrow> 'b::{Finite_Join_cpo,pcpo}"
  shows "(m1 \<squnion> m2) f|` S = (m1 f|` S) \<squnion> (m2 f|` S )"
  by (auto simp add: env_restr_def)

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


definition Acomplete :: "heap \<Rightarrow> exp \<Rightarrow> (AEnv \<rightarrow> AEnv) \<Rightarrow> Arity \<rightarrow> AEnv"
  where "Acomplete \<Gamma> e F = (\<Lambda> a. (\<mu> ae. ABinds \<Gamma> \<squnion> F) \<cdot> (Aexp e \<cdot> a))"

definition inc_bot :: "Arity\<^sub>\<bottom> \<rightarrow> Arity\<^sub>\<bottom>" ("inc\<^sub>\<bottom>") where "inc_bot = fup\<cdot>(up oo inc)"

lemma inc_bot_simps[simp]:
  "inc\<^sub>\<bottom>\<cdot>\<bottom>=\<bottom>"
  "inc\<^sub>\<bottom>\<cdot>(up\<cdot>n)=up\<cdot>(inc\<cdot>n)"
  unfolding inc_bot_def by simp_all

end


lemma Aexp'_eqvt[eqvt]: "\<pi> \<bullet> (ArityAnalysis.Aexp' Aexp e) = ArityAnalysis.Aexp' (\<pi> \<bullet> Aexp) (\<pi> \<bullet> e)"
  unfolding ArityAnalysis.Aexp'_def
  by perm_simp rule

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

lemma Afix_eqvt[eqvt]: "\<pi> \<bullet> (ArityAnalysis.Afix Aexp \<Gamma>) = ArityAnalysis.Afix  (\<pi> \<bullet> Aexp) (\<pi> \<bullet> \<Gamma>)"
  unfolding ArityAnalysis.Afix_def
  by perm_simp (simp add: Abs_cfun_eqvt)

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

lemma Afix_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> aexp1 e = aexp2 e); heap1 = heap2 \<rbrakk>
      \<Longrightarrow> ArityAnalysis.Afix aexp1 heap1 = ArityAnalysis.Afix aexp2 heap2"
   unfolding ArityAnalysis.Afix_def by (metis Abinds_cong)

end
