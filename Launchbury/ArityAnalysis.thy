theory ArityAnalysis
imports Terms AEnv "Arity-Nominal" "Nominal-HOLCF" 
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
