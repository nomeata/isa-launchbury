theory ArityAnalysis
imports Terms Heap  "Arity"
begin

type_synonym AEnv = "var \<Rightarrow> Arity\<^sub>\<bottom>"

locale ArityAnalysis =
  fixes Aexp :: "exp \<Rightarrow> Arity \<rightarrow> AEnv"
begin

definition Aexp' :: "exp \<Rightarrow> Arity\<^sub>\<bottom> \<rightarrow> AEnv"
  where "Aexp' e = fup \<cdot> (Aexp e)"

lemma Aexp'_simps[simp]:
  "Aexp' e \<cdot> \<bottom> = \<bottom>"
  "Aexp' e \<cdot> (up\<cdot>n) = Aexp e \<cdot> n"
  unfolding Aexp'_def by simp_all

definition AE_singleton :: "var \<Rightarrow> Arity\<^sub>\<bottom> \<rightarrow> AEnv"
  where "AE_singleton x = (\<Lambda> a. (\<lambda> y . (if x = y then a else \<bottom>)))"

lemma AE_singleton_bot[simp]: "AE_singleton x \<cdot> \<bottom> = \<bottom>"
  by (rule ext)(simp add: AE_singleton_def)

lemma AE_singleton_simps[simp]: "(AE_singleton x \<cdot> n) x = n"
  by (simp add: AE_singleton_def)

lemma up_zero_top[simp]: "x \<sqsubseteq> up\<cdot>(0::Arity)"
  by (cases x) auto

lemma AE_singleton_below_iff[simp]: "AE_singleton x \<cdot> a \<sqsubseteq> ae  \<longleftrightarrow> a \<sqsubseteq> ae x"
  by (auto simp add: fun_below_iff AE_singleton_def)

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
  finally show "ae \<sqsubseteq> ABinds ((v, e) # \<Gamma>)\<cdot>ae".
qed

definition Afix ::  "heap \<Rightarrow> (AEnv \<rightarrow> AEnv) \<rightarrow> (AEnv \<rightarrow> AEnv)"
  where "Afix \<Gamma> = (\<Lambda> F ae. (\<mu>  ae'. ae \<squnion> ((ABinds \<Gamma> \<cdot> ae') \<squnion> F \<cdot> ae')))"

lemma Afix_eq: "Afix \<Gamma> \<cdot> F \<cdot> ae = (\<mu>  ae'. ae \<squnion> ((ABinds \<Gamma> \<cdot> ae') \<squnion> F \<cdot> ae'))"
  unfolding Afix_def by simp

definition Afix2 ::  "heap \<Rightarrow> (AEnv \<rightarrow> AEnv)"
  where "Afix2 \<Gamma> = (\<Lambda> ae. (\<mu>  ae'. ABinds \<Gamma> \<cdot> ae' \<squnion> ae))"

lemma Afix2_eq: "Afix2 \<Gamma> \<cdot> ae = (\<mu>  ae'. (ABinds \<Gamma> \<cdot> ae') \<squnion> ae)"
  unfolding Afix2_def by simp

lemma Afix2_strict[simp]: "Afix2 \<Gamma> \<cdot> \<bottom> = \<bottom>"
  unfolding Afix2_eq
  by (rule fix_eqI) auto

lemma Afix2_least_below: "ABinds \<Gamma> \<cdot> ae' \<sqsubseteq> ae' \<Longrightarrow> ae \<sqsubseteq> ae' \<Longrightarrow> Afix2 \<Gamma> \<cdot> ae \<sqsubseteq> ae'"
  unfolding Afix2_eq
  by (auto intro: fix_least_below)

lemma Abinds_below_Afix2: "ABinds \<Delta> \<sqsubseteq> Afix2 \<Delta>"
  apply (rule cfun_belowI)
  apply (simp add: Afix2_eq)
  apply (subst fix_eq, simp)
  apply (rule below_trans[OF _ join_above1])
  apply (rule monofun_cfun_arg)
  apply (subst fix_eq, simp)
  done

lemma Afix2_above_arg: "ae \<sqsubseteq> Afix2 \<Gamma> \<cdot> ae"
  by (metis (hide_lams, no_types) Abinds_below_Afix2 ArityAnalysis.ABinds_above_arg below_refl box_below monofun_cfun_fun)

lemma join_self_below[iff]:
  "x = x \<squnion> y \<longleftrightarrow> y \<sqsubseteq> (x::'a::Finite_Join_cpo)"
  by (metis "HOLCF-Join-Classes.join_above2" larger_is_join1)

lemma Abinds_Afix[simp]: "ABinds \<Gamma>\<cdot>(Afix2 \<Gamma>\<cdot>ae) = Afix2 \<Gamma>\<cdot>ae"
  unfolding Afix2_eq
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


end