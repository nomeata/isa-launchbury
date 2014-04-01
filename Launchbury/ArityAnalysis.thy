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

definition AE_singleton :: "var \<Rightarrow> Arity\<^sub>\<bottom> \<Rightarrow> AEnv"
  where "AE_singleton x a y = (if x = y then a else \<bottom>)"

lemma AE_singleton_bot[simp]: "AE_singleton x \<bottom> = \<bottom>"
  by (rule ext)(simp add: AE_singleton_def)

lemma up_zero_top[simp]: "x \<sqsubseteq> up\<cdot>(0::Arity)"
  by (cases x) auto

lemma AE_singleton_below_iff[simp]: "AE_singleton x a \<sqsubseteq> ae  \<longleftrightarrow> a \<sqsubseteq> ae x"
  by (auto simp add: fun_below_iff AE_singleton_def)

definition ABind :: "var \<Rightarrow> exp \<Rightarrow> (AEnv \<rightarrow> AEnv)"
  where "ABind v e = (\<Lambda> ae. Aexp' e \<cdot> (ae v))"

fun ABinds :: "heap \<Rightarrow> (AEnv \<rightarrow> AEnv)"
  where "ABinds [] = ID"
     |  "ABinds ((v,e)#binds) = ABind v e \<squnion> ABinds (delete v binds)"

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

definition Acomplete :: "heap \<Rightarrow> exp \<Rightarrow> (AEnv \<rightarrow> AEnv) \<Rightarrow> Arity \<rightarrow> AEnv"
  where "Acomplete \<Gamma> e F = (\<Lambda> a. (\<mu> ae. ABinds \<Gamma> \<squnion> F) \<cdot> (Aexp e \<cdot> a))"

definition inc_bot :: "Arity\<^sub>\<bottom> \<rightarrow> Arity\<^sub>\<bottom>" ("inc\<^sub>\<bottom>") where "inc_bot = fup\<cdot>(up oo inc)"

lemma inc_bot_simps[simp]:
  "inc\<^sub>\<bottom>\<cdot>\<bottom>=\<bottom>"
  "inc\<^sub>\<bottom>\<cdot>(up\<cdot>n)=up\<cdot>(inc\<cdot>n)"
  unfolding inc_bot_def by simp_all


end


end
