theory NoCardinalityAnalysis
imports CardinalityAnalysis
begin

locale NoCardinalityAnalysis = CorrectArityAnalysisLet' +
  assumes Aheap_thunk: "x \<in> thunks \<Gamma> \<Longrightarrow> (Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0"
begin

definition a2c :: "Arity\<^sub>\<bottom> \<rightarrow> two" where "a2c = (\<Lambda> a. if a \<sqsubseteq> \<bottom> then \<bottom> else many)"
lemma a2c_simp: "a2c\<cdot>a = (if a \<sqsubseteq> \<bottom> then \<bottom> else many)"
  unfolding a2c_def by (rule beta_cfun[OF cont_if_else_above]) auto


lemma a2c_eqvt[eqvt]: "\<pi> \<bullet> a2c = a2c"
  unfolding a2c_def
  apply perm_simp
  apply (rule Abs_cfun_eqvt)
  apply (rule cont_if_else_above)
  apply auto
  done

definition ae2ce :: "AEnv \<Rightarrow> (var \<Rightarrow> two)" where "ae2ce ae x = a2c\<cdot>(ae x)"

lemma ae2ce_cont: "cont ae2ce"
  by (auto simp add: ae2ce_def) 
lemmas cont_compose[OF ae2ce_cont, cont2cont, simp]

lemma ae2ce_eqvt[eqvt]: "\<pi> \<bullet> ae2ce ae x = ae2ce (\<pi> \<bullet> ae) (\<pi> \<bullet> x)"
  unfolding ae2ce_def by perm_simp rule

lemma ae2ce_to_env_restr: "ae2ce ae = (\<lambda>_ . many) f|` edom ae"
  by (auto simp add: ae2ce_def lookup_env_restr_eq edom_def a2c_simp)

lemma edom_ae2ce[simp]: "edom (ae2ce ae) = edom ae"
  unfolding edom_def
  by (auto simp add: ae2ce_def  a2c_simp)


definition cHeap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> (var \<Rightarrow> two)"
  where "cHeap \<Gamma> e = (\<Lambda> a. ae2ce (Aheap \<Gamma> e\<cdot>a))"
lemma cHeap_simp[simp]: "cHeap \<Gamma> e\<cdot>a = ae2ce (Aheap \<Gamma> e\<cdot>a)"
  unfolding cHeap_def by simp

lemma cHeap_eqvt[eqvt]: "\<pi> \<bullet> cHeap \<Gamma> e = cHeap (\<pi> \<bullet> \<Gamma>) (\<pi> \<bullet> e)"
  unfolding cHeap_def
  apply perm_simp
  apply (rule Abs_cfun_eqvt)
  apply simp
  done

sublocale CardinalityHeap Aexp Aheap cHeap
  apply default
  apply (perm_simp, rule)
  apply (erule Aheap_thunk)
  apply simp
  done
  
(*
fun prognosis where 
  "prognosis ae a (\<Gamma>, e, S) = ae2ce (ABinds \<Gamma>\<cdot>ae \<squnion> Aexp e\<cdot>a) \<squnion> ((\<lambda>_. many) f|` ap S)"
*)

fun prognosis where 
  "prognosis ae a (\<Gamma>, e, S) = ((\<lambda>_. many) f|` (edom (ABinds \<Gamma>\<cdot>ae) \<union> edom (Aexp e\<cdot>a) \<union> ap S))"

lemma record_all_noop[simp]:
  "record_call x\<cdot>((\<lambda>_. many) f|` S) = (\<lambda>_. many) f|` S"
  by (auto simp add: record_call_def lookup_env_restr_eq)

sublocale CardinalityPrognosis prognosis.

sublocale CardinalityPrognosisCorrect prognosis
proof
  case goal1 thus ?case by (simp cong: Abinds_env_restr_cong)
next
  case goal2 thus ?case by auto
next
  case goal3 thus ?case
    using edom_mono[OF Aexp_App] by (auto intro!: env_restr_mono2)
next
  case goal4
  have "edom (Aexp e[y::=x]\<cdot>(pred\<cdot>a)) \<subseteq> insert x (edom (env_delete y (Aexp e\<cdot>(pred\<cdot>a))))"
    by (auto dest: set_mp[OF edom_mono[OF Aexp_subst]] )
  also have "\<dots> \<subseteq> insert x (edom (Aexp (Lam [y]. e)\<cdot>a))"
    using edom_mono[OF Aexp_Lam] by auto
  finally show ?case by (auto intro!: env_restr_mono2)
next
  case goal5
  thus ?case by (auto intro!: env_restr_mono2 simp add: Abinds_reorder1[OF goal5(1)])
next
  case goal6
  from `ae x \<sqsubseteq> up\<cdot>a`
  have "Aexp' e\<cdot>(ae x) \<sqsubseteq> Aexp e\<cdot>a" by (cases "ae x") (auto intro: monofun_cfun_arg)
  from edom_mono[OF this]
  show ?case by (auto intro!: env_restr_mono2 dest: set_mp[OF edom_mono[OF ABinds_delete_below]])
qed
  
sublocale CardinalityPrognosisCorrectLet prognosis Aexp Aheap cHeap
proof
  case goal1
  note set_mp[OF edom_Aheap]
  have "ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a \<squnion> ae) = ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)" sorry
  moreover
  have "ABinds \<Gamma>\<cdot>(Aheap \<Delta> e\<cdot>a \<squnion> ae) = ABinds \<Gamma>\<cdot>ae" sorry
  ultimately
  have "edom (ABinds (\<Delta> @ \<Gamma>)\<cdot>(Aheap \<Delta> e\<cdot>a \<squnion> ae)) \<union> edom (Aexp e\<cdot>a)  = edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) \<union> edom (ABinds \<Gamma>\<cdot>ae) \<union>  edom (Aexp e\<cdot>a) "
    by (simp add: Abinds_append_disjoint[OF goal1(1)])
  also have "\<dots> = edom (ABinds \<Gamma>\<cdot>ae) \<union> edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a)"
    by force
  also have "\<dots> \<subseteq> edom (ABinds \<Gamma>\<cdot>ae) \<union> edom (Aheap \<Delta> e\<cdot>a \<squnion> Aexp (Let \<Delta> e)\<cdot>a)"
    using  edom_mono[OF Aexp_Let] by force
  also have "\<dots> = edom (Aheap \<Delta> e\<cdot>a) \<union> edom (ABinds \<Gamma>\<cdot>ae) \<union> edom (Aexp (Let \<Delta> e)\<cdot>a)"
    by auto
  finally
  have "edom (ABinds (\<Delta> @ \<Gamma>)\<cdot>(Aheap \<Delta> e\<cdot>a \<squnion> ae)) \<union> edom (Aexp e\<cdot>a) \<subseteq> edom (Aheap \<Delta> e\<cdot>a) \<union> edom (ABinds \<Gamma>\<cdot>ae) \<union> edom (Aexp (Terms.Let \<Delta> e)\<cdot>a)".
  hence "edom (ABinds (\<Delta> @ \<Gamma>)\<cdot>(Aheap \<Delta> e\<cdot>a \<squnion> ae)) \<union> edom (Aexp e\<cdot>a) \<union> ap S \<subseteq> edom (Aheap \<Delta> e\<cdot>a) \<union> edom (ABinds \<Gamma>\<cdot>ae) \<union> edom (Aexp (Terms.Let \<Delta> e)\<cdot>a) \<union> ap S" by auto
  thus ?case by (simp add: ae2ce_to_env_restr env_restr_join2 Un_assoc[symmetric] env_restr_mono2)
qed

sublocale CardinalityPrognosisEdom prognosis Aexp Aheap
  by default auto

end

end
