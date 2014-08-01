theory ArityCorrectSestoft
imports ArityCorrect SestoftCorrect
begin

fun Astack :: "AEnv \<Rightarrow> stack \<Rightarrow> Arity"
  where "Astack ae [] = 0"
      | "Astack ae (Arg x # S) = inc\<cdot>(Astack ae S)"
      | "Astack ae (Upd x # S) = (case ae x of Iup a \<Rightarrow> a)"
      | "Astack ae (Dummy x # S) = 0"

lemma Astack_cong: "(\<And> x. x \<in> upds S \<Longrightarrow> ae x = ae' x) \<Longrightarrow>  Astack ae S = Astack ae' S"
  by (induction S  rule: Astack.induct) auto

lemma Astack_Upd_simps[simp]:
  "ae x = up\<cdot>u \<Longrightarrow> Astack ae (Upd x # S) = u"
  by (simp add: up_def cont_Iup)
declare Astack.simps(3)[simp del]


fun AEstack :: "AEnv \<Rightarrow> stack \<Rightarrow> AEnv"
  where "AEstack ae [] = \<bottom>"
      | "AEstack ae (Arg x # S) = AE_singleton x \<cdot> (up\<cdot>0) \<squnion> AEstack ae S"
      | "AEstack ae (Upd x # S) = AE_singleton x \<cdot> (up\<cdot>(Astack ae S)) \<squnion> AEstack ae S"
      | "AEstack ae (Dummy x # S) = AEstack ae S"

lemma AEstack_cong: "(\<And> x. x \<in> upds S \<Longrightarrow> ae x = ae' x) \<Longrightarrow> AEstack ae S = AEstack ae' S"
  by (induction S  rule: upds.induct) (auto cong: Astack_cong)

locale CorrectArityAnalysis2 = CorrectArityAnalysis + 
  fixes Aheap :: "heap \<Rightarrow> AEnv \<rightarrow> AEnv"
  assumes edom_Aheap: "edom (Aheap \<Gamma> \<cdot> ae) \<subseteq> domA \<Gamma>"
  assumes Aheap_heap: "map_of \<Gamma> x = Some e' \<Longrightarrow> Aexp' e'\<cdot>((Aheap \<Gamma>\<cdot>ae) x) f|` domA \<Gamma> \<sqsubseteq> Aheap \<Gamma>\<cdot>ae"
  assumes Aheap_heap2: "map_of \<Gamma> x = Some e' \<Longrightarrow> Aexp' e'\<cdot>((Aheap \<Gamma>\<cdot>(Aexp e\<cdot>a)) x) f|` (- domA \<Gamma>) \<sqsubseteq>  Aexp (Terms.Let \<Gamma> e)\<cdot>a"
  assumes Aheap_above_arg: "ae f|` domA \<Gamma> \<sqsubseteq> Aheap \<Gamma>\<cdot>ae"
  assumes Aexp_Let_above: "Aexp e\<cdot>a f|` (- domA \<Gamma>) \<sqsubseteq> Aexp (Terms.Let \<Gamma> e)\<cdot>a"
begin

inductive AE_consistent :: "AEnv \<Rightarrow> conf \<Rightarrow> bool" where
  AE_consistentI: 
  "edom ae \<subseteq> domA \<Gamma> \<union> upds S
  \<Longrightarrow> upds S \<subseteq> edom ae
  \<Longrightarrow> AEstack ae S \<sqsubseteq> ae 
  \<Longrightarrow> Aexp e \<cdot> (Astack ae S) \<sqsubseteq> ae
  \<Longrightarrow> (\<And> x e. map_of \<Gamma> x = Some e \<Longrightarrow> Aexp' e \<cdot> (ae x) \<sqsubseteq> ae)
  \<Longrightarrow> AE_consistent ae (\<Gamma>, e, S)"

inductive_cases AE_consistentE[elim]: "AE_consistent ae (\<Gamma>, e, S)"

lemma [simp]: "Aexp' e\<cdot>(Iup u) = Aexp e\<cdot>u"
proof-
  have "Iup u = up\<cdot>u" by (simp add: up_def cont_Iup )
  thus ?thesis by simp
qed

lemma map_of_deleteD: "map_of (delete x \<Gamma>) xa = Some e \<Longrightarrow> map_of \<Gamma> xa = Some e"
  by (metis delete_conv fun_upd_same map_of_delete option.distinct(1))

theorem
  assumes "(\<Gamma>, e, S) \<Rightarrow> (\<Delta>, v, S')"
  assumes "AE_consistent ae (\<Gamma>, e, S)"
(*   shows "AE_consistent ae (\<Delta>, v, S')" *)
  shows "\<exists> ae'. ae' f|` (-((domA \<Delta> \<union> upds S') - (domA \<Gamma> \<union> upds S))) = ae \<and> AE_consistent ae' (\<Delta>, v, S')"
using assms
proof(induction "(\<Gamma>, e, S)" "(\<Delta>, v, S')"  arbitrary: \<Gamma> e S \<Delta> v S' rule: step.inducts)
case (app\<^sub>1 \<Gamma> e x S)
  hence "AE_consistent ae (\<Gamma>, e, Arg x # S)"  by (fastforce elim!: AE_consistentE intro!: AE_consistentI simp add: Aexp_App join_below_iff)
  thus ?case by simp
next
case (app\<^sub>2 \<Gamma> y e x S)
  hence "AE_consistent ae (\<Gamma>, e[y::=x], S)" 
    by (auto elim!: AE_consistentE intro!: AE_consistentI  below_trans[OF monofun_cfun_fun[OF Aexp_subst_App_Lam]] simp add: Aexp_App join_below_iff)
  thus ?case by simp
next
case (var\<^sub>1 \<Gamma> x e S)
  from `map_of \<Gamma> x = Some e`
  have "x \<in> domA \<Gamma>" by (metis domI dom_map_of_conv_domA)
  hence *: "(domA (delete x \<Gamma>) \<union> upds (Upd x # S) - (domA \<Gamma> \<union> upds S)) = {}" using `x \<in> domA \<Gamma>` by auto
  
  from var\<^sub>1 have "Aexp (Var x)\<cdot>(Astack ae S) \<sqsubseteq> ae" by auto
  from below_trans[OF Aexp_Var fun_belowD[OF this] ]
  have "up\<cdot>(Astack ae S) \<sqsubseteq> ae x".
  then obtain u where "ae x = up\<cdot>u" and "Astack ae S \<sqsubseteq> u" by (cases "ae x") auto
  moreover
  hence "x \<in> edom ae" unfolding edom_def by auto
  ultimately
  have "AE_consistent ae (delete x \<Gamma>, e, Upd x # S)" using var\<^sub>1 by (fastforce intro!: AE_consistentI dest: map_of_deleteD simp add: join_below_iff)
  thus ?case unfolding * by simp
next
case (var\<^sub>2 x \<Gamma> e S)
  have "up\<cdot>(Astack ae S) \<sqsubseteq> ae x" using var\<^sub>2 by (auto simp add: join_below_iff)
  then obtain u where "ae x = up \<cdot> u" and "Astack ae S \<sqsubseteq> u" by (cases "ae x") auto

  from this(2)
  have "Aexp e\<cdot>(Astack ae S) \<sqsubseteq> Aexp e\<cdot>u" by (rule monofun_cfun_arg)
  also have "\<dots> \<sqsubseteq> ae" using `ae x = up \<cdot> u` var\<^sub>2 by auto
  finally have "Aexp e\<cdot>(Astack ae S) \<sqsubseteq> ae" by this simp
  hence "AE_consistent ae ((x, e) # \<Gamma>, e, S)" using var\<^sub>2 `ae x = up \<cdot> u`
    by (fastforce intro!: AE_consistentI  simp add: join_below_iff split:if_splits)+
  thus ?case by simp
next
case (let\<^sub>1 \<Delta> \<Gamma> S e)
  let ?ae = "Aheap \<Delta> \<cdot> (Aexp e\<cdot>(Astack ae S))"
  let ?new = "(domA (\<Delta> @ \<Gamma>) \<union> upds S - (domA \<Gamma> \<union> upds S))"
  have new: "?new = domA \<Delta>"
    using fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)]
    by (auto dest: set_mp[OF ups_fv_subset])

  have "domA \<Delta> \<inter> upds S = {}" using fresh_distinct_fv[OF let\<^sub>1(2)] by (auto dest: set_mp[OF ups_fv_subset])
  hence "\<And> x. x \<in> upds S \<Longrightarrow> x \<notin> edom (Aheap \<Delta>\<cdot>(Aexp e\<cdot>(Astack ae S)))"
    using edom_Aheap[where \<Gamma> = \<Delta> and ae = "Aexp e\<cdot>(Astack ae S)"] by auto
  hence stack: "AEstack (Aheap \<Delta>\<cdot>(Aexp e\<cdot>(Astack ae S)) \<squnion> ae) S = AEstack ae S"
               "Astack (Aheap \<Delta>\<cdot>(Aexp e\<cdot>(Astack ae S)) \<squnion> ae) S = Astack ae S"
    by (auto simp add: edomIff cong: AEstack_cong Astack_cong)


  have "edom ae \<subseteq> - domA \<Delta>" using let\<^sub>1(3)
    using fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)]
    by (fastforce dest: set_mp[OF ups_fv_subset])
  hence "(?ae \<squnion> ae) f|` (- domA \<Delta>) = ae"
    by (auto simp add: env_restr_join  env_restr_useless disjoint_eq_subset_Compl edom_Aheap)
  moreover
  {
  have "edom (?ae \<squnion> ae) \<subseteq> domA (\<Delta> @ \<Gamma>) \<union> upds S"
    using let\<^sub>1(3) by (auto dest: set_mp[OF edom_Aheap])
  moreover
  have "upds S \<subseteq> edom (?ae \<squnion> ae)"
    using let\<^sub>1(3) by auto
  moreover
  have "AEstack ae S \<sqsubseteq> ?ae \<squnion> ae"
    by (rule AE_consistentE[OF let\<^sub>1(3)])
       (metis "join_above1" below_refl box_below join_comm)
  moreover
  {
  have "Aexp e\<cdot>(Astack ae S) \<sqsubseteq> (Aexp e\<cdot>(Astack ae S) f|` domA \<Delta>) \<squnion> (Aexp e\<cdot>(Astack ae S) f|` (- domA \<Delta>))"
    by (rule eq_imp_below[OF join_env_restr_UNIV[symmetric]]) auto
  also have "Aexp e\<cdot>(Astack ae S) f|` (- domA \<Delta>) \<sqsubseteq> Aexp (Terms.Let \<Delta> e)\<cdot>(Astack ae S)" by (rule Aexp_Let_above)
  also have "\<dots> \<sqsubseteq> ae" by (rule AE_consistentE[OF let\<^sub>1(3)])
  also have "Aexp e\<cdot>(Astack ae S) f|` domA \<Delta> \<sqsubseteq> ?ae" by (rule Aheap_above_arg)
  finally have "Aexp e\<cdot>(Astack ae S) \<sqsubseteq> ?ae \<squnion> ae" by this auto
  }
  moreover
  { fix x e'
    assume "map_of \<Delta> x = Some e'"
    hence "x \<notin> edom ae" using `edom ae \<subseteq> - domA \<Delta>` by (metis Compl_iff contra_subsetD domI dom_map_of_conv_domA)
    hence "Aexp' e'\<cdot>((?ae \<squnion> ae) x) = Aexp' e'\<cdot>(?ae x)" by (auto simp add: edomIff)
    also
    have "Aexp' e'\<cdot>(?ae x) \<sqsubseteq> (Aexp' e'\<cdot>(?ae x) f|` domA \<Delta>) \<squnion> (Aexp' e'\<cdot>(?ae x) f|` (- domA \<Delta>))"
      by (rule eq_imp_below[OF join_env_restr_UNIV[symmetric]]) auto
    also
    from `map_of \<Delta> x = Some e'`
    have "Aexp' e'\<cdot>(?ae x) f|` domA \<Delta> \<sqsubseteq> ?ae" by (rule Aheap_heap)
    also
    from `map_of \<Delta> x = Some e'`
    have "Aexp' e'\<cdot>(?ae x) f|` (- domA \<Delta>) \<sqsubseteq> Aexp (Terms.Let \<Delta> e)\<cdot>(Astack ae S)" by (rule Aheap_heap2)
    also
    have "Aexp (Terms.Let \<Delta> e)\<cdot>(Astack ae S) \<sqsubseteq> ae"  by (rule AE_consistentE[OF let\<^sub>1(3)])
    finally
    have "Aexp' e'\<cdot>((?ae \<squnion> ae) x) \<sqsubseteq> ?ae \<squnion> ae" by this auto
  }
  moreover
  { fix x e'
    assume "map_of \<Gamma> x = Some e'"
    hence "x \<in> domA \<Gamma>" by (metis domI dom_map_of_conv_domA)
    hence "x \<notin>  edom ?ae" using fresh_distinct[OF let\<^sub>1(1)]  by (auto dest: set_mp[OF edom_Aheap])
    with let\<^sub>1 `map_of \<Gamma> x = Some e'`
    have "Aexp' e'\<cdot>((?ae \<squnion> ae) x) \<sqsubseteq> ae" by (auto simp add: edomIff)
    hence "Aexp' e'\<cdot>((?ae \<squnion> ae) x) \<sqsubseteq> ?ae \<squnion> ae" by (metis (erased, hide_lams) "HOLCF-Join-Classes.join_above2" below_trans)
  }
  ultimately
  have "AE_consistent (?ae \<squnion> ae) (\<Delta> @ \<Gamma>, e, S) "
    by (auto intro!: AE_consistentI simp add: stack)
  }
  ultimately
  show ?case unfolding new by auto
qed


(*

nominal_function maybeVar :: "exp \<Rightarrow> var option" where
  "maybeVar (Var x) = Some x" |
  "maybeVar (Lam [x]. e) = None" |
  "maybeVar (App e x) = None" |
  "maybeVar (Let as e) = None"
  unfolding maybeVar_graph_aux_def eqvt_def
  apply simp
  apply simp
  apply (metis exp_strong_exhaust)
  apply auto
  done
nominal_termination (eqvt) by lexicographic_order

fun conf_arities :: "conf \<Rightarrow> AEnv"
  where "conf_arities (\<Gamma>,e,S) = (case maybeVar e of Some x \<Rightarrow> (AE_singleton x) \<cdot> (up\<cdot>(stack_arity S)) | None \<Rightarrow> \<bottom>)"

fun trace_arities :: "conf list \<Rightarrow> AEnv"
  where
  "trace_arities [] = \<bottom>"
 |"trace_arities ((\<Gamma>,e,S)#T) = conf_arities (\<Gamma>,e,S) \<squnion> trace_arities T"


context CorrectArityAnalysis
begin

fun  conf_analysis :: "conf \<Rightarrow> AEnv"
where "conf_analysis (\<Gamma>,e,S) = Afix \<Gamma>\<cdot>(Aexp e\<cdot>(stack_arity S))" 
lemmas conf_analysis.simps[simp del]

lemma arity_preservation:
  assumes "(\<Gamma>, e, S) \<Rightarrow> (\<Gamma>', e', S')"
  shows "conf_analysis (\<Gamma>', e', S')  f|` (- (domA \<Gamma>' - domA \<Gamma>))  \<sqsubseteq> conf_analysis (\<Gamma>, e, S)  f|` (- (domA \<Gamma>' - domA \<Gamma>)) "
sorry

lemma arity_correct_now:
  shows "conf_arities (\<Gamma>, e, S) \<sqsubseteq> conf_analysis (\<Gamma>, e, S)"
proof(cases e rule: maybeVar.cases)
case goal1
  have "up\<cdot>(stack_arity S) \<sqsubseteq> (Aexp (Var x)\<cdot>(stack_arity S)) x" by (simp add: Aexp_Var)
  also have "(Aexp (Var x)\<cdot>(stack_arity S)) \<sqsubseteq>  (Afix \<Gamma>\<cdot>(Aexp (Var x)\<cdot>(stack_arity S)))" by (rule Afix_above_arg)
  finally
  have "up\<cdot>(stack_arity S) \<sqsubseteq> (Afix \<Gamma>\<cdot>(Aexp (Var x)\<cdot>(stack_arity S))) x" by this simp
  thus ?thesis using `e = _` unfolding conf_analysis.simps by simp
qed auto

theorem
  assumes "(\<Gamma>, e, S) \<Rightarrow>\<^sup>*\<^bsub>T\<^esub> (\<Delta>, v, S')"
  shows "trace_arities ((\<Gamma>, e, S) # T) f|` (- (domA \<Delta> - domA \<Gamma>)) \<sqsubseteq> conf_analysis (\<Gamma>, e, S)  f|` (- (domA \<Delta> - domA \<Gamma>))"
using assms
proof(induction rule: conf_trace_induct_final)
  case (trace_nil \<Gamma> e S)
    thus ?case by (simp del: app_strict conf_arities.simps) (rule arity_correct_now)
next
  case (trace_cons \<Gamma> e S T \<Gamma>' e' S')

  have "domA \<Gamma> \<subseteq> domA \<Gamma>'" and "domA \<Gamma>' \<subseteq> domA \<Delta>" sorry
  hence subset1: "- (domA \<Delta> - domA \<Gamma>) \<subseteq> - (domA \<Delta> - domA \<Gamma>')" and
        subset2: "- (domA \<Delta> - domA \<Gamma>) \<subseteq> - (domA \<Gamma>' - domA \<Gamma>)" by auto

  from arity_correct_now
  have "conf_arities (\<Gamma>, e, S)  f|` (- (domA \<Delta> - domA \<Gamma>)) \<sqsubseteq> conf_analysis (\<Gamma>, e, S)  f|` (- (domA \<Delta> - domA \<Gamma>))" by (rule env_restr_mono)
  moreover
  from trace_cons(3)
  have "trace_arities ((\<Gamma>', e', S') # T)  f|` (- (domA \<Delta> - domA \<Gamma>)) \<sqsubseteq> conf_analysis (\<Gamma>', e', S')  f|` (- (domA \<Delta> - domA \<Gamma>))"
    by (rule env_restr_below_subset[OF subset1])
  moreover
  from `(\<Gamma>, e, S) \<Rightarrow> (\<Gamma>', e', S')`
  have "conf_analysis (\<Gamma>', e', S')  f|` (- (domA \<Gamma>' - domA \<Gamma>)) \<sqsubseteq> conf_analysis (\<Gamma>, e, S)  f|` (- (domA \<Gamma>' - domA \<Gamma>))"
    by (rule arity_preservation)
  hence "conf_analysis (\<Gamma>', e', S')  f|` (- (domA \<Delta> - domA \<Gamma>)) \<sqsubseteq> conf_analysis (\<Gamma>, e, S)  f|` (- (domA \<Delta> - domA \<Gamma>))"
    by (rule env_restr_below_subset[OF subset2])
  ultimately
  show ?case by (auto intro: join_below dest: below_trans simp add: env_restr_join simp del: conf_arities.simps fun_meet_simp)
qed

*)
end

context CorrectArityAnalysis 
begin

sublocale CorrectArityAnalysis2 Aexp "\<lambda> \<Gamma>. \<Lambda> ae. (Afix \<Gamma> \<cdot> ae f|` domA \<Gamma>)"
apply default
  apply simp

  apply simp
  apply (subst Env.lookup_env_restr)
  apply (metis domI dom_map_of_conv_domA)
  apply (rule env_restr_mono)
  apply (metis (erased, hide_lams) "HOLCF-Join-Classes.join_above2" ABind_eq ArityAnalysis.Abinds_Afix ArityAnalysis.Abinds_reorder1 join_comm monofun_cfun_fun)

  apply simp
  apply (subst Env.lookup_env_restr)
  apply (metis domI dom_map_of_conv_domA)
  apply (rule below_trans[OF _ Aexp_Let])
  apply (rule env_restr_mono)
  apply (metis (erased, hide_lams) "HOLCF-Join-Classes.join_above2" ABind_eq ArityAnalysis.Abinds_Afix ArityAnalysis.Abinds_reorder1 join_comm monofun_cfun_fun)


  apply simp
  apply (metis ArityAnalysis.Afix_above_arg env_restr_mono)

  apply (rule below_trans[OF _ Aexp_Let])
  apply (metis ArityAnalysis.Afix_above_arg env_restr_mono)




done
end

end
