theory ArityCorrectSestoft
imports ArityCorrect SestoftCorrect
begin

fun Astack :: "AEnv \<Rightarrow> stack \<Rightarrow> Arity"
  where "Astack ae [] = 0"
      | "Astack ae (Arg x # S) = inc\<cdot>(Astack ae S)"
      | "Astack ae (Upd x # S) = (case ae x of Iup a \<Rightarrow> a)"
      | "Astack ae (Dummy x # S) = 0"

lemma Astack_Upd_simps[simp]:
  "ae x = up\<cdot>u \<Longrightarrow> Astack ae (Upd x # S) = u"
  by (simp add: up_def cont_Iup)
declare Astack.simps(3)[simp del]

fun AEstack :: "AEnv \<Rightarrow> stack \<Rightarrow> AEnv"
  where "AEstack ae [] = \<bottom>"
      | "AEstack ae (Arg x # S) = AE_singleton x \<cdot> (up\<cdot>0) \<squnion> AEstack ae S"
      | "AEstack ae (Upd x # S) = AE_singleton x \<cdot> (up\<cdot>(Astack ae S)) \<squnion> AEstack ae S"
      | "AEstack ae (Dummy x # S) = AEstack ae S"

context CorrectArityAnalysis
begin

inductive AE_consistent :: "AEnv \<Rightarrow> conf \<Rightarrow> bool" where
  AE_consistentI: 
  "upds S \<subseteq> edom ae
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
case (let\<^sub>1 x \<Gamma> e S)
  show ?case
    sorry
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
