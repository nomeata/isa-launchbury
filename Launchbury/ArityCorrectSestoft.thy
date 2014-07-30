theory ArityCorrectSestoft
imports ArityCorrect SestoftCorrect
begin

fun stack_arity :: "stack \<Rightarrow> Arity"
  where "stack_arity [] = 0"
      | "stack_arity (Arg x # S) = inc_Arity (stack_arity S)"
      | "stack_arity (Upd x # S) = stack_arity S"
      | "stack_arity (Dummy x # S) = stack_arity S"

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
  where "conf_arities (\<Gamma>,e,S) = (case maybeVar e of Some x \<Rightarrow> AE_singleton x \<cdot> (up\<cdot>(stack_arity S)) | None \<Rightarrow> \<bottom>)"

fun trace_arities :: "conf list \<Rightarrow> AEnv"
  where
  "trace_arities [] = \<bottom>"
 |"trace_arities ((\<Gamma>,e,S)#T) = conf_arities (\<Gamma>,e,S) \<squnion> trace_arities T"


context CorrectArityAnalysis
begin

lemma arity_preservation:
  assumes "(\<Gamma>, e, S) \<Rightarrow> (\<Gamma>', e', S')"
  shows "Afix \<Gamma>'\<cdot>(Aexp e'\<cdot>(stack_arity S')) \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp e\<cdot>(stack_arity S))" sorry

lemma arity_correct_now:
  shows "conf_arities (\<Gamma>, e, S) \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp e\<cdot>(stack_arity S))"
proof(cases e rule: maybeVar.cases)
case goal1
  have "up\<cdot>(stack_arity S) \<sqsubseteq> (Aexp (Var x)\<cdot>(stack_arity S)) x" by (simp add: Aexp_Var)
  also have "(Aexp (Var x)\<cdot>(stack_arity S)) \<sqsubseteq>  (Afix \<Gamma>\<cdot>(Aexp (Var x)\<cdot>(stack_arity S)))" by (rule Afix_above_arg)
  finally
  have "up\<cdot>(stack_arity S) \<sqsubseteq> (Afix \<Gamma>\<cdot>(Aexp (Var x)\<cdot>(stack_arity S))) x" by this simp
  thus ?thesis using `e = _` by simp
qed auto

theorem
  assumes "(\<Gamma>, e, S) \<Rightarrow>\<^sup>*\<^bsub>T\<^esub> final"
  shows "trace_arities ((\<Gamma>, e, S) # T) \<sqsubseteq> Afix \<Gamma> \<cdot> (Aexp e \<cdot> (stack_arity S))"
using assms
proof(induction rule: conf_trace_induct_final)
  case (trace_nil \<Gamma> e S)
    thus ?case by (simp del: app_strict conf_arities.simps) (rule arity_correct_now)
next
  case (trace_cons \<Gamma> e S T \<Gamma>' e' S')

  have "conf_arities (\<Gamma>, e, S) \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp e\<cdot>(stack_arity S))" by (rule arity_correct_now)
  moreover
  note `trace_arities ((\<Gamma>', e', S') # T) \<sqsubseteq> Afix \<Gamma>'\<cdot>(Aexp e'\<cdot>(stack_arity S'))`
  moreover
  from `(\<Gamma>, e, S) \<Rightarrow> (\<Gamma>', e', S')`
  have "Afix \<Gamma>'\<cdot>(Aexp e'\<cdot>(stack_arity S')) \<sqsubseteq> Afix \<Gamma>\<cdot>(Aexp e\<cdot>(stack_arity S))"
    by (rule arity_preservation)
  ultimately
  show ?case by (auto intro: join_below dest: below_trans simp del: conf_arities.simps fun_meet_simp)
qed

end
