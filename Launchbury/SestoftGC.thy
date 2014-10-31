theory SestoftGC
imports Sestoft 
begin

inductive gc_step :: "conf \<Rightarrow> conf \<Rightarrow> bool" (infix "\<Rightarrow>\<^sub>G" 50) where
  normal:  "c \<Rightarrow> c' \<Longrightarrow> c \<Rightarrow>\<^sub>G c'"
| drop:    "(\<Gamma>, e, S) \<Rightarrow>\<^sub>G (restrictA V \<Gamma>, e, S)"
| dropUpd: "(\<Gamma>, e, Upd x # S) \<Rightarrow>\<^sub>G (\<Gamma>, e, S)"

lemmas gc_step_intros[intro] =
  normal[OF step.intros(1)] normal[OF step.intros(2)] normal[OF step.intros(3)]
  normal[OF step.intros(4)] normal[OF step.intros(5)] drop dropUpd


abbreviation gc_steps (infix "\<Rightarrow>\<^sub>G\<^sup>*" 50) where "gc_steps \<equiv> gc_step\<^sup>*\<^sup>*"

lemma var_onceI:
  assumes "map_of \<Gamma> x = Some e"
  shows "(\<Gamma>, Var x, S) \<Rightarrow>\<^sub>G\<^sup>* (delete x \<Gamma>, e , S)"
proof-
  from assms 
  have "(\<Gamma>, Var x, S) \<Rightarrow>\<^sub>G (delete x \<Gamma>, e , Upd x # S)"..
  moreover
  have "\<dots> \<Rightarrow>\<^sub>G  (delete x \<Gamma>, e , S)"..
  ultimately
  show ?thesis by (rule converse_rtranclp_into_rtranclp[OF _ r_into_rtranclp])
qed

lemma normal_trans:  "c \<Rightarrow>\<^sup>* c' \<Longrightarrow> c \<Rightarrow>\<^sub>G\<^sup>* c'"
  by (induction rule:rtranclp_induct) (auto dest: normal)


end

