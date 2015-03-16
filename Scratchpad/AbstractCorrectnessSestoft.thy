theory AbstractCorrectnessSestoft
imports AbstractCorrectness Sestoft
begin

locale AbstractCorrectnessSestoft = AbstractCorrectness step +
  assumes conf_app\<^sub>1:    "(\<Gamma>, App e x, S) \<triangleright> s \<Longrightarrow> (\<Gamma>, e, Arg x # S) \<triangleright> update (\<Gamma>, App e x, S) s"
  assumes trans_app\<^sub>1:   "(\<Gamma>, App e x, S) \<triangleright> s \<Longrightarrow> trans s (\<Gamma>, App e x, S) \<Rightarrow>\<^sup>* trans (update (\<Gamma>, App e x, S) s) (\<Gamma>, e, Arg x # S)"  
  assumes conf_app\<^sub>2:    "(\<Gamma>, Lam [y]. e, Arg x # S) \<triangleright> s \<Longrightarrow> (\<Gamma>, e[y::=x], S) \<triangleright> update (\<Gamma>, Lam [y]. e, Arg x # S) s"
  assumes trans_app\<^sub>2:   "(\<Gamma>, Lam [y]. e, Arg x # S) \<triangleright> s \<Longrightarrow> trans s (\<Gamma>, Lam [y]. e, Arg x # S) \<Rightarrow>\<^sup>* trans (update (\<Gamma>, Lam [y]. e, Arg x # S) s) (\<Gamma>, e[y::=x], S)"
  assumes conf_thunk:   "map_of \<Gamma> x = Some e \<Longrightarrow> \<not> isLam e \<Longrightarrow> (\<Gamma>, Var x, S) \<triangleright> s \<Longrightarrow> (delete x \<Gamma>, e, Upd x # S) \<triangleright> update (\<Gamma>, Var x, S) s"
  assumes trans_thunk:  "map_of \<Gamma> x = Some e \<Longrightarrow> \<not> isLam e \<Longrightarrow> (\<Gamma>, Var x, S) \<triangleright> s \<Longrightarrow> trans s (\<Gamma>, Var x, S) \<Rightarrow>\<^sup>* trans (update (\<Gamma>, Var x, S) s) (delete x \<Gamma>, e, Upd x # S)"
  assumes conf_lamvar:  "map_of \<Gamma> x = Some e \<Longrightarrow> isLam e \<Longrightarrow> (\<Gamma>, Var x, S) \<triangleright> s \<Longrightarrow> ((x, e) # delete x \<Gamma>, e, S) \<triangleright> update (\<Gamma>, Var x, S) s"
  assumes trans_lamvar: "map_of \<Gamma> x = Some e \<Longrightarrow> isLam e \<Longrightarrow> (\<Gamma>, Var x, S) \<triangleright> s \<Longrightarrow> trans s (\<Gamma>, Var x, S) \<Rightarrow>\<^sup>* trans (update (\<Gamma>, Var x, S) s) ((x, e) # delete x \<Gamma>, e, S)"
  assumes conf_var\<^sub>2:    "x \<notin> domA \<Gamma> \<Longrightarrow> isLam e \<Longrightarrow> (\<Gamma>, e, Upd x # S) \<triangleright> s \<Longrightarrow> ((x, e) # \<Gamma>, e, S) \<triangleright> update (\<Gamma>, e, Upd x # S) s"
  assumes trans_var\<^sub>2:   "x \<notin> domA \<Gamma> \<Longrightarrow> isLam e \<Longrightarrow> (\<Gamma>, e, Upd x # S) \<triangleright> s \<Longrightarrow> trans s (\<Gamma>, e, Upd x # S) \<Rightarrow>\<^sup>* trans (update (\<Gamma>, e, Upd x # S) s) ((x, e) # \<Gamma>, e, S)"
  assumes conf_let:     "atom ` domA \<Delta> \<sharp>* \<Gamma> \<Longrightarrow> atom ` domA \<Delta> \<sharp>* S \<Longrightarrow> (\<Gamma>, Terms.Let \<Delta> e, S) \<triangleright> s \<Longrightarrow> (\<Delta> @ \<Gamma>, e, S) \<triangleright> update (\<Gamma>, Terms.Let \<Delta> e, S) s"
  assumes trans_let:    "atom ` domA \<Delta> \<sharp>* \<Gamma> \<Longrightarrow> atom ` domA \<Delta> \<sharp>* S \<Longrightarrow> (\<Gamma>, Terms.Let \<Delta> e, S) \<triangleright> s \<Longrightarrow> trans s (\<Gamma>, Terms.Let \<Delta> e, S) \<Rightarrow>\<^sup>* trans (update (\<Gamma>, Terms.Let \<Delta> e, S) s) (\<Delta> @ \<Gamma>, e, S)"
begin


lemma correct:
  assumes "c \<Rightarrow>\<^sup>* c'"
  assumes "\<not> boring_step c'"
  assumes "c \<triangleright> s"
  obtains s' where "c' \<triangleright> s'" and "trans s c \<Rightarrow>\<^sup>* trans s' c'"
proof-
  from assms
  have "\<exists> s'. c' \<triangleright> s' \<and> trans s c \<Rightarrow>\<^sup>* trans s' c'"
    apply (induction  arbitrary: s rule: step_induction)
    apply (rule exI, rule conjI[OF conf_app\<^sub>1 trans_app\<^sub>1], assumption+)
    apply (rule exI, rule conjI[OF conf_app\<^sub>2 trans_app\<^sub>2], assumption+)
    apply (rule exI, rule conjI[OF conf_thunk trans_thunk], assumption+)
    apply (rule exI, rule conjI[OF conf_lamvar trans_lamvar], assumption+)
    apply (rule exI, rule conjI[OF conf_var\<^sub>2 trans_var\<^sub>2], assumption+)
    apply (rule exI, rule conjI[OF conf_let trans_let], assumption+)
    apply auto[1]
    apply fastforce
    done
 thus ?thesis using that by auto
qed

end
end

