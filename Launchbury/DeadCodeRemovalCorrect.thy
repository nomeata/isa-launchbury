theory DeadCodeRemovalCorrect
imports Launchbury LaunchburyAbstractTransformation DeadCodeRemoval
begin

definition rdcH :: "var set \<Rightarrow> heap \<Rightarrow> heap"
  where "rdcH S \<Gamma> = [ (x, remove_dead_code e) . (x,e) \<leftarrow> \<Gamma>, x \<notin> S]" 

inductive dc_rel :: "(heap \<times> exp) \<Rightarrow> var list \<Rightarrow> (heap \<times> exp) \<Rightarrow>  bool" ("_ \<triangleright>\<^bsub>_\<^esub> _" [50,50,50] 50 )
  where "S \<subseteq> domA \<Gamma> \<union> set L \<Longrightarrow> (\<Gamma>, e) \<triangleright>\<^bsub>L\<^esub> (rdcH S \<Gamma>, remove_dead_code e)"


interpretation rel_lambda_cong dc_rel
  by default (fastforce elim: dc_rel.cases)
interpretation rel_app_cong dc_rel
  by default (auto elim: dc_rel.cases)
interpretation rel_var_cong dc_rel
  by default (auto elim: dc_rel.cases)

locale let_removed = 
  fixes \<Gamma> as body
  assumes "domA as \<inter> fv body = {} "

locale let_not_removed = 
  fixes as :: heap and  body :: exp
  assumes let_not_removed: " domA as \<inter> fv body \<noteq> {} "
begin
sublocale rel_let_cong dc_rel  \<Gamma> as body for \<Gamma>
  apply default
  proof-
    case goal1
    show thesis apply (rule goal1(2))
    using goal1(1) let_not_removed
    by (auto elim!: dc_rel.cases simp add: if_not_P[OF let_not_removed])
  qed

sublocale rel_let_case dc_rel  \<Gamma> as body for \<Gamma> sorry
end
  

interpretation reds_rel_fresh dc_rel sorry

interpretation rel_lambda_case dc_rel by default
interpretation rel_app_case dc_rel sorry
interpretation rel_var_case dc_rel sorry


theorem DeadCodeRemovalCorrect:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  assumes "(\<Gamma>, e) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', e')"
   shows  "\<exists> \<Delta>' z'. (\<Delta>, z) \<triangleright>\<^bsub>L\<^esub> (\<Delta>', z') \<and> \<Gamma>' : e' \<Down>\<^bsub>L\<^esub> \<Delta>' : z'"
  using assms
proof(nominal_induct arbitrary: \<Gamma>' e' rule:reds.strong_induct)
case (Lambda \<Gamma> x e L) thus ?case by (rule lambda_case)
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> z body) thus ?case by (rule app_case)
next
case (Variable \<Gamma> x e L \<Delta> z \<Gamma>' var) thus ?case by (rule var_case)
next
case (Let as \<Gamma> L body \<Delta> z \<Gamma>' let')
  show ?case
  proof (cases "domA as \<inter> fv body = {}")
  case True
    with `(\<Gamma>, Let as body) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', let')` 
    have "let' = remove_dead_code body" by (auto elim!: dc_rel.cases)
    from `(\<Gamma>, Let as body) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', let')`[unfolded `let' = _`]
    have "(as @ \<Gamma>, body) \<triangleright>\<^bsub>L\<^esub> (\<Gamma>', remove_dead_code body)" sorry
    from Let(4)[OF this]
    show ?thesis unfolding `let' = _`.
  next
  case False
    interpret let_not_removed as body apply default using False.
    show ?thesis using Let by (rule let_case)
  qed
qed

end
