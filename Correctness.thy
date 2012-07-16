theory Correctness
  imports Denotational Launchbury
begin

lemma preserve_meaning:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  and "x \<in> set L"
  and "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>\<Delta>\<rbrace>\<rho>"
  shows "\<lbrakk>Var x\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk>Var x\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
proof(cases "x \<in> heapVars \<Gamma>")
case True
  thus ?thesis
  using fmap_less_eqD[OF `\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>\<Delta>\<rbrace>\<rho>`, of x] 
  by (auto simp add: heapVars_def)
next
case False with reds_avoids_live[OF assms(1,2)]
  have "\<lbrakk>Var x\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = the (lookup \<rho> x)" and "\<lbrakk>Var x\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> = the (lookup \<rho> x)"
    by (auto intro:  the_lookup_HSem_other simp add: heapVars_def)
  thus ?thesis by simp
qed

theorem correctness:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  shows "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>" and "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>\<Delta>\<rbrace>\<rho>"
  using assms
proof(nominal_induct avoiding: \<rho>  rule:reds.strong_induct)
print_cases
case (Lambda \<Gamma> x e)
  case 1 show ?case by simp
  case 2 show ?case by simp
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> z e') case 1
  have "\<lbrakk> App e x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp also
  have "... = \<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    using `\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = _` by simp also
  have "... = \<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
    by (subst preserve_meaning[OF `\<Gamma> : e \<Down>\<^bsub>x # L\<^esub> \<Delta> : Lam [y]. e'` _ `\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>\<Delta>\<rbrace>\<rho>`], auto) also
  have "... = (\<Lambda> v. \<lbrakk> e' \<rbrakk>\<^bsub>(\<lbrace>\<Delta>\<rbrace>\<rho>)(y f\<mapsto> v)\<^esub>)\<cdot>(\<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>)"
    using `atom y \<sharp> \<Delta>` and `atom y \<sharp> \<rho>` by simp also
  have "... = \<lbrakk> e' \<rbrakk>\<^bsub>(\<lbrace>\<Delta>\<rbrace>\<rho>)(y f\<mapsto> (\<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>))\<^esub>"
    by simp also
  have "... = \<lbrakk>  e'[y::=x] \<rbrakk>\<^bsub>(\<lbrace>\<Delta>\<rbrace>\<rho>)\<^esub>"
    using `atom y \<sharp> \<Delta>` and `atom y \<sharp> \<rho>` and `atom y \<sharp> x` by-(rule ESem_subst, simp_all add:fresh_at_base) also
  have "... = \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Theta>\<rbrace>\<rho>\<^esub>"
    using `\<lbrakk>  e'[y::=x] \<rbrakk>\<^bsub>_\<^esub> = _` by simp
  finally
  show ?case .
  case 2 show ?case using `\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> _` `\<lbrace>\<Delta>\<rbrace>\<rho> \<le> _`  by simp
next


oops

end


