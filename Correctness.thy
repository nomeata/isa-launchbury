theory Correctness
  imports Denotational Launchbury
begin


theorem correctness:
  assumes "\<Gamma> : e \<Down> \<Delta> : z"
  shows "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>" and "\<lbrace>\<Gamma>\<rbrace>\<rho> \<le> \<lbrace>\<Delta>\<rbrace>\<rho>"
  using assms
proof(nominal_induct avoiding: \<rho>  rule:reds.strong_induct)
print_cases
case (Lambda \<Gamma> x e)
  case 1 show ?case by simp
  case 2 show ?case by simp
next
case (Application y \<Gamma> e x \<Delta> \<Theta> z e') case 1
  have "\<lbrakk> App e x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp also
  have "... = \<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    using `\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = _` by simp also
  have "... = \<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> \<down>Fn \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
    sorry also
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


