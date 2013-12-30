theory Denotational
  imports "Abstract-Denotational-Props" Value
begin

interpretation semantic_domain Fn Fn_project "\<Lambda> x. x".

abbreviation ESem_syn'' ("\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60) where "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> \<equiv> ESem e \<cdot> \<rho>"
abbreviation HSem_syn' ("\<lbrace>_\<rbrace>_"  [60,60] 60) where "\<lbrace>\<Gamma>\<rbrace>\<rho> \<equiv> HSem \<Gamma> \<cdot> \<rho>"
abbreviation HSem_fempty  ("\<lbrace>_\<rbrace>"  [60] 60) where "\<lbrace>\<Gamma>\<rbrace> \<equiv> \<lbrace>\<Gamma>\<rbrace>\<bottom>"


subsubsection {* Replacing subexpressions by variables *}

lemma HSem_subst_var_app:
  assumes fresh: "atom n \<sharp> x"
  shows "\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho> "
proof(rule HSem_subst_expr)
  from fresh have [simp]: "n \<noteq> x" by (simp add: fresh_at_base)
  have ne: "(n,e) \<in> set ((x, App e y) # (n, e) # \<Gamma>)" by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = (\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>) n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    by (subst HSem_eq, simp)
  finally
  show "\<lbrakk> App (Var n) y \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> App e y \<rbrakk>\<^bsub>\<lbrace>(x, App e y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp

 have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = (\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>) n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    by (subst HSem_eq, simp)
  finally
  show "\<lbrakk> App e y \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> App (Var n) y \<rbrakk>\<^bsub>\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp
qed

lemma HSem_subst_var_var:
  assumes fresh: "atom n \<sharp> x"
  shows "\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho> "
proof(rule HSem_subst_expr)
  from fresh have [simp]: "n \<noteq> x" by (simp add: fresh_at_base)
  have ne: "(n,e) \<in> set ((x, e) # (n, e) # \<Gamma>)" by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = (\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>) n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    by (subst HSem_eq, simp)
  finally
  show "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>(x, e) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp

  have "\<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> = (\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>) n"
    by simp
  also have "... = \<lbrakk> e \<rbrakk>\<^bsub>(\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>)\<^esub>"
    by (subst HSem_eq, simp)
  finally
  show "\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> Var n \<rbrakk>\<^bsub>\<lbrace>(x, Var n) # (n, e) # \<Gamma>\<rbrace>\<rho>\<^esub>"
    by simp
qed

end
