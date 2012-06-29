theory "Nominal-HOLCF"
imports
  "Nominal/Nominal/Nominal2" "~~/src/HOL/HOLCF/HOLCF"
begin

class cont_pt = 
  cpo + 
  pt +
  assumes perm_cont: "\<And>p. cont ((permute p) :: 'a::{cpo,pt} \<Rightarrow> 'a)"

class discr_pt = 
  discrete_cpo + 
  pt

instance discr_pt \<subseteq> cont_pt
 by (default, auto)


lemma (in cont_pt) perm_cont_simp[simp]: "\<pi> \<bullet> x \<sqsubseteq> \<pi> \<bullet> y \<longleftrightarrow> x \<sqsubseteq> y"
  apply rule
  apply (drule cont2monofunE[OF perm_cont, of _ _ "-\<pi>"], simp)[1]
  apply (erule cont2monofunE[OF perm_cont, of _ _ "\<pi>"])
  done

lemmas perm_cont2cont[simp,cont2cont] = cont_compose[OF perm_cont]

lemma perm_bottom[simp,eqvt]: "\<pi> \<bullet> \<bottom> = (\<bottom>::'a::{cont_pt,pcpo})"
  proof-
  have "\<bottom> \<sqsubseteq> -\<pi> \<bullet> (\<bottom>::'a::{cont_pt,pcpo})" by simp
  hence "\<pi> \<bullet> \<bottom> \<sqsubseteq> \<pi> \<bullet> (-\<pi> \<bullet> (\<bottom>::'a::{cont_pt,pcpo}))" by(rule cont2monofunE[OF perm_cont])
  hence "\<pi> \<bullet> \<bottom> \<sqsubseteq> (\<bottom>::'a::{cont_pt,pcpo})" by simp
  thus "\<pi> \<bullet> \<bottom> = (\<bottom>::'a::{cont_pt,pcpo})" by simp
qed


instantiation "cfun" :: (cont_pt, cont_pt) pt
begin
  definition "p \<bullet> (f :: 'a  \<rightarrow> 'b) = (\<Lambda> x. p \<bullet> (f \<cdot> (- p \<bullet> x)))"

  instance
  apply(default)
  apply (simp add: permute_cfun_def eta_cfun)
  apply (simp add: permute_cfun_def cfun_eqI minus_add)
  done
end

(*
Is this possible?
lemma permute_fun_eq: "permute p = (\<lambda> f x. permute p (f (permute (-p) x)))"
  by (rule, rule, auto simp add: permute_fun_def)

instance "fun" :: (cont_pt, cont_pt) cont_pt
  apply (default)
  apply (subst permute_fun_eq)
  using [[show_sorts]]
  apply (rule perm_cont2cont)
  apply (intro cont2cont)
*)

lemma permute_cfun_eq: "permute p = (\<lambda> f. (Abs_cfun (permute p)) oo f oo (Abs_cfun (permute (-p))))"
  by (rule, rule cfun_eqI, auto simp add: permute_cfun_def)

instance "cfun" :: (cont_pt, cont_pt) cont_pt
  by (default,subst permute_cfun_eq, auto)

lemma Lam_eqvt:
  "cont f \<Longrightarrow> \<pi> \<bullet> Abs_cfun f = Abs_cfun (\<pi> \<bullet> f)"
  unfolding permute_fun_def permute_cfun_def
  by auto

lemma Cfun_app_eqvt[eqvt]:
  "\<pi> \<bullet> (f \<cdot> x) = (\<pi> \<bullet> f) \<cdot> (\<pi> \<bullet> x)"
  unfolding permute_cfun_def
  by auto

(*
lemma Rep_cfun_eqvt[eqvt]:
  "\<pi> \<bullet> (Rep_cfun f) = Rep_cfun (\<pi> \<bullet> f)"
  unfolding permute_cfun_def permute_fun_def
  by auto
*)

class pure_cpo = Nominal2_Base.pure + cpo

instance pure_cpo \<subseteq> cont_pt
  apply default
  proof-
    fix p :: perm
    have "permute p = ((\<lambda>x. x) :: 'a \<Rightarrow> 'a)" by(rule)(rule permute_pure)
    thus "cont (permute p :: 'a \<Rightarrow> 'a)" by (auto)
  qed

instance "cfun" :: (pure_cpo, pure_cpo) pure_cpo
  apply default
  apply (auto  simp add: permute_cfun_def permute_pure Cfun.cfun.Rep_cfun_inverse)
  done


end
