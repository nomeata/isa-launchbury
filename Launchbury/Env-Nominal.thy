theory "Env-Nominal"
  imports Env "Nominal-Utils" "Nominal-HOLCF"
begin

subsubsection {* Equivariance lemmas  *}

lemma fdom_perm:
  fixes f :: "'a::pt \<Rightarrow> 'b::{pcpo_pt}"
  shows "fdom (\<pi> \<bullet> f) = \<pi> \<bullet> (fdom f)"
  by (simp add: fdom_def)

lemmas fdom_perm_rev[simp,eqvt] = fdom_perm[symmetric]

lemma mem_fdom_perm[simp]:
  fixes \<rho> :: "'a::at_base \<Rightarrow> 'b::{pcpo_pt}"
  shows "xa \<in> fdom (p \<bullet> \<rho>) \<longleftrightarrow> - p \<bullet> xa \<in> fdom \<rho>" 
  by (metis (mono_tags) fdom_perm_rev mem_Collect_eq permute_set_eq)

lemma fmap_restr_eqvt[eqvt]:
  fixes m :: "'a::pt \<Rightarrow> 'b::{cont_pt,pcpo}"
  shows "\<pi> \<bullet> m f|` d = (\<pi> \<bullet> m) f|` (\<pi> \<bullet> d)"
  by (auto simp add: fmap_restr_def)

lemma fmap_delete_eqvt[eqvt]:
  fixes m :: "'a::pt \<Rightarrow> 'b::{cont_pt,pcpo}"
  shows "\<pi> \<bullet> fmap_delete x m = fmap_delete (\<pi> \<bullet> x) (\<pi> \<bullet> m)"
  by (auto simp add: fmap_delete_def)

lemma fun_merge_eqvt[eqvt]:
  fixes m1 m2 :: "'a::pt \<Rightarrow> 'b::{cont_pt,pcpo}"
  shows "\<pi> \<bullet> m1 f++\<^bsub>S\<^esub> m2 = (\<pi> \<bullet> m1) f++\<^bsub>\<pi> \<bullet> S\<^esub> (\<pi> \<bullet> m2)"
  by (auto simp add: fun_merge_def )

subsubsection {* Permutation and restriction *}

lemma fmap_restr_perm:
  fixes \<rho> :: "'a::at_base \<Rightarrow> 'b::{pcpo_pt,pure}"
  assumes "supp p \<sharp>* S" and [simp]: "finite S"
  shows "(p \<bullet> \<rho>) f|` S = \<rho> f|` S"
using assms
apply -
apply (rule ext)
apply (case_tac "x \<in> S")
apply (simp)
apply (subst permute_fun_def)
apply (simp add: permute_pure)
apply (subst perm_supp_eq)
apply (auto simp add:perm_supp_eq supp_minus_perm fresh_star_def fresh_def supp_set_elem_finite)
done

lemma fmap_restr_flip:
  fixes \<rho> :: "'a::at \<Rightarrow> 'b::{pcpo_pt,pure}"
  assumes "x \<notin> S" and "x' \<notin> S"
  shows "((x' \<leftrightarrow> x) \<bullet> \<rho>) f|` S = \<rho> f|` S"
  using assms
  apply -
  apply rule
  apply (auto  simp add: permute_flip_at fmap_restr_def split:if_splits)
  by (metis eqvt_lambda flip_at_base_simps(3) minus_flip permute_pure unpermute_def)

end