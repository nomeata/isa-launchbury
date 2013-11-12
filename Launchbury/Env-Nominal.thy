theory "Env-Nominal"
  imports Env "Nominal-Utils" "Nominal-HOLCF"
begin

subsubsection {* Permtuations on finite maps *}

instantiation "fmap" :: (pt,pcpo_pt) pt
begin
  lift_definition permute_fmap :: "perm \<Rightarrow> 'a f\<rightharpoonup> 'b \<Rightarrow> 'a f\<rightharpoonup> 'b"
    is "\<lambda> p f . p \<bullet> f" ..
  
  instance
  apply(default)
  apply(transfer, simp)+
  done
end

subsubsection {* Equivariance lemmas related to finite maps *}

lemma lookup_eqvt[eqvt]:
  "\<pi> \<bullet> lookup m x = lookup (\<pi> \<bullet> m) (\<pi> \<bullet> x)"
  by transfer simp

lemma the_lookup_perm[simp]:
  fixes \<rho> :: "'a::at_base f\<rightharpoonup> 'b::{pure,pcpo_pt}"
  shows "((x' \<leftrightarrow> x) \<bullet> \<rho>) f! xa = \<rho> f! ((x' \<leftrightarrow> x) \<bullet> xa) " 
  by (metis lookup_eqvt permute_flip_cancel permute_pure)

lemma fempty_eqvt[eqvt, simp]:
  "\<pi> \<bullet> f\<emptyset> = f\<emptyset>"
  by transfer auto

lemma fempty_supp[simp]: "supp f\<emptyset> = {}"
  by (metis eqvt_def fempty_eqvt supp_fun_eqvt)

lemma fempty_fresh[simp]: "a \<sharp> f\<emptyset>"
  by (simp add: fresh_def)

lemma fempty_fresh_star[simp]: "a \<sharp>* f\<emptyset>"
  by (simp add: fresh_star_def)

lemma fdom_perm: "fdom (\<pi> \<bullet> f) = \<pi> \<bullet> (fdom f)"
  by transfer auto

lemmas fdom_perm_rev[simp,eqvt] = fdom_perm[symmetric]

lemma mem_fdom_perm[simp]:
  fixes \<rho> :: "'a::at_base f\<rightharpoonup> 'b::{pcpo_pt}"
  shows "xa \<in> fdom (p \<bullet> \<rho>) \<longleftrightarrow> - p \<bullet> xa \<in> fdom \<rho>" 
  by (metis (mono_tags) fdom_perm_rev mem_Collect_eq permute_set_eq)

lemma fmap_upd_eqvt[eqvt]: "p \<bullet> (fmap_upd f x y) = fmap_upd (p \<bullet> f) (p \<bullet> x) (p \<bullet> y)"
  by transfer (metis fun_upd_eqvt)

lemma fmap_restr_eqvt[eqvt]:
  "\<pi> \<bullet> m f|` d = (\<pi> \<bullet> m) f|` (\<pi> \<bullet> d)"
  by transfer auto

lemma fmap_delete_eqvt[eqvt]:
  "\<pi> \<bullet> fmap_delete x m = fmap_delete (\<pi> \<bullet> x) (\<pi> \<bullet> m)"
  by transfer simp

lemma fmap_copy_eqvt[eqvt]:
  "\<pi> \<bullet> fmap_copy m a b = fmap_copy (\<pi> \<bullet> m) (\<pi> \<bullet> a) (\<pi> \<bullet> b)"
  by transfer simp

lemma fmap_add_eqvt[eqvt]:
  "\<pi> \<bullet> m1 f++\<^bsub>S\<^esub> m2 = (\<pi> \<bullet> m1) f++\<^bsub>\<pi> \<bullet> S\<^esub> (\<pi> \<bullet> m2)"
  by transfer simp

(*
lemma fmap_of_eqvt[eqvt]:
  "\<pi> \<bullet> fmap_of l = fmap_of (\<pi> \<bullet> l)"
  by transfer (rule map_of_eqvt)
*)

lemma fmap_map_eqvt[eqvt]:
  "\<pi> \<bullet> fmap_map f m = fmap_map (\<pi> \<bullet> f) (\<pi> \<bullet> m)"
by transfer simp

subsubsection {* Permutation and restriction *}

lemma fmap_restr_perm:
  fixes \<rho> :: "'a::at_base f\<rightharpoonup> 'b::{pcpo_pt,pure}"
  assumes "supp p \<sharp>* S" and [simp]: "finite S"
  shows "(p \<bullet> \<rho>) f|` S = \<rho> f|` S"
using assms
apply transfer
apply rule
apply (case_tac "x \<in> S")
apply (simp)
apply (subst permute_fun_def)
apply (simp add: permute_pure)
apply (subst perm_supp_eq)
apply (auto simp add:perm_supp_eq supp_minus_perm fresh_star_def fresh_def supp_set_elem_finite)
done

lemma fmap_restr_flip:
  fixes \<rho> :: "'a::at f\<rightharpoonup> 'b::{pcpo_pt,pure}"
  assumes "x \<notin> S" and "x' \<notin> S"
  shows "((x' \<leftrightarrow> x) \<bullet> \<rho>) f|` S = \<rho> f|` S"
  using assms
  apply transfer
  apply rule
  apply (auto  simp add: permute_flip_at split:if_splits)
  by (metis eqvt_lambda flip_at_base_simps(3) minus_flip permute_pure unpermute_def)

end
