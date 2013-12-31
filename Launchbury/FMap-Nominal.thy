theory "FMap-Nominal"
  imports FMap "Nominal-Utils"
begin

subsubsection {* Permtuations on finite maps *}

instantiation "fmap" :: (pt,pt) pt
begin
  lift_definition permute_fmap :: "perm \<Rightarrow> 'a::pt f\<rightharpoonup> 'b::pt \<Rightarrow> 'a f\<rightharpoonup> 'b"
    is "\<lambda> p f . p \<bullet> f" by (metis (full_types) dom_perm_rev permute_finite)
  
  instance
  apply(default)
  apply(transfer, simp)+
  done
end

subsubsection {* Equivariance lemmas related to finite maps *}

lemma lookup_eqvt[eqvt]:
  "\<pi> \<bullet> lookup m x = lookup (\<pi> \<bullet> m) (\<pi> \<bullet> x)"
  by transfer simp

lemma the_lookup_eqvt:
  "x \<in> fdom m \<Longrightarrow> \<pi> \<bullet> (m f! x) = (\<pi> \<bullet> m) f! (\<pi> \<bullet> x)"
  apply (transfer fixing: x) 
  apply auto
  by (metis Some_eqvt permute_fun_app_eq the.simps)

lemma the_lookup_perm[simp]:
  fixes \<rho> :: "'a::at_base f\<rightharpoonup> 'b::pure"
  shows "((x' \<leftrightarrow> x) \<bullet> \<rho>) f! xa = \<rho> f! ((x' \<leftrightarrow> x) \<bullet> xa) " 
  by (metis lookup_eqvt permute_flip_cancel permute_pure)

lemma fempty_eqvt[eqvt, simp]:
  "\<pi> \<bullet> fempty = fempty"
  by (transfer, auto simp add: permute_fun_def)

lemma fempty_supp[simp]: "supp fempty = {}"
  by (metis eqvtI fempty_eqvt supp_fun_eqvt)

lemma fempty_fresh[simp]: "a \<sharp> fempty"
  by (simp add: fresh_def)

lemma fempty_fresh_star[simp]: "a \<sharp>* fempty"
  by (simp add: fresh_star_def)

lemma fdom_perm: "fdom (\<pi> \<bullet> f) = \<pi> \<bullet> (fdom f)"
  apply transfer by (rule dom_perm)
lemmas fdom_perm_rev[simp,eqvt] = fdom_perm[symmetric]

lemma mem_fdom_perm[simp]:
  fixes \<rho> :: "'a::at_base f\<rightharpoonup> 'b::pure"
  shows "xa \<in> fdom (p \<bullet> \<rho>) \<longleftrightarrow> - p \<bullet> xa \<in> fdom \<rho>" 
  by (metis (mono_tags) fdom_perm_rev mem_Collect_eq permute_set_eq)

lemma fmap_upd_eqvt[eqvt]: "p \<bullet> (fmap_upd f x y) = fmap_upd (p \<bullet> f) (p \<bullet> x) (p \<bullet> y)"
  by transfer (metis Some_eqvt fun_upd_eqvt)

lemma fmap_restr_eqvt[eqvt]:
  "\<pi> \<bullet> (fmap_restr d m) = fmap_restr (\<pi> \<bullet> d) (\<pi> \<bullet> m)"
proof
case goal1 thus ?case by (metis fdom_fmap_restr fdom_perm_rev inter_eqvt)
case goal2
  from goal2 have "x \<in> \<pi> \<bullet> fdom m \<inter> \<pi> \<bullet> d" by (metis (full_types) fdom_fmap_restr fdom_perm_rev inter_eqvt)
  then obtain y where "x = \<pi> \<bullet> y" and "y \<in> fdom m \<inter> d" by (auto simp add: permute_set_def)

  have "(\<pi> \<bullet> fmap_restr d m) f! x = (\<pi> \<bullet> fmap_restr d m) f! (\<pi> \<bullet> y)" by (simp add: `x = _`)
  also have "... = \<pi> \<bullet> ((fmap_restr d m) f! y)" using  `y \<in> fdom m \<inter> d` by (metis fdom_fmap_restr the_lookup_eqvt)
  also have "... = \<pi> \<bullet> (m f! y)" using `y \<in> _` by simp
  also have "... = (\<pi> \<bullet> m) f! x" using `x = _` `y \<in> _` by (simp add: the_lookup_eqvt)
  also have "... = fmap_restr (\<pi> \<bullet> d) (\<pi> \<bullet> m) f! x" using `x \<in> _ \<inter> _` by simp
  finally show ?case.
qed

lemma fmap_delete_eqvt[eqvt]:
  "\<pi> \<bullet> fmap_delete x m = fmap_delete (\<pi> \<bullet> x) (\<pi> \<bullet> m)"
  by transfer simp

lemma fmap_copy_eqvt[eqvt]:
  "\<pi> \<bullet> fmap_copy m a b = fmap_copy (\<pi> \<bullet> m) (\<pi> \<bullet> a) (\<pi> \<bullet> b)"
  by transfer simp

lemma fun_merge_eqvt[eqvt]:
  "\<pi> \<bullet> m1 f++ m2 = (\<pi> \<bullet> m1) f++ (\<pi> \<bullet> m2)"
  by transfer simp

lemma fmap_of_eqvt[eqvt]:
  "\<pi> \<bullet> fmap_of l = fmap_of (\<pi> \<bullet> l)"
by transfer (rule map_of_eqvt)

lemma fmap_map_eqvt[eqvt]:
  "\<pi> \<bullet> fmap_map f m = fmap_map (\<pi> \<bullet> f) (\<pi> \<bullet> m)"
by transfer simp

subsubsection {* Permutation and restriction *}

lemma fmap_restr_perm:
  fixes \<rho> :: "'a::at f\<rightharpoonup> 'b::pure"
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
  fixes \<rho> :: "'a::at f\<rightharpoonup> 'b::pure"
  assumes "x \<notin> S" and "x' \<notin> S"
  shows "((x' \<leftrightarrow> x) \<bullet> \<rho>) f|` S = \<rho> f|` S"
  using assms
  by (auto simp add: permute_flip_at  split:if_splits)

end
