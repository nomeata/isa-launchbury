theory "FMap-Nominal-HOLCF"
imports "Nominal-HOLCF" "FMap-Nominal" "FMap-HOLCF" "Nominal-Utils"
begin

subsubsection {* Permutation of finite maps is continuous *}

instance "fmap" :: (pt, cont_pt) cont_pt
apply default
proof(intro contI2 monofunI fmap_belowI)
  fix \<pi> m1 m2
  assume "m1 \<sqsubseteq> (m2 :: 'a f\<rightharpoonup> 'b)"
  hence "fdom m1 = fdom m2"
    by (rule fmap_below_dom)

  show "fdom (\<pi> \<bullet> m1) = fdom (\<pi> \<bullet> m2)"
    using `fdom m1 = fdom m2`
    by (simp add: fdom_perm del: fdom_perm_rev)

  fix x
  assume "x \<in> fdom (\<pi> \<bullet> m1)" and "x \<in> fdom (\<pi> \<bullet> m2)"
  moreover
  obtain x2 where "x = \<pi> \<bullet> x2" by (metis eqvt_bound)
  ultimately
  have "x2 \<in> fdom m1" "x2 \<in> fdom m2"
    using `x \<in> fdom (\<pi> \<bullet> m1)` `x \<in> fdom (\<pi> \<bullet> m2)`
    by (simp add: fdom_perm mem_permute_iff del: fdom_perm_rev)+

  have "(\<pi> \<bullet> m1) f! x = \<pi> \<bullet> (m1 f! x2)"
    by (simp add: the_lookup_eqvt[OF `x2 \<in> fdom m1`]  `x = _`)
  also have "... \<sqsubseteq> \<pi> \<bullet> (m2 f! x2)"
    by -(subst perm_cont_simp, rule fmap_belowE[OF `m1 \<sqsubseteq> m2`])
  also have "... \<sqsubseteq> (\<pi> \<bullet> m2) f! x"
    using `x = _`
    by (simp add: the_lookup_eqvt[OF `x2 \<in> fdom m2`]  )
  finally show "(\<pi> \<bullet> m1) f! x \<sqsubseteq> (\<pi> \<bullet> m2) f! x".

next
  fix \<pi> Y
  assume "chain (Y\<Colon>nat \<Rightarrow> 'a f\<rightharpoonup> 'b)"
  assume "chain (\<lambda>i. \<pi> \<bullet> Y i)"
  
  show "fdom (\<pi> \<bullet> (\<Squnion> i. Y i)) = fdom (\<Squnion> i. \<pi> \<bullet> Y i)"
      by (simp add: chain_fdom(2)[OF `chain (\<lambda>i. \<pi> \<bullet> Y i)`] chain_fdom(2)[OF `chain Y`] fdom_perm del: fdom_perm_rev)

  fix x
  assume "x \<in> fdom (\<pi> \<bullet> (\<Squnion> i. Y i))"
  moreover
  obtain x2 where "x = \<pi> \<bullet> x2" by (metis eqvt_bound)
  ultimately
  have "x2 \<in> fdom (\<Squnion> i. Y i)"
    using `x \<in> fdom (\<pi> \<bullet> (\<Squnion> i. Y i))` 
    by (simp add: fdom_perm mem_permute_iff del: fdom_perm_rev)+
  hence "x2 \<in> fdom (Y 0)"
    by (simp add: chain_fdom(2)[OF `chain Y`])
    
  have "\<pi> \<bullet> (\<Squnion> i. Y i) f! x = \<pi> \<bullet> ((\<Squnion> i. Y i) f! x2)"
    by (simp add: the_lookup_eqvt[OF `x2 \<in> fdom (\<Squnion> i. Y i)`]  `x = _`)
  also have "... = \<pi> \<bullet> (\<Squnion>i. (Y i f! x2))"
    by (subst lookup_cont[OF `chain Y`], rule refl)
  also have "... = (\<Squnion>i. \<pi> \<bullet> (Y i f! x2))"
    by (rule cont2contlubE[OF perm_cont, OF lookup_chain[OF `chain Y`]])
  also have "... = (\<Squnion>i. \<pi> \<bullet> Y i f! x)"
    using `x2 \<in> fdom (Y 0)` chain_fdom(1)[OF `chain Y`] `x = _`
    apply (subst the_lookup_eqvt)
    apply auto
    done
  also have "... = (\<Squnion>i. \<pi> \<bullet> Y i) f! x"
    by (subst lookup_cont[OF `chain (\<lambda>i. \<pi> \<bullet> Y i)`], rule refl)
  finally
  have "\<pi> \<bullet> (\<Squnion> i. Y i) f! x = (\<Squnion> i. \<pi> \<bullet> Y i) f! x" .
  thus "\<pi> \<bullet> (\<Squnion> i. Y i) f! x \<sqsubseteq> (\<Squnion> i. \<pi> \<bullet> Y i) f! x" by auto
qed

subsubsection {* Equivariance lemmas *}

lemma finite_transfer[transfer_rule]: "(op = ===> op =) finite finite" 
  unfolding fun_rel_eq by (rule refl)

(* This seems to be required to work around a bug in the transfer package, which generates these with a "setrel op =" constraint. *)
lemma [transfer_rule]:
  "(op = ===> cr_fmap) (\<lambda>S. if finite S then \<lambda>x. if x \<in> S then Some \<bottom> else None else Map.empty) fmap_bottom"
  using fmap_bottom.transfer
  unfolding set_rel_eq.

lemma [transfer_rule]: "(cr_fmap ===> op = ===> cr_fmap)
 (\<lambda>m1 S. if finite S then \<lambda>x. if x \<in> S then Some \<bottom> else m1 x else Map.empty)
 fmap_extend"
  using fmap_extend.transfer
  unfolding set_rel_eq.

lemma [transfer_rule]: "(cr_fmap ===> op = ===> cr_fmap)
     (\<lambda>m1 S.
         if finite S
         then \<lambda>x. if x \<in> S then Some (case m1 x of None \<Rightarrow> \<bottom> | Some x \<Rightarrow> x) else None
         else Map.empty)
     fmap_expand"
  using fmap_expand.transfer
  unfolding set_rel_eq.

lemma fmap_bottom_eqvt:
  "finite S \<Longrightarrow> \<pi> \<bullet> (fmap_bottom S :: 'a::pt f\<rightharpoonup> 'b::{cont_pt,pcpo}) = fmap_bottom (\<pi> \<bullet> S)"
  by (transfer,perm_simp, rule refl)

lemma fmap_extend_eqvt[eqvt]:
  "\<pi> \<bullet> fmap_extend (m :: 'a::{pt} f\<rightharpoonup> 'b::{cont_pt,pcpo}) S = fmap_extend (\<pi> \<bullet> m) (\<pi> \<bullet> S)"
  by (transfer, perm_simp, rule refl)

lemma fmap_expand_eqvt[eqvt]:
  "\<pi> \<bullet> fmap_expand (m :: 'a::{pt} f\<rightharpoonup> 'b::{cont_pt,pcpo}) S = fmap_expand (\<pi> \<bullet> m) (\<pi> \<bullet> S)"
  by (transfer, perm_simp, rule refl)

subsubsection {* Freshness of @{term fmap_bottom} *}

lemma fresh_fmap_bottom_set[simp]:
  assumes "x \<sharp> d"
  shows "x \<sharp> (fmap_bottom (set d) :: 'a::pt f\<rightharpoonup> 'b::{pcpo,cont_pt})"
  apply (rule eqvt_fresh_cong1[OF _ assms])
  by (simp add: fmap_bottom_eqvt set_eqvt)

lemma fresh_star_fmap_bottom_set[simp]:
  "x \<sharp>* d \<Longrightarrow> x \<sharp>* (fmap_bottom (set d) :: 'a::pt f\<rightharpoonup> 'b::{pcpo,cont_pt})"
  by (metis fresh_star_def fresh_fmap_bottom_set)

end

