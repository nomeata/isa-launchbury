theory "FMap-Nominal-HOLCF"
imports "Nominal-HOLCF" "FMap-Nominal" "FMap-HOLCF" "Nominal-Utils"
begin

instance "fmap" :: (cont_pt, cont_pt) cont_pt
apply default
proof(intro contI2 monofunI fmap_belowI')
  fix \<pi> m1 m2
  assume "m1 \<sqsubseteq> (m2 :: ('a, 'b) fmap)"
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

  have "the (lookup (\<pi> \<bullet> m1) x) = \<pi> \<bullet> the (lookup m1 x2)"
    by (simp add: the_lookup_eqvt[OF `x2 \<in> fdom m1`]  `x = _`)
  also have "... \<sqsubseteq> \<pi> \<bullet> the (lookup m2 x2)"
    by -(subst perm_cont_simp, rule fmap_belowE[OF `m1 \<sqsubseteq> m2`])
  also have "... \<sqsubseteq> the (lookup (\<pi> \<bullet> m2) x)"
    using `x = _`
    by (simp add: the_lookup_eqvt[OF `x2 \<in> fdom m2`]  )
  finally show "the (lookup (\<pi> \<bullet> m1) x) \<sqsubseteq> the (lookup (\<pi> \<bullet> m2) x)".

next
  fix \<pi> Y
  assume "chain (Y\<Colon>nat \<Rightarrow> ('a, 'b) fmap)"
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
    
  have "the (lookup (\<pi> \<bullet> (\<Squnion> i. Y i)) x) = \<pi> \<bullet> (the (lookup (\<Squnion> i. Y i) x2))"
    by (simp add: the_lookup_eqvt[OF `x2 \<in> fdom (\<Squnion> i. Y i)`]  `x = _`)
  also have "... = \<pi> \<bullet> (\<Squnion>i. (the (lookup (Y i) x2)))"
    by (subst lookup_cont[OF `chain Y`], rule refl)
  also have "... = (\<Squnion>i. \<pi> \<bullet> (the (lookup (Y i) x2)))"
    by (rule cont2contlubE[OF perm_cont, OF lookup_chain[OF `chain Y`]])
  also have "... = (\<Squnion>i. the (lookup (\<pi> \<bullet> (Y i)) x))"
    using `x2 \<in> fdom (Y 0)` chain_fdom(1)[OF `chain Y`] `x = _`
    apply (subst the_lookup_eqvt)
    apply auto
    done
  also have "... = the (lookup (\<Squnion>i. \<pi> \<bullet> (Y i)) x)"
    by (subst lookup_cont[OF `chain (\<lambda>i. \<pi> \<bullet> Y i)`], rule refl)
  finally
  have "the (lookup (\<pi> \<bullet> (\<Squnion> i. Y i)) x) = the (lookup (\<Squnion> i. \<pi> \<bullet> Y i) x)" .
  thus "the (lookup (\<pi> \<bullet> (\<Squnion> i. Y i)) x) \<sqsubseteq> the (lookup (\<Squnion> i. \<pi> \<bullet> Y i) x)" by auto
qed

lemma fix1_eqvt[simp,eqvt]:
  "\<pi> \<bullet> fix1 x f = fix1 (\<pi> \<bullet> x) (\<pi> \<bullet> f)"
proof(cases "x \<sqsubseteq> f \<cdot> x")
  case True thus ?thesis
  by -(rule parallel_fix1_ind, auto dest:cont2monofunE[OF perm_cont] simp add: Cfun_app_eqvt)
next
  case False thus ?thesis
  unfolding fix1_def
  apply (subst if_not_P, assumption)
  apply (subst if_not_P)
  apply (metis if_not_P Cfun_app_eqvt perm_cont_simp)
  apply rule
  done
qed  

lemma finite_transfer[transfer_rule]: "(op = ===> op =) finite finite" 
  unfolding fun_rel_eq by (rule refl)

lemma fmap_bottom_eqvt:
  "finite S \<Longrightarrow> \<pi> \<bullet> (fmap_bottom S :: ('a::pt, 'b::{cont_pt,pcpo}) fmap) = fmap_bottom (\<pi> \<bullet> S)"
  by (transfer, perm_simp, rule refl)

lemma fmap_update_eqvt[eqvt]:
  "\<pi> \<bullet> fmap_update m1 (m2 :: ('a::{cont_pt,cpo}, 'b::{cont_pt,cpo}) fmap) = fmap_update (\<pi> \<bullet> m1) (\<pi> \<bullet> m2)"
  by (transfer, perm_simp, rule refl)

end

