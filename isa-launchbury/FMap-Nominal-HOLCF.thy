theory "FMap-Nominal-HOLCF"
imports "Nominal-HOLCF" "FMap-Nominal" "FMap-HOLCF" "Nominal-Utils"
begin

instance "fmap" :: (pt, cont_pt) cont_pt
apply default
proof(intro contI2 monofunI fmap_belowI')
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

(*
lemma fix1_eqvt[simp,eqvt]:
  "\<pi> \<bullet> fix1 x f = fix1 (\<pi> \<bullet> x) (\<pi> \<bullet> f)"
proof(cases "x \<sqsubseteq> f \<cdot> x")
  case True thus ?thesis
  apply -
  using [[show_types]] [[show_sorts]]
  apply (rule parallel_fix1_ind)
  apply auto[1]
  by -(rule parallel_fix1_ind, auto dest:cont2monofunE[OF perm_cont] simp add: Cfun_app_eqvt)
next
  case False thus ?thesis
  unfolding fix1_def
  apply (subst if_not_P, assumption)
  apply (subst if_not_P)
  apply (metis Cfun_app_eqvt perm_cont_simp)
  apply rule
  done
qed
*)

lemma chain_shift_funpow[simp]: 
  "chain (\<lambda>i. (f ^^ i) x) \<Longrightarrow> chain (\<lambda>i. f ((f ^^ i) x))"
proof-
  have tmp: "\<And> i. f ((f ^^ i) x) = (f ^^ (Suc i)) x"
    by (metis funpow.simps(2) o_apply)
  show "chain (\<lambda>i. (f ^^ i) x) \<Longrightarrow> chain (\<lambda>i. f ((f ^^ i) x))"
    apply (subst tmp)
    by (rule chain_shift[of _ 1, simplified])
qed

(*
lemma chainFrom_eqvt[simp,eqvt]:
  "chainFrom f (x :: 'a :: cont_pt) \<Longrightarrow> chainFrom (\<pi> \<bullet> f) (\<pi> \<bullet> x)"
  unfolding chainFrom_def
  apply (auto simp only:funpow_eqvt[symmetric, simplified permute_pure] permute_fun_app_eq[symmetric] perm_cont_simp)
  apply (subst Lub_eqvt[symmetric])
  apply (rule cpo, rule chainI, auto)[1]
  apply (subst Lub_eqvt[symmetric])
  apply (rule cpo, rule chain_shift_funpow, rule chainI, auto)[1]
  apply (auto simp only:funpow_eqvt[symmetric, simplified permute_pure] permute_fun_app_eq[symmetric] perm_cont_simp)
  done  

lemma fixR_eqvt[simp,eqvt]:
  "\<pi> \<bullet> fixR (x::'a::cont_pt) f = fixR (\<pi> \<bullet> x) (\<pi> \<bullet> f)"
proof(cases "chainFrom f x")
  case True thus ?thesis
  apply -
  apply (rule parallel_fixR_ind)
  apply auto[1]
  apply assumption
  apply (erule chainFrom_eqvt)
  apply rule
  apply (simp add: permute_fun_app_eq)
  done
next
  case False thus ?thesis
  unfolding fixR_def
  apply (subst if_not_P, assumption)
  apply (subst if_not_P)
  apply (metis chainFrom_eqvt permute_minus_cancel(2))
  apply rule
  done
qed  
*)

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

lemma fmap_add_eqvt[eqvt]:
  "\<pi> \<bullet> fmap_add m1 (m2 :: 'a::{cont_pt,cpo} f\<rightharpoonup> 'b::{cont_pt,cpo}) = fmap_add (\<pi> \<bullet> m1) (\<pi> \<bullet> m2)"
  by (transfer, perm_simp, rule refl)

lemma fmap_extend_eqvt[eqvt]:
  "\<pi> \<bullet> fmap_extend (m :: 'a::{pt} f\<rightharpoonup> 'b::{cont_pt,pcpo}) S = fmap_extend (\<pi> \<bullet> m) (\<pi> \<bullet> S)"
  by (transfer, perm_simp, rule refl)

lemma fmap_expand_eqvt[eqvt]:
  "\<pi> \<bullet> fmap_expand (m :: 'a::{pt} f\<rightharpoonup> 'b::{cont_pt,pcpo}) S = fmap_expand (\<pi> \<bullet> m) (\<pi> \<bullet> S)"
  by (transfer, perm_simp, rule refl)

lemma compatible_eqvt[eqvt]:
  "compatible (x::'a::cont_pt) y \<Longrightarrow> compatible (\<pi> \<bullet> x) (\<pi> \<bullet> y)"
  unfolding compatible_def
  by (metis empty_eqvt insert_eqvt perm_is_lub_simp)

lemma permute_under_all:
  "(\<forall> x . P (\<pi> \<bullet> x)) \<Longrightarrow> (\<forall> x. P x)"
  by (metis eqvt_bound)

lemma permute_under_ball:
  "(\<forall> x \<in> (- \<pi> \<bullet> S). P (\<pi> \<bullet> x)) \<Longrightarrow> (\<forall> x \<in> S . P x)"
  by (metis mem_eqvt permute_minus_cancel(1) permute_pure) 

lemma compatible_fmap_eqvt[eqvt]:
  "compatible_fmap m1 (m2 :: 'a::pt f\<rightharpoonup> 'b::{cont_pt,pcpo}) \<Longrightarrow> compatible_fmap (\<pi> \<bullet> m1) (\<pi> \<bullet> m2)"
  unfolding compatible_fmap_def'
  apply (rule permute_under_ball[of \<pi>])
  apply rule
  apply (simp add: inter_eqvt)
  apply (erule_tac x = z in ballE)
  apply (simp only: the_lookup_eqvt[symmetric] compatible_eqvt)
  apply auto
  done

lemma join_eqvt[simp,eqvt]:
  "\<pi> \<bullet> join (x::'a::{cont_pt}) y = join (\<pi> \<bullet> x) (\<pi> \<bullet> y)"
proof (cases "\<exists> z. {x, y} <<| z")
case False
  hence "\<not> (\<exists> z. {\<pi> \<bullet> x, \<pi> \<bullet> y} <<| z)" by (metis perm_is_lub_simp empty_eqvt insert_eqvt eqvt_bound)
  thus ?thesis using False unfolding join_def by auto
next
case True
  hence "\<exists> z. {\<pi> \<bullet> x, \<pi> \<bullet> y} <<| z" by (metis perm_is_lub_simp empty_eqvt insert_eqvt)
  thus ?thesis using True unfolding join_def by (auto simp add: empty_eqvt insert_eqvt)
qed

lemma fmap_join_eqvt[eqvt]:
  "\<pi> \<bullet> fmap_join m1 (m2 :: 'a::{pt} f\<rightharpoonup> 'b::{cont_pt, pcpo}) = fmap_join (\<pi> \<bullet> m1) (\<pi> \<bullet> m2)"
  by (transfer, perm_simp, rule refl)


lemma below_eqvt [eqvt]:
    "\<pi> \<bullet> (x \<sqsubseteq> y) = (\<pi> \<bullet> x \<sqsubseteq> \<pi> \<bullet> (y::'a::cont_pt))" by (auto simp add: permute_pure)

definition fmap_bottom_l where
  "fmap_bottom_l d = fmap_bottom (set d)"

lemma fmap_bottom_l_eqvt[eqvt]:
  "\<pi> \<bullet> fmap_bottom_l d = (fmap_bottom_l (\<pi> \<bullet> d) :: 'a::pt f\<rightharpoonup> 'b::{pcpo,cont_pt})"
  by (simp add: fmap_bottom_l_def fmap_bottom_eqvt set_eqvt)

lemma fresh_fmap_bottom_set[simp]:
  "x \<sharp> d \<Longrightarrow> x \<sharp> (fmap_bottom (set d) :: 'a::pt f\<rightharpoonup> 'b::{pcpo,cont_pt})"
  unfolding fmap_bottom_l_def[symmetric]
  apply (erule fresh_fun_eqvt_app[rotated])
  apply (rule eqvtI)
  apply (rule eq_reflection)
  by (metis fmap_bottom_l_eqvt permute_fun_def permute_minus_cancel(1))

lemma fresh_star_fmap_bottom_set[simp]:
  "x \<sharp>* d \<Longrightarrow> x \<sharp>* (fmap_bottom (set d) :: 'a::pt f\<rightharpoonup> 'b::{pcpo,cont_pt})"
  by (metis fresh_star_def fresh_fmap_bottom_set)


end

