theory DenotationalEquivalences
imports "Denotational" "HSem-Equivalences"
begin

(* TODO: Replace this by a lemma showing that the equation for Let with update-based semantics 
  also holds for HSem (thus showing that either definition would be the equivalent)

lemma sharp_star_Env: "set (bn as) \<sharp>* (\<rho> :: (var f\<rightharpoonup> 'b::{pure_cpo})) \<longleftrightarrow> (\<forall> x \<in> heapVars (asToHeap as) . x \<notin> fdom \<rho>)"
  by(induct rule:asToHeap.induct, auto simp add: fresh_star_def exp_assn.bn_defs fresh_fmap_pure)


theorem HSem_join_update:
  "DenotationalUpd.ESem e \<rho> = Denotational.ESem e \<rho>" and "\<And> e. e \<in> snd ` set (asToHeap as) \<Longrightarrow> DenotationalUpd.ESem e \<rho> = Denotational.ESem e \<rho>"
proof(nominal_induct e and  avoiding: \<rho>  rule:exp_assn.strong_induct)
case (Let as e \<rho>)
  have "fdom \<rho> \<inter> heapVars (asToHeap as) = {}"
    by (metis Let(1) disjoint_iff_not_equal sharp_star_Env)
  hence "DenotationalUpd.UHSem (asToHeap as) \<rho> = Denotational.HSem (asToHeap as) \<rho>"
    by (rule heap_update_join[OF _ "Denotational-PropsUpd.ESem_cont" "Denotational.ESem_cont" Let(2)])
  thus ?case using Let(1,3) by simp
qed (auto dest!: set_mp[OF set_delete_subset])

*)

end
