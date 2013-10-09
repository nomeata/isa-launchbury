theory DenotationalEquivalences
imports "Denotational-PropsUpd" "Denotational-Props" "HSem-Equivalences"
begin

theorem HSem_join_update:
  "DenotationalUpd.ESem e \<rho> = Denotational.ESem e \<rho>" and "\<And> e. e \<in> snd ` set (asToHeap as) \<Longrightarrow> DenotationalUpd.ESem e \<rho> = Denotational.ESem e \<rho>"
proof(nominal_induct e and  avoiding: \<rho>  rule:exp_assn.strong_induct)
case (Let as e \<rho>)
  have "fdom \<rho> \<inter> heapVars (asToHeap as) = {}"
    by (metis Let(1) disjoint_iff_not_equal sharp_star_Env)
  hence "DenotationalUpd.HSem (asToHeap as) \<rho> = Denotational.HSem (asToHeap as) \<rho>"
    by (rule heap_update_join[OF _ "Denotational-PropsUpd.ESem_cont" "Denotational-Props.ESem_cont" Let(2)])
  thus ?case using Let(1,3) by simp
qed (auto dest!: set_mp[OF set_delete_subset])

end
