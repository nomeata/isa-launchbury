theory "CoCallGraph-Nominal"
imports CoCallGraph "Nominal-HOLCF"
begin

instantiation CoCalls :: pt
begin
  lift_definition permute_CoCalls :: "perm \<Rightarrow> CoCalls \<Rightarrow> CoCalls" is "permute"
    by (auto intro!: symI elim: symE simp add: mem_permute_set)
instance
  apply default
  apply (transfer, simp)+
  done
end

instance CoCalls :: cont_pt
  apply default
  apply (rule contI2)
  apply (rule monofunI)
  apply transfer
  apply (metis (full_types) True_eqvt subset_eqvt)
  apply (thin_tac "chain ?x")+
  apply transfer
  apply simp
  done

lemma cc_restr_perm:
  fixes G :: CoCalls
  assumes "supp p \<sharp>* S" and [simp]: "finite S"
  shows "cc_restr S (p \<bullet> G) = cc_restr S G"
  using assms
  apply -
  apply transfer
  apply (auto simp add: mem_permute_set)
  apply (subst (asm) perm_supp_eq, simp add: supp_minus_perm, metis (full_types) fresh_def fresh_star_def supp_set_elem_finite)+
  apply assumption
  apply (subst perm_supp_eq, simp add: supp_minus_perm, metis (full_types) fresh_def fresh_star_def supp_set_elem_finite)+
  apply assumption
  done

lemma inCC_eqvt[eqvt]: "\<pi> \<bullet> inCC = inCC" sorry
lemma cc_restr_eqvt[eqvt]: "\<pi> \<bullet> cc_restr = cc_restr" sorry
lemma ccSquare_eqvt[eqvt]: "\<pi> \<bullet> ccSquare = ccSquare" sorry
lemma ccProd_eqvt[eqvt]: "\<pi> \<bullet> ccProd = ccProd" sorry
lemma ccNeighbors_eqvt[eqvt]: "\<pi> \<bullet> ccNeighbors = ccNeighbors" sorry

end
