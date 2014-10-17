theory "CoCallGraph-Nominal"
imports CoCallGraph "Nominal-HOLCF"
begin

instantiation CoCalls :: pt
begin
  lift_definition permute_CoCalls :: "perm \<Rightarrow> CoCalls \<Rightarrow> CoCalls" is "permute".
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

end
