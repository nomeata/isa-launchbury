theory "Set-Cpo-Nominal"
imports "Set-Cpo" "Nominal-HOLCF"
begin

instance set :: (pt) cont_pt
  apply default
  apply (rule set_contI)
  apply perm_simp
  apply (simp add : permute_set_eq_image)
  done
end
