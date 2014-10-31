theory Set_Cpo_Nominal
imports Set_Cpo "Nominal-HOLCF"
begin

instance set :: (pt) cont_pt
  apply default
  apply (rule set_contI)
  apply perm_simp
  apply (simp add : permute_set_eq_image)
  done
end
