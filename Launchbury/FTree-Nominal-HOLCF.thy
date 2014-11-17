theory "FTree-Nominal-HOLCF"
imports "FTree-HOLCF" "Nominal-Utils" "Nominal-HOLCF"
begin

instantiation ftree :: (pt) pt
begin
  lift_definition permute_ftree :: "perm \<Rightarrow> 'a ftree \<Rightarrow> 'a ftree" is "\<lambda> p xss. map (\<lambda> xs. permute p xs) ` xss"
    by (auto intro: downset_mapI)
  instance by default (transfer, simp add: image_comp)+
end

lemma paths_eqvt[eqvt]: "\<pi> \<bullet> (paths t) = paths (\<pi> \<bullet> t)"
  by transfer (simp add: map_permute permute_set_eq_image)

instance ftree :: (pt) cont_pt
proof default
  fix p
  show "cont (permute p :: 'a ftree \<Rightarrow> 'a ftree)"
    by (rule ftree_contI) (transfer, auto)
qed

instance lift :: (pt) pcpo_pt by default

end
