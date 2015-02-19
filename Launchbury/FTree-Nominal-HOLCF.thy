theory "TTree-Nominal-HOLCF"
imports "TTree-HOLCF" "Nominal-Utils" "Nominal-HOLCF"
begin

(* TODO: This ssems to be unused *)

instantiation ttree :: (pt) pt
begin
  lift_definition permute_ttree :: "perm \<Rightarrow> 'a ttree \<Rightarrow> 'a ttree" is "\<lambda> p xss. map (\<lambda> xs. permute p xs) ` xss"
    by (auto intro: downset_mapI)
  instance by default (transfer, simp add: image_comp)+
end

lemma paths_eqvt[eqvt]: "\<pi> \<bullet> (paths t) = paths (\<pi> \<bullet> t)"
  by transfer (simp add: map_permute permute_set_eq_image)

instance ttree :: (pt) cont_pt
proof default
  fix p
  show "cont (permute p :: 'a ttree \<Rightarrow> 'a ttree)"
    by (rule ttree_contI) (transfer, auto)
qed

end
