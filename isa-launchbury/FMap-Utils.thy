theory "FMap-Utils"
imports "FMap-Nominal-HOLCF" "HOLCF-Fix-Join-Nominal"
begin

text {* Lemmas relating @{theory FMap} to the other auxillary theories. *}

lemma fdom_fix_join_compat:
  assumes "fix_on_cond S (bottom_of S) (\<lambda>\<rho>'. \<rho> \<squnion> F \<rho>')"
  assumes "\<rho>' \<in> fix_join_compat \<rho> F"
  shows "fdom \<rho>' = fdom \<rho>"
  by (metis assms(2) bottom_of_fjc fmap_below_dom subpcpo.bottom_of_minimal subpcpo_fjc to_bot_minimal)
end
