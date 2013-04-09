theory "FMap-Utils"
imports "FMap-Nominal-HOLCF" "HOLCF-Fix-Join-Nominal" "DistinctVars"
begin

default_sort type

text {* Lemmas relating @{theory FMap} to the other auxillary theories. *}

lemma fdom_fix_join_compat:
  assumes "fix_on_cond S (bottom_of S) (\<lambda>\<rho>'. \<rho> \<squnion> F \<rho>')"
  assumes "\<rho>' \<in> fix_join_compat \<rho> F"
  shows "fdom \<rho>' = fdom \<rho>"
  by (metis assms(2) bottom_of_fjc fmap_below_dom subpcpo.bottom_of_minimal subpcpo_fjc to_bot_minimal)

lemma fmap_empty_join[simp]: "fdom f = S \<Longrightarrow> f\<emptyset>\<^bsub>[S]\<^esub> \<squnion> f = f"
  by (metis fmap_bottom_below larger_is_join2)

lemma bottom_of_fdom[simp]: "finite S \<Longrightarrow> bottom_of {y. fdom y = S} = f\<emptyset>\<^bsub>[S]\<^esub>"
  using bottom_of_cone_above[where x = "f\<emptyset>\<^bsub>[S]\<^esub>"]
  by simp

lemma sharp_star_Env': "atom ` heapVars \<Gamma> \<sharp>* (\<rho> :: 'var::{cont_pt,at_base} f\<rightharpoonup> 'value::{pure_cpo,Nonempty_Meet_cpo,pcpo}) \<longleftrightarrow> heapVars \<Gamma> \<inter> fdom \<rho> = {}"
  by(induct \<Gamma>, auto simp add: fresh_star_def sharp_Env)
end
