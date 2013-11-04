theory "FMap-Utils"
imports "FMap-Nominal-HOLCF"  "DistinctVars"
begin

default_sort type

text {* Lemmas relating @{theory FMap} to the other auxillary theories. *}

lemma sharp_star_Env': "atom ` heapVars \<Gamma> \<sharp>* (\<rho> :: 'var::{cont_pt,at_base} f\<rightharpoonup> 'value::{pure_cpo,pcpo}) \<longleftrightarrow> heapVars \<Gamma> \<inter> fdom \<rho> = {}"
  by(induct \<Gamma>, auto simp add: fresh_star_def fresh_fmap_pure)
end
