theory HasESem
imports "Nominal-HOLCF" "FMap-HOLCF" "HOLCF-Join"
begin

locale has_ESem =
  fixes ESem :: "'exp::pt \<Rightarrow> 'var::{cont_pt,at_base} f\<rightharpoonup> 'value \<Rightarrow> 'value::{pure_cpo,Nonempty_Meet_cpo,pcpo}"  ("\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60)

locale has_cont_ESem = has_ESem +
  assumes ESem_cont: "\<And> e. cont (ESem e)"

end
