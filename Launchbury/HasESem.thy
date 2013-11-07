theory HasESem
imports "Nominal-HOLCF" "Env-HOLCF" "HOLCF-Join"
begin

locale has_ESem =
  fixes ESem :: "'exp::pt \<Rightarrow> 'var::{cont_pt,at_base} f\<rightharpoonup> 'value \<rightarrow> 'value::{pure_cpo,Nonempty_Meet_cpo,pcpo}" 
begin
  abbreviation ESem_syn ("\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60) where "\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub> \<equiv> ESem e \<cdot> \<rho>"
end

end
