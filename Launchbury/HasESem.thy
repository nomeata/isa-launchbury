theory HasESem
imports "Nominal-HOLCF" "Env-HOLCF"
begin

locale has_ESem =
  fixes ESem :: "'exp::pt \<Rightarrow> ('var::{cont_pt,at_base} \<Rightarrow> 'value) \<rightarrow> 'value::{pure,pcpo}" 
begin
  abbreviation ESem_syn ("\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>"  [60,60] 60) where "\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub> \<equiv> ESem e \<cdot> \<rho>"
end

locale has_ignore_fresh_ESem = has_ESem +
  assumes fv_supp: "supp e = atom ` (fv e :: 'b set)"
  assumes ESem_considers_fv: "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho> f|` (fv e)\<^esub>"

end
