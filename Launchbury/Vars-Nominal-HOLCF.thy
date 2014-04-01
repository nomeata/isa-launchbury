theory "Vars-Nominal-HOLCF"  imports Vars "Nominal-HOLCF"
begin

subsubsection {* Variables are discretely ordered *}

instantiation var :: discrete_cpo
begin
  definition  [simp]: "(x::var) \<sqsubseteq> y \<longleftrightarrow> x = y"
  instance by default simp
end

instance var :: cont_pt  by default auto

end
