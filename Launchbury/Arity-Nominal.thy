theory "Arity-Nominal"
imports Arity "Nominal-HOLCF"
begin

instantiation Arity :: pure
begin
  definition "p \<bullet> (a::Arity) = a"
instance
  apply default
  apply (auto simp add: permute_Arity_def)
  done
end


instance Arity :: cont_pt by default (simp add: pure_permute_id)
instance Arity :: pure_cont_pt by default

end
