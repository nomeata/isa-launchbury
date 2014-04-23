theory "Arity-Nominal"
imports Arity Nominal2
begin

instantiation Arity :: pure
begin
  definition "p \<bullet> (a::Arity) = a"
instance
  apply default
  apply (auto simp add: permute_Arity_def)
  done
end

end
