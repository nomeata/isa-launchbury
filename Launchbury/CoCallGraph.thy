theory CoCallGraph
imports Main Vars HOLCF
begin

typedef CoCalls = "UNIV :: (var \<times> var) set set"
  morphisms Rep_CoCall Abs_CoCall
  by auto

setup_lifting type_definition_CoCalls

instantiation CoCalls :: po
begin
lift_definition below_CoCalls :: "CoCalls \<Rightarrow> CoCalls \<Rightarrow> bool" is "op \<subseteq>".
instance
  apply default
  apply ((transfer, auto)+)
  done
end

instance CoCalls :: cpo
  sorry


lift_definition ccField :: "CoCalls \<Rightarrow> var set" is Field.

end
