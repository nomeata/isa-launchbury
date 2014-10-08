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

lift_definition inCC :: "var \<Rightarrow> var \<Rightarrow> CoCalls \<Rightarrow> bool" ("_--_\<in>_")
  is "\<lambda> x y s. (x,y) \<in> s".

abbreviation notInCC :: "var \<Rightarrow> var \<Rightarrow> CoCalls \<Rightarrow> bool" ("_--_\<notin>_")
  where "x--y\<notin>S \<equiv> \<not> (x--y\<in>S)"

end
