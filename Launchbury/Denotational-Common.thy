theory "Denotational-Common"
  imports Terms Heap "Nominal-Utils" "FMap-Nominal-HOLCF"
begin

default_sort cpo

subsubsection {* Variables are discretely ordered *}

instantiation var :: discrete_cpo
begin
  definition  [simp]: "(x::var) \<sqsubseteq> y \<longleftrightarrow> x = y"
  instance by default simp
end

instance var :: cont_pt  by default auto

subsubsection {* The semantic domain for values and environments *}

domain Value = Fn (lazy "Value \<rightarrow> Value")

fixrec Fn_project :: "Value \<rightarrow> Value \<rightarrow> Value"
 where "Fn_project\<cdot>(Fn\<cdot>f) = f"

abbreviation Fn_project_abbr (infix "\<down>Fn" 55)
  where "f \<down>Fn v \<equiv> Fn_project\<cdot>f\<cdot>v"


type_synonym Env = "var f\<rightharpoonup> Value"

instantiation Value :: pure_cpo
begin
  definition "p \<bullet> (v::Value) = v"
instance
  apply default
  apply (auto simp add: permute_Value_def)
  done
end

end
