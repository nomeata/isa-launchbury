theory "Value"
  imports Vars "Nominal-Utils" "Nominal-HOLCF"
begin

default_sort cpo

subsubsection {* The semantic domain for values and environments *}

domain Value = Fn (lazy "Value \<rightarrow> Value")

fixrec Fn_project :: "Value \<rightarrow> Value \<rightarrow> Value"
 where "Fn_project\<cdot>(Fn\<cdot>f) = f"

abbreviation Fn_project_abbr (infix "\<down>Fn" 55)
  where "f \<down>Fn v \<equiv> Fn_project\<cdot>f\<cdot>v"


type_synonym Env = "var \<Rightarrow> Value"

instantiation Value :: pure
begin
  definition "p \<bullet> (v::Value) = v"
instance
  apply default
  apply (auto simp add: permute_Value_def)
  done
end

instance Value :: pcpo_pt
  by default (simp add: pure_permute_id)

end
