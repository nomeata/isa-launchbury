theory CValue
imports  C
begin

domain CValue' = CFn (lazy "(C \<rightarrow> CValue') \<rightarrow> (C \<rightarrow> CValue')")
type_synonym CValue = "C \<rightarrow> CValue'"

fixrec CFn_project :: "CValue' \<rightarrow> CValue \<rightarrow> CValue"
 where "CFn_project\<cdot>(CFn\<cdot>f)\<cdot>v = f \<cdot> v"

abbreviation CFn_project_abbr (infix "\<down>CFn" 55)
  where "f \<down>CFn v \<equiv> CFn_project\<cdot>f\<cdot>v"

lemma CFn_project_strict[simp]:
  "\<bottom> \<down>CFn v = \<bottom>"
  by (fixrec_simp) 

instantiation CValue' :: pure
begin
  definition "p \<bullet> (v::CValue') = v"
instance
  apply default
  apply (auto simp add: permute_CValue'_def)
  done
end

instance CValue' :: pcpo_pt
  by default (simp add: pure_permute_id)

end
