theory AbstractCorrectness
imports Main
begin

locale AbstractCorrectness =
  fixes rel :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<Rightarrow>" 50)
  fixes trans :: "'s \<Rightarrow> 'a \<Rightarrow> 'a" 
  fixes conf :: "'a \<Rightarrow> 's \<Rightarrow> bool" (infix "\<triangleright>" 50)
  fixes update :: "'a \<Rightarrow> 's \<Rightarrow> 's"

end
