theory FTreeAnalysisSig
imports Arity  "FTree-HOLCF"  AnalBinds
begin

locale FTreeAnalysis =
 fixes Fexp :: "exp \<Rightarrow> Arity \<rightarrow> var ftree"
begin
  sublocale Fexp!: ExpAnalysis Fexp.
  abbreviation "FBinds == Fexp.AnalBinds"
end

end
