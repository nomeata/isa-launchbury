theory TTreeAnalysisSig
imports Arity  "TTree-HOLCF"  AnalBinds
begin

locale TTreeAnalysis =
 fixes Fexp :: "exp \<Rightarrow> Arity \<rightarrow> var ftree"
begin
  sublocale Fexp!: ExpAnalysis Fexp.
  abbreviation "FBinds == Fexp.AnalBinds"
end

end
