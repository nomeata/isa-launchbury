theory ArityAnalysisSig
imports Terms AEnv "Arity-Nominal" "Nominal-HOLCF"  "Substitution"
begin

locale ArityAnalysis =
  fixes Aexp :: "exp \<Rightarrow> Arity \<rightarrow> AEnv"

end
