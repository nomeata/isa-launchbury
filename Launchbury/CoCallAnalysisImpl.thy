theory CoCallAnalysisImpl
imports CoCallFix "Arity-Nominal" "Nominal-HOLCF" "Env-Nominal" "Env-HOLCF"
begin

nominal_function
  Aexp :: "exp \<Rightarrow> (Arity \<rightarrow> AEnv)" and ccExp :: "exp \<Rightarrow> (Arity \<rightarrow> CoCalls)" 
where
  "Aexp (GVar b x) = (\<Lambda> n . AE_singleton x \<cdot> (up \<cdot> n))"
| "Aexp (Lam [x]. e) = (\<Lambda> n . (Aexp e \<cdot> (pred \<cdot> n)  f|` (fv (Lam [x]. e))))"
| "Aexp (App e x) = (\<Lambda> n . Aexp e  \<cdot> (inc \<cdot> n) \<squnion> (AE_singleton x \<cdot> (up \<cdot> 0)))"
| "Aexp (Terms.Let as e) = (\<Lambda> n . fst (CoCallArityAnalysis.ccFix  ccExp Aexp as \<cdot> (Aexp e \<cdot> n, cExp e \<cdot> n)) f|` (fv (Terms.Let as e)))"

| "ccExp (GVar b x) = (\<Lambda> n . \<bottom>)"
| "ccExp (Lam [x]. e) = (\<Lambda> n . \<bottom>)"
| "ccExp (App e x) = (\<Lambda> n . \<bottom>)"
| "ccExp (Terms.Let as e) = (\<Lambda> n . \<bottom>)"



end

