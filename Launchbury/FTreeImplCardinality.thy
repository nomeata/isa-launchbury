theory FTreeImplCardinality
imports FTreeAnalysisSig CardinalityAnalysisSig CallFutureCardinality
begin

hide_const Multiset.single

context FTreeAnalysis
begin

fun unstack :: "stack \<Rightarrow> exp \<Rightarrow> exp" where
  "unstack [] e = e"
| "unstack (Alts e1 e2 # S) e = unstack S e"
| "unstack (Upd x # S) e = unstack S e"
| "unstack (Arg x # S) e = unstack S (App e x)"
| "unstack (Dummy x # S) e = unstack S e"

fun Fstack :: "stack \<Rightarrow> var ftree"
  where "Fstack [] = \<bottom>"
  | "Fstack (Alts e1 e2 # S) = Fstack S"
  | "Fstack (Upd x # S) = Fstack S"
  | "Fstack (Arg x # S) = many_calls x \<otimes>\<otimes> Fstack S"
  | "Fstack (Dummy x # S) = Fstack S"

lemma carrier_Fstack[simp]: "carrier (Fstack S) = ap S"
  by (induction S rule: Fstack.induct) (auto simp add: empty_is_bottom[symmetric])

fun prognosis :: "AEnv \<Rightarrow> Arity \<Rightarrow> conf \<Rightarrow> var \<Rightarrow> two"
   where "prognosis ae a (\<Gamma>, e, S) = pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Fexp e\<cdot>a \<otimes>\<otimes> Fstack S)))"
end

end
