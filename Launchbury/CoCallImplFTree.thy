theory CoCallImplFTree
imports FTreeAnalysisSpec CoCallAritySig "CoCallGraph-FTree"
begin

context CoCallArity
begin
  definition Fexp :: "exp \<Rightarrow> Arity \<rightarrow> var ftree"
    where "Fexp e = (\<Lambda> a. ccFTree (edom (Aexp e \<cdot>a)) (ccExp e\<cdot>a))"
  
  lemma Fexp_simp: "Fexp e\<cdot>a = ccFTree (edom (Aexp e \<cdot>a)) (ccExp e\<cdot>a)"
    unfolding Fexp_def by simp

  sublocale FTreeAnalysis Fexp.
end



end

