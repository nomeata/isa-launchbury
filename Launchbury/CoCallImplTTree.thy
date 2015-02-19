theory CoCallImplTTree
imports TTreeAnalysisSig "Env-Set-Cpo" CoCallAritySig "CoCallGraph-TTree"
begin

context CoCallArity
begin
  definition Fexp :: "exp \<Rightarrow> Arity \<rightarrow> var ftree"
    where "Fexp e = (\<Lambda> a. ccTTree (edom (Aexp e \<cdot>a)) (ccExp e\<cdot>a))"
  
  lemma Fexp_simp: "Fexp e\<cdot>a = ccTTree (edom (Aexp e \<cdot>a)) (ccExp e\<cdot>a)"
    unfolding Fexp_def
    by simp

  sublocale TTreeAnalysis Fexp.
end



end

