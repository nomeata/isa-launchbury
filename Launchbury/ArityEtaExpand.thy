theory ArityEtaExpand
imports ArityAnalysisSig AbstractTransform ArityEtaExpansionSestoft
begin

context ArityAnalysisHeapEqvt
begin
  sublocale AbstractTransformBound
    "\<lambda> a . inc\<cdot>a"
    "\<lambda> a . pred\<cdot>a"
    "\<lambda> \<Delta> e a . (a, Aheap \<Delta> e\<cdot>a)"
    "fst"
    "snd"
    "\<lambda> _. 0"
    "Aeta_expand"
    "snd"
  apply default
  apply (((rule eq_reflection)?, perm_simp, rule)+)
  done
end


end
