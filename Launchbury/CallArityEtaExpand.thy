theory CallArityEtaExpand
imports CoCallAnalysisImpl AbstractTransform EtaExpansionArity
begin

(* TODO: Import a general locale instead of the concrete implementation *)

(* TODO: Mark as one-shot *)

  interpretation AbstractTransformBound
    "\<lambda> a . inc\<cdot>a"
    "\<lambda> a . pred\<cdot>a"
    "\<lambda> \<Delta> e a . (a, combined_restrict (domA \<Delta>) (ccFix \<Delta>\<cdot>(cccExp e\<cdot>a)))"
    "\<lambda> b . fst b"
    "\<lambda> b . fst (snd b)"
    "Aeta_expand"
  apply default
  apply (((rule eq_reflection)?, perm_simp, rule)+)[6]
  done

  interpretation AbstractTransformBoundSubst
    "\<lambda> a . inc\<cdot>a"
    "\<lambda> a . pred\<cdot>a"
    "\<lambda> \<Delta> e a . (a, ccFix \<Delta>\<cdot>(cccExp e\<cdot>a))"
    "\<lambda> b . fst b"
    "\<lambda> b . fst (snd b)"
    "Aeta_expand"
  apply default
  sorry
  (*
  apply (simp add: Afix_subst  Aheap_cong[OF Aexp_subst_restr])[1]
  apply (rule subst_Aeta_expand)  
  done
  *)

  abbreviation Atransform where "Atransform \<equiv> transform"


end
