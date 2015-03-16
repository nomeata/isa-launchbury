session "HOLCF+Library" = HOLCF +
  options [document = false]
  theories
    "~~/src/HOL/Library/Quotient_Option"
    "~~/src/HOL/Library/AList"
    "~~/src/HOL/Library/FuncSet"
    "~~/src/HOL/Library/Permutation"
    "~~/src/HOL/Library/LaTeXsugar"
    "~~/src/HOL/Library/Infinite_Set"

session "HOLCF-Nominal2" in "Nominal2-Devel" = "HOLCF+Library" +
  options [document = false]
  theories
    "Nominal2"
    "Atoms"
    "Eqvt"

session Arity (AFP) in "Call_Arity" = "HOLCF-Nominal2" +
  options [document_variants = arity, document = pdf, document_graph, document_output = "output" ]
  theories
    "ArityAnalysisImplCorrect"
    "TrivialArityAnal"
    "ArityTransformSafe"
    "CardArityTransformSafe"
    "EtaExpansionSestoft"
    "DeadCodeRemovalCorrect"
    "DeadCodeRemoval2Correct"
    "DeadCodeRemoval2CorrectSestoft"
    "RedsImprovesArityAnalysis"
    "NoCardinalityAnalysis"
    "CallArityEnd2EndSafe"
    "ArityAnalysisCorrDenotational"
