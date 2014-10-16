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

session Launchbury (AFP) in "Launchbury" = "HOLCF-Nominal2" +
  options [document = pdf, document_graph, document_output = "output"]
  theories
    "Everything"

session LaunchburyAdequacy (AFP) in "Launchbury" = "HOLCF-Nominal2" +
  options [document_variants = adequacy, document = pdf, document_graph, document_output = "output" ]
  theories
    "EverythingAdequacy"

session LaunchburyComplete (AFP) in "Launchbury" = "HOLCF-Nominal2" +
  options [document_variants = newstuff, document = pdf, document_graph, document_output = "output", quick_and_dirty]
  theories
    "NewStuff"

session Arity (AFP) in "Launchbury" = "HOLCF-Nominal2" +
  options [document_variants = arity, document = pdf, document_graph, document_output = "output" ]
  theories
    "ArityCorrect2"
    "ArityAnalysisImpl"
    "TrivialArityAnal"
    "ArityEtaExpand"
    "ArityEtaExpandInst"
    "EtaExpansionSestoft"
    "DeadCodeRemovalCorrect"
    "DeadCodeRemoval2Correct"
    "DeadCodeRemoval2CorrectSestoft"

session Nominal2013_1 in "Nominal2-Isabelle2013-1/Nominal" = HOL +
  theories
    "Nominal2"

session Nominal2013_1_Orig in "Nominal2-Isabelle2013-1.orig/Nominal" = HOL +
  theories
    "Nominal2"

session Nominal_Deve in "Nominal-Devel" = HOL +
  theories
    "Nominal2"

session LocaleBug = Nominal2013_1 +
  options [quick_and_dirty]
  theories
    "LocaleBug"

session LocaleBug_Orig = Nominal2013_1_Orig +
  options [quick_and_dirty]
  theories
    "LocaleBug"

session LocaleBug_Devel = Nominal2013_1_Orig +
  options [quick_and_dirty]
  theories
    "LocaleBug"
