session "HOLCF-Nominal2" in "Nominal2-Isabelle2013-1/Nominal" = HOLCF +
  options [document = false]
  theories
    "Nominal2"
    "Atoms"
    "Eqvt"
    "~~/src/HOL/Library/Quotient_Option"
    "~~/src/HOL/Library/AList"
    "~~/src/HOL/Library/FuncSet"
    "~~/src/HOL/Library/Permutation"

session Launchbury (AFP) in "Launchbury" = "HOLCF-Nominal2" +
  options [document = pdf, document_graph, document_output = "output"]
  theories
    "Everything"

session LaunchburyAdequacy (AFP) in "Launchbury" = "HOLCF-Nominal2" +
  options [document_variants = newstuff, document = pdf, document_graph, document_output = "output" ]
  theories
    "Adequacy"
    "CorrectnessOriginal"

session LaunchburyComplete (AFP) in "Launchbury" = "HOLCF-Nominal2" +
  options [document_variants = newstuff, document = pdf, document_graph, document_output = "output", quick_and_dirty]
  theories
    "NewStuff"
