session DissSnippets1 in Launchbury = "HOLCF-Nominal2" +
  options [document_variants = empty, document = pdf, document_output = "/home/jojo/uni/diss/isa-thy-output"]
  theories
    "EverythingAdequacy"
  document_files "root_empty.tex"

session DissSnippets2 in Call_Arity = DissSnippets1 +
  options [document_variants = empty, document = pdf, document_output = "/home/jojo/uni/diss/isa-thy-output"]
  theories
    "SestoftCorrect"
    "TrivialArityAnal"
    "NoCardinalityAnalysis"
    "ArityTransformSafe"
    "CallArityEnd2EndSafe"
    "ArityAnalysisCorrDenotational"
  document_files "root_empty.tex"

session DissSnippets3 = "HOLCF-Nominal2" +
  options [document_variants = empty, document = pdf, document_output = "/home/jojo/uni/diss/isa-thy-output"]
  theories
    "Scratchpad/ITree"
    "Scratchpad/LTree"
  document_files "root_empty.tex"

session DissSnippets = "HOLCF-Nominal2" +
  options [document_variants = empty, document = pdf, document_output = "/home/jojo/uni/diss/isa-thy-output"]
  theories
    "Launchbury/EverythingAdequacy"
    "Call_Arity/SestoftCorrect"
    "Call_Arity/TrivialArityAnal"
    "Call_Arity/NoCardinalityAnalysis"
    "Call_Arity/ArityTransformSafe"
    "Call_Arity/CallArityEnd2EndSafe"
    "Call_Arity/ArityAnalysisCorrDenotational"
    "Scratchpad/ITree"
    "Scratchpad/LTree"
  document_files "root_empty.tex"


session Arity (AFP) in "Call_Arity" = "HOLCF-Nominal2" +
  options [document_variants = arity, document = pdf, document_output = "output" ]
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


session Call_Arity_Paperstats (AFP) = "HOLCF-Nominal2" +
  options [document = pdf, document_output = "/tmp/call-arity-paperstats"]
  theories
    (* "Call_Arity/SestoftCorrect" *)
    "Call_Arity/TrivialArityAnal"
    "Call_Arity/NoCardinalityAnalysis"
    "Call_Arity/ArityTransformSafe"
    "Call_Arity/CallArityEnd2EndSafe"
    "Call_Arity/ArityAnalysisCorrDenotational"
  document_files
    "root.tex"


