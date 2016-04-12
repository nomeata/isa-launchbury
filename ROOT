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



session Stats_Common = "HOLCF-Nominal2" +
  options [document_variants = empty, document = pdf, document_output = "/tmp/stats-common"]
  theories
    "Launchbury/Terms"
    "Launchbury/Nominal-HOLCF"
    "Launchbury/HOLCF-Join-Classes"
    "Launchbury/Env"
    "Launchbury/Env-Nominal"
    "Launchbury/Env-HOLCF"
    "Launchbury/Substitution"
    "Launchbury/Denotational"
    "Call_Arity/Sestoft"
  document_files
    "root_empty.tex"

session Stats_Semantics = "Stats_Common" +
  options [document_variants = empty, document = pdf, document_output = "/tmp/stats-semantics"]
  theories
    "Launchbury/EverythingAdequacy"
    "Call_Arity/SestoftCorrect"
  document_files
    "root_empty.tex"


session Stats_Call_Arity = "Stats_Common" +
  options [document_variants = empty, document = pdf, document_output = "/tmp/stats-call-arity"]
  theories
    "Call_Arity/TrivialArityAnal"
    "Call_Arity/NoCardinalityAnalysis"
    "Call_Arity/ArityTransformSafe"
    "Call_Arity/CallArityEnd2EndSafe"
    "Call_Arity/ArityAnalysisCorrDenotational"
  document_files
    "root_empty.tex"


session Stats_All = "HOLCF-Nominal2" +
  options [document_variants = empty, document = pdf, document_output = "/tmp/stats-all"]
  theories
    "Launchbury/EverythingAdequacy"
    "Call_Arity/SestoftCorrect"
    "Call_Arity/TrivialArityAnal"
    "Call_Arity/NoCardinalityAnalysis"
    "Call_Arity/ArityTransformSafe"
    "Call_Arity/CallArityEnd2EndSafe"
    "Call_Arity/ArityAnalysisCorrDenotational"
  document_files
    "root_empty.tex"


