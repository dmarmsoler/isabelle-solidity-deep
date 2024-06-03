session Solidity = "HOL-Library" +
  options [document = pdf, document_output = "output"]
  sessions
    "HOL-Eisbach"
  theories
    ReadShow
    StateMonad
    Valuetypes
    Storage
    Accounts
    Environment
    Statements
    Solidity_Main
    Solidity_Symbex
    Solidity_Evaluator
    Reentrancy
  theories [condition = ISABELLE_GHC]
    Compile_Evaluator
  document_files
    "root.tex"
    "root.bib"
    "orcidlink.sty"
  export_files (in ".") [2] "*:**.hs" "*:**.ML"
  export_files (in "solidity-evaluator/bin") [1] "*:solidity-evaluator"
