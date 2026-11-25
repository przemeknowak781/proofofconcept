import LeanChecker
unsafe def verifyAudit (names : List String) : IO Unit := do
  let output ← IO.getStdout
  for name in names do
    replayFromImports name.toName
    output.putStrLn ("kernel OK " ++ name)
    output.flush
#eval verifyAudit ["TreeEntropy.APriori", "TreeEntropy.Darts", "TreeEntropy.Large", "TreeEntropy.Main", "TreeEntropy.OneVar", "TreeEntropy.Sharp", "TreeEntropy.Sum", "TreeEntropy.Table", "Kenyon.Amplify", "Kenyon.Bethe", "Kenyon.BetheFun", "Kenyon.Cayley", "Kenyon.Contract", "Kenyon.Count", "Kenyon.Examples", "Kenyon.Forest", "Kenyon.ForestCount", "Kenyon.Green", "Kenyon.Lap", "Kenyon.Levels", "Kenyon.LogDet", "Kenyon.Main", "Kenyon.MatrixTree", "Kenyon.MatrixTree2", "Kenyon.OneStep", "Kenyon.Regular", "Kenyon.Sanov", "Kenyon.Sharp", "Kenyon.Super"]
