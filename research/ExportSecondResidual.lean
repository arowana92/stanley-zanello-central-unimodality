import CentralUnimodality.SecondResidualRows

/-! Stream the two polynomial rows as exact integers for the independent
coefficient comparison in verify_second_split.py. -/
open CentralUnimodality.PolynomialTrial

def main : IO Unit := do
  for parity in [0,1] do
    let row := quadraticResidualRow parity
    IO.println s!"{parity} {row.numer.length}"
    IO.println (toString (row.denom:ℕ))
    for coefficient in row.numer do
      IO.println (toString coefficient)
