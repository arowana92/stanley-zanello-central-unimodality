import CentralUnimodality.CertifiedQuadraticCells

open CentralUnimodality.PolynomialTrial

def main : IO Unit := do
  for g in List.range 57 do
    IO.println s!"{g} {twoUnitNum evenQuadraticPower g} {twoUnitNum oddQuadraticPower g} {cellQuadraticNum g}"
