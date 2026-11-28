module

public import CentralUnimodality.SecondResidualRows
public import CentralUnimodality.RationalRowCache
public meta import CentralUnimodality.SecondResidualRows
public meta import CentralUnimodality.RationalRowCache

/-! Candidate physical coefficient lists for the two signed residuals. Their
identification with the split formula is proved after checking its products. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial.QuadraticInputs
open RationalPolyRow

set_option maxRecDepth 65536

def evenPhysicalEncoding : List ℤ × ℕ := eval% encode (quadraticResidualRow 0)
def oddPhysicalEncoding : List ℤ × ℕ := eval% encode (quadraticResidualRow 1)
def evenResidual := decode evenPhysicalEncoding
def oddResidual := decode oddPhysicalEncoding

end CentralUnimodality.PolynomialTrial.QuadraticInputs
