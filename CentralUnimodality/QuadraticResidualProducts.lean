module

public import CentralUnimodality.QuadraticLeadingJets
public import CentralUnimodality.QuadraticFirstJets
public import CentralUnimodality.QuadraticPhysicalWitnesses
public meta import CentralUnimodality.QuadraticLeadingJets
public meta import CentralUnimodality.QuadraticFirstJets
public meta import CentralUnimodality.RationalRowCache

/-! Assemble the checked factorial products into the exact signed polynomial
for each parity, saving the common part once. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial.QuadraticInputs
open RationalPolyRow

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

cache_rational_row noncomputable leadingBF leadingBF_exact := beta bTwo trial
cache_rational_row noncomputable leadingEven leadingEven_exact := beta bOne gEven
cache_rational_row noncomputable leadingOdd leadingOdd_exact := beta bOne gOdd

cache_rational_row noncomputable firstBF firstBF_exact := scale 1 2 (shift 1 secondBF)
cache_rational_row noncomputable firstEven firstEven_exact := scale 1 2 (shift 1 secondEven)
cache_rational_row noncomputable firstOdd firstOdd_exact := scale 1 2 (shift 1 secondOdd)
cache_rational_row noncomputable secondBFBase secondBFBase_exact :=
  linear 1 1 (scale 1 6 (shift 1 (linear 1 (-1) third12 third21))) (scale 1 8 (shift 2 fourth22))

noncomputable def assemble (p leading first : RationalPolyRow) :=
  linear 1 (-1) (linear 1 (-1) (linear 1 (-1) (linear 1 (-1) p leadingBF) leading)
    (linear 1 1 firstBF first)) secondBFBase

theorem evenResidual_exact : assemble pEven leadingEven firstEven=evenResidual := by
  have h : encode (assemble pEven leadingEven firstEven)=evenPhysicalEncoding := by decide +kernel
  exact (decode_encode _).symm.trans (congrArg decode h)

theorem oddResidual_exact : assemble pOdd leadingOdd firstOdd=oddResidual := by
  have h : encode (assemble pOdd leadingOdd firstOdd)=oddPhysicalEncoding := by decide +kernel
  exact (decode_encode _).symm.trans (congrArg decode h)

end CentralUnimodality.PolynomialTrial.QuadraticInputs
