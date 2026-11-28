module

public import CentralUnimodality.PackedIntervalSigns
public import CentralUnimodality.PackedBaseResidual

/-! Supremum certificate for the tail of the trial polynomial using
the integer projective transform on nine closed intervals. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

def tailPair (l h : ℤ) : Bool :=
  let z := homogeneousPack 6145 l h 256 trialPower
  packedDigitsTest 6144 422 (10^14) (-(2^120)) z &&
    packedDigitsTest 6144 422 (-(10^14)) (-(2^120)) z

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem tail_checks :
    tailPair 64 88=true ∧
    tailPair 88 112=true ∧
    tailPair 112 160=true ∧
    tailPair 160 184=true ∧
    tailPair 184 208=true ∧
    tailPair 208 232=true ∧
    tailPair 232 244=true ∧
    tailPair 244 250=true ∧
    tailPair 250 256=true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem tail_capacity :
    trialPower.length+1≤422 ∧
    (10^14*coefficientMass trialPower+2^120)*512^trialPower.length<2^6144 := by decide +kernel

end CentralUnimodality.PolynomialTrial
