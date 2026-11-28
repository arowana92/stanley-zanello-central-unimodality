module

public import CentralUnimodality.FirstChebyshevData
public import CentralUnimodality.TwoBetaPacking
public meta import CentralUnimodality.FirstChebyshevData
import Mathlib.Tactic.Eval

/-! Factorial-weighted rows for the equality of the two corrected beta
products. The literal rows keep the integer replay in bounded pieces. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

def firstResidualPower (σ : ℕ) := unpackCheb 5120 (firstWitness σ).2
def firstLeft (σ : ℕ) := linearRows ((firstWitness σ).1:ℤ) (-(7680*2^240*(residualDen:ℤ)))
  (firstOrdinary σ) (firstResidualPower σ)
def firstPacking (σ : ℕ) := weightedPair (firstLeft σ) firstBridge trialPower bridgePower (correctionPower σ)

def evenLeftWeighted : List ℤ := eval% fullWeighted (firstLeft 0)
def oddLeftWeighted : List ℤ := eval% fullWeighted (firstLeft 1)
def firstBridgeWeighted : List ℤ := eval% halfWeighted firstBridge
def firstTrialWeighted : List ℤ := eval% halfWeighted trialPower
def bridgeTrialWeighted : List ℤ := eval% halfWeighted bridgePower
def evenMWeighted : List ℤ := eval% halfWeighted (correctionPower 0)
def oddMWeighted : List ℤ := eval% halfWeighted (correctionPower 1)

def evenCachedPacking : BetaPairRows :=
  ⟨evenLeftWeighted,firstBridgeWeighted,firstTrialWeighted,bridgeTrialWeighted,evenMWeighted⟩
def oddCachedPacking : BetaPairRows :=
  ⟨oddLeftWeighted,firstBridgeWeighted,firstTrialWeighted,bridgeTrialWeighted,oddMWeighted⟩

end CentralUnimodality.PolynomialTrial
