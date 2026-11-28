module

public import CentralUnimodality.SpatialIntegralWitnesses
public import CentralUnimodality.BalancedIntervalSigns
public import CentralUnimodality.BlockRadixDigits

/-! Exact integer sign checks for the compact spatial windows. Each
homogeneous transformation uses one packed integer product tree. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

def spatialSign (a : List ℤ) (l h m k : ℤ) : Bool :=
  let (p,q) := balancedPack 10 32769 l h 10000 a
  (blockCenteredDigits 32768 10 1026 (m*p-(k*trialRowDen)*q)).all (fun c => decide (0≤c))

theorem spatialSign_exact (a : List ℤ) (l h m k : ℤ) :
    spatialSign a l h m k=packedDigitsTest 32768 1026 m (k*trialRowDen)
      (homogeneousPack 32769 l h 10000 a) := by
  simp only [spatialSign,balancedPack_exact,blockCenteredDigits_exact,packedDigitsTest]

theorem first_trial_coefficients : tabulatedRow 1 1024 spatialMoments=firstTrialRow := by decide +kernel
theorem second_trial_coefficients : tabulatedRow 2 1024 spatialMoments=secondTrialRow := by decide +kernel

theorem trial_row_den {r : ℕ} (hr : r≤2) : integralDen r 1024 trialPower=trialRowDen := by
  have len : trialPower.length=421 := by rw [trialPower,unpackCheb,centeredDigits_length]; decide
  have top : momentTop r 1024 trialPower≤4000 := by unfold momentTop; rw [len]; omega
  simp only [integralDen,momentDivisor,top,ite_true,len]
  decide +kernel

theorem first_trial_capacity : coefficientMass firstTrialRow≤2^16500 ∧ trialRowDen≤2^16000 := by decide +kernel
theorem second_trial_capacity : coefficientMass secondTrialRow≤2^16500 ∧ trialRowDen≤2^16000 := by decide +kernel

theorem left_trial_sign : spatialSign firstTrialRow 1359 3390 5 1=true := by decide +kernel
theorem middle_trial_sign : spatialSign secondTrialRow 3330 4040 (-1) 160=true := by decide +kernel
theorem right_trial_sign : spatialSign firstTrialRow 3980 6310 (-1) 2=true := by decide +kernel

end CentralUnimodality.PolynomialTrial
