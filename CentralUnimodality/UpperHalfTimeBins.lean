module

public import CentralUnimodality.RankBinNumbers

/-! Seven rational first-crossing intervals for every upper-half saddle
with scaled parameter at least 23.8. All power and exponential rounding
is outward. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic

def farCut (i : ℕ) : ℚ := min lateCut (1/10+i/8)
def farBase : ℚ := 119/5
def farDrift : ℚ := 19/50

def farHitCost (i : ℕ) : ℚ :=
  let v := farCut i
  let w := farCut (i+1)
  let e := w+epsilon
  let R := rootLo (v/3-2*epsilon)
  let a := v*(1-e/2)^2/8
  (farBase/farDrift)*(e/2+(4/5)/(R*farBase))^2/R*
    decay (a*(19/20)*farBase^2)/(1-e)^3

def farTimeCost (i : ℕ) : ℚ := ((farCut (i+1)-farCut i)/2+epsilon)*farHitCost i

theorem far_time_data (i : Fin 7) :
    let v := farCut i
    let w := farCut (i+1:ℕ)
    let e := w+epsilon
    0 ≤ v ∧ v ≤ w ∧ w ≤ lateCut ∧ e<1 ∧ 0<rootLo (v/3-2*epsilon) ∧
      80 ≤ 4096*(v/3-2*epsilon) ∧ 1/160 ≤ v*(1-e/2)^2/8 := by
  fin_cases i <;> decide +kernel

theorem far_time_total : (∑ i ∈ Finset.range 7, charge (farTimeCost i)) ≤ 1/40 := by
  decide +kernel

end CentralUnimodality.MarkedExcursion.BinArithmetic
