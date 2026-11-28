module

public import CentralUnimodality.QuadraticPrices
public import CentralUnimodality.IntegerCellChecks
public meta import CentralUnimodality.QuadraticPrices
import Mathlib.Tactic.Eval

/-! Exact rational frequency sums for the quadratic certificate. Local
data and each return-time allowance have separate kernel checks. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

def quadraticAllowances : Array ℚ := eval% ((List.range 288).map quadraticFrequencyAllowance).toArray

def quadraticAllowanceCheck (i : ℕ) := decide (quadraticAllowances[i]?=some (quadraticFrequencyAllowance i))

def storedQuadraticCharge (i r : ℕ) :=
  roundUpper (3/4*rootHigh (topTime i)*(topFrequency i)^r*(quadraticAllowances[i]?.getD 0))

theorem quadratic_charge_totals :
    (∑ i ∈ Finset.range 288, storedQuadraticCharge i 1)=136728072565006141360288466101/10^30 ∧
    (∑ i ∈ Finset.range 288, storedQuadraticCharge i 2)=221734617957719363864526305557/6250000000000000000000000000 := by
  decide +kernel

theorem quadratic_charge_agrees {i : ℕ} (hi : quadraticAllowanceCheck i=true) (r : ℕ) :
    quadraticFrequencyCharge i r=storedQuadraticCharge i r := by
  simp only [quadraticAllowanceCheck,decide_eq_true_eq] at hi
  simp [quadraticFrequencyCharge,storedQuadraticCharge,hi]

end CentralUnimodality.PolynomialTrial
