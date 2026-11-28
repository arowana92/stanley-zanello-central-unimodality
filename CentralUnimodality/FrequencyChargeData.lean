module

public import CentralUnimodality.RationalRetainedCost
public import CentralUnimodality.IntegerCellChecks
public meta import CentralUnimodality.RationalRetainedCost
import Mathlib.Tactic.Eval

/-! Exact rational cell allowances and their two weighted sums.
The table is certified against the time-dependent return calculation. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def allowanceTable : Array ℚ := eval% ((List.range 288).map frequencyAllowance).toArray
def allowanceCheck (i : ℕ) := decide (allowanceTable[i]?=some (frequencyAllowance i))

def tableCharge (i r : ℕ) :=
  roundUpper (3/4*rootHigh (topTime i)*(topFrequency i)^r*(allowanceTable[i]?.getD 0))

theorem charge_totals :
    (∑ i ∈ Finset.range 288, tableCharge i 1)≤0.176 ∧
    (∑ i ∈ Finset.range 288, tableCharge i 2)≤148.4 := by decide +kernel

theorem charge_agrees {i : ℕ} (hi : allowanceCheck i=true) (r : ℕ) : frequencyCharge i r=tableCharge i r := by
  simp only [allowanceCheck,decide_eq_true_eq] at hi
  simp [frequencyCharge,tableCharge,hi]

end CentralUnimodality.PolynomialTrial
