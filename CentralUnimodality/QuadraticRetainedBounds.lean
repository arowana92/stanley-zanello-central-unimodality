module

public import CentralUnimodality.QuadraticUniformCell
public import CentralUnimodality.QuadraticChargeBlock0
public import CentralUnimodality.QuadraticChargeBlock1
public import CentralUnimodality.QuadraticChargeBlock2
public import CentralUnimodality.QuadraticChargeBlock3

/-! Bounds on the two retained integrals from the exact rational charges. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open ReturnSplit Set Witness

private theorem all_quadratic_charges {i : ℕ} (hi : i<288) : quadraticAllowanceCheck i=true := by
  by_cases a : i<100
  · simpa only [Nat.zero_add] using quadratic_charge_block_0 i a
  by_cases b : i<160
  · simpa only [show 100+(i-100)=i by omega] using quadratic_charge_block_1 (i-100) (by omega)
  by_cases c : i<200
  · simpa only [show 160+(i-160)=i by omega] using quadratic_charge_block_2 (i-160) (by omega)
  simpa only [show 200+(i-200)=i by omega] using quadratic_charge_block_3 (i-200) (by omega)

theorem quadratic_retained_bounds {n δ : ℕ} (hs : δ≤1)
    (errors : ∀ i<288, ∀ ξ∈Icc (frequencyEdge i) (frequencyEdge (i+1)),
      |signedAmplitude n δ (ξ/cellScale (n+δ))-spectralTrial ξ|≤(quadraticFrequencyAllowance i:ℝ)) :
    retainedError n δ 1≤0.136729 ∧ retainedError n δ 2≤35.478 := by
  have cap (r : ℕ) : retainedError n δ r≤((∑ i ∈ Finset.range 288, quadraticFrequencyCharge i r:ℚ):ℝ) :=
    rational_charge_bound hs quadraticFrequencyAllowance quadratic_allowance_nonneg errors r
  have row (r : ℕ) : (∑ i ∈ Finset.range 288, quadraticFrequencyCharge i r)=∑ i ∈ Finset.range 288, storedQuadraticCharge i r := by
    apply Finset.sum_congr rfl
    intro i hi
    exact quadratic_charge_agrees (all_quadratic_charges (Finset.mem_range.mp hi)) r
  constructor
  · apply (cap 1).trans
    rw [row,quadratic_charge_totals.1]; norm_num
  · apply (cap 2).trans
    rw [row,quadratic_charge_totals.2]; norm_num

end CentralUnimodality.PolynomialTrial
