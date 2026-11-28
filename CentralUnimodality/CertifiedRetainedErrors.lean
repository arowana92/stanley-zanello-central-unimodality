module

public import CentralUnimodality.UniformCellAmplitude
public import CentralUnimodality.SplitMaximaBlock0
public import CentralUnimodality.SplitMaximaBlock1
public import CentralUnimodality.SplitMaximaBlock2
public import CentralUnimodality.SplitMaximaBlock3
public import CentralUnimodality.FrequencyAllowanceBlock0
public import CentralUnimodality.FrequencyAllowanceBlock1
public import CentralUnimodality.FrequencyAllowanceBlock2
public import CentralUnimodality.FrequencyAllowanceBlock3

/-! Both true weighted retained Fourier errors for both staircase
families, uniformly over every half-length at least 150,000. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

theorem all_split_maxima (i : ℕ) (hi : i<288) : cellMaxTest i=true := by
  by_cases a : i<144
  · simpa only [Nat.zero_add] using maxima_block_0 i a
  by_cases b : i<204
  · simpa only [show 144+(i-144)=i by omega] using maxima_block_1 (i-144) (by omega)
  by_cases c : i<249
  · simpa only [show 204+(i-204)=i by omega] using maxima_block_2 (i-204) (by omega)
  simpa only [show 249+(i-249)=i by omega] using maxima_block_3 (i-249) (by omega)

theorem all_frequency_allowances (i : ℕ) (hi : i<288) : allowanceCheck i=true := by
  by_cases a : i<144
  · simpa only [Nat.zero_add] using allowance_block_0 i a
  by_cases b : i<204
  · simpa only [show 144+(i-144)=i by omega] using allowance_block_1 (i-144) (by omega)
  by_cases c : i<249
  · simpa only [show 204+(i-204)=i by omega] using allowance_block_2 (i-204) (by omega)
  simpa only [show 249+(i-249)=i by omega] using allowance_block_3 (i-249) (by omega)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem exact_charge_totals :
    (∑ i ∈ Finset.range 288, tableCharge i 1)=172963162671854636150765017741/10^30 ∧
    (∑ i ∈ Finset.range 288, tableCharge i 2)=10519170698051795800640705312913/500000000000000000000000000000 := by decide +kernel

theorem certified_retained_errors {n δ : ℕ} (hs : δ≤1) (hn : 150000≤n+δ) :
    retainedError n δ 1≤0.174 ∧ retainedError n δ 2≤22 := by
  have row (r : ℕ) : (∑ i ∈ Finset.range 288, frequencyCharge i r)=∑ i ∈ Finset.range 288, tableCharge i r := by
    apply Finset.sum_congr rfl
    intro i hi
    exact charge_agrees (all_frequency_allowances i (Finset.mem_range.mp hi)) r
  have cap (r : ℕ) := retained_charge_bound hs hn all_split_maxima r
  constructor
  · apply (cap 1).trans
    rw [row]
    simpa only [Rat.cast_ofScientific] using (Rat.cast_le (K:=ℝ)).mpr charge_totals.1
  · apply (cap 2).trans
    rw [row]
    simpa only [Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr charge_totals.2

end CentralUnimodality.PolynomialTrial
