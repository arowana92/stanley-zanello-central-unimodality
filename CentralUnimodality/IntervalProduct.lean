module

public import CentralUnimodality.Stump
public import Mathlib.Algebra.Polynomial.Coeff

/-! An interval factor transfers reflected comparisons of a smaller row to
adjacent comparisons of the product. Integer subscripts treat left boundary
terms of the convolution as zero. -/
@[expose] public section

namespace CentralUnimodality

open Polynomial

noncomputable def ballotPoly (m : ℕ) : Polynomial ℕ := corankSum X (ballots m)
noncomputable def dyckPoly (n : ℕ) : Polynomial ℕ := corankSum X (dycks n)

theorem ballotPoly_coeff (n δ k : ℕ) (hδ : δ ≤ 1) (hk : k ≤ n*(n+δ)) :
    (ballotPoly (2*n+δ)).coeff k = rankCount (2*n+δ) (n*(n+δ)-k) := by
  rw [ballotPoly, ballot_rank_polynomial _ n δ hδ, finsetSum_coeff]
  rw [Finset.sum_eq_single_of_mem (n*(n+δ)-k) (Finset.mem_range.mpr (by omega))]
  · simp [coeff_X_pow, show n*(n+δ)-(n*(n+δ)-k) = k by omega]
  · intro i hi hne
    have h := Finset.mem_range.mp hi
    simp [coeff_X_pow, show k ≠ n*(n+δ)-i by omega]

/-- An interval of width w has w+1 terms and starts at a. -/
noncomputable def intervalPoly (a w : ℕ) : Polynomial ℕ :=
  ∑ t ∈ Finset.range (w+1), X^(a+t)

def intCoeff (P : Polynomial ℕ) (k : ℤ) : ℕ := if 0 ≤ k then P.coeff k.toNat else 0

private theorem shifted_coeff (P : Polynomial ℕ) (s k : ℕ) :
    (P*X^s).coeff k = intCoeff P ((k:ℤ)-s) := by
  rw [coeff_mul_X_pow', intCoeff]
  by_cases hs : s ≤ k <;> simp [hs, Int.toNat_sub']

theorem interval_product_coeff (P : Polynomial ℕ) (a w k : ℕ) :
    (P * intervalPoly a w).coeff k =
      ∑ t ∈ Finset.range (w+1), intCoeff P ((k:ℤ)-a-t) := by
  simp only [intervalPoly, Finset.mul_sum, finsetSum_coeff, shifted_coeff, Nat.cast_add, sub_add_eq_sub_sub]

theorem interval_product_balance (P : Polynomial ℕ) (a w k : ℕ) :
    (P * intervalPoly a w).coeff (k+1) + intCoeff P ((k:ℤ)-a-w) =
      (P * intervalPoly a w).coeff k + intCoeff P ((k:ℤ)+1-a) := by
  rw [interval_product_coeff, interval_product_coeff, Finset.sum_range_succ' _ (w+0),
    Finset.sum_range_succ (fun t => intCoeff P ((k:ℤ)-a-t)) w]
  simp only [Nat.add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
  have ht (i : ℕ) : (k:ℤ)+1-a-(i+1) = k-a-i := by omega
  simp only [ht]
  omega

/-- A bound on the sum of the two reflected indices suffices. If the left
index is negative, the step is automatically nondecreasing. -/
theorem interval_product_step {P : Polynomial ℕ} {T : ℤ}
    (href : ∀ i j : ℕ, i < j → (i:ℤ)+j ≤ T → P.coeff i ≤ P.coeff j)
    (a w k : ℕ) (hcut : 2*(k:ℤ)+1 ≤ T+2*a+w) :
    (P * intervalPoly a w).coeff k ≤ (P * intervalPoly a w).coeff (k+1) := by
  have hb := interval_product_balance P a w k
  by_cases hl : 0 ≤ (k:ℤ)-a-w
  · have hr : 0 ≤ (k:ℤ)+1-a := by omega
    have hle := href ((k:ℤ)-a-w).toNat ((k:ℤ)+1-a).toNat (by omega) (by omega)
    simp only [intCoeff, hl, hr, ite_true] at hb
    omega
  · simp only [intCoeff, ite_eq_right hl, Nat.add_zero] at hb
    omega

end CentralUnimodality
