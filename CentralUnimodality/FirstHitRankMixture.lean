module

public import CentralUnimodality.LatticeDifference
public import CentralUnimodality.HitTiltBins
public import CentralUnimodality.PrefixRankMixture

/-! Rank-resolved differences for the discarded event of a first hit at
a prescribed time. The remaining labels retain their independent law. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

/-- A signed difference commutes with the mixture at the exact shifted rank. -/
theorem prefix_difference_mixture (c : ℝ) {m t : ℕ} (ht : t ≤ m) (A : Finset (List Bool))
    (hA : A ⊆ words t) (r : Fin 3) (k : ℤ) :
    rankDifference r k (prefixEventSiteMass c m t A) =
    ∑ w ∈ A, signMass c (c*m) w * rankDifference r (k-shiftedPrefixRank (m-t) w) (freeRankMass c (m-t)) := by
  let S := fun (w : List Bool) (j : ℤ) => freeRankMass c (m-t) (j-shiftedPrefixRank (m-t) w)
  have he : prefixEventSiteMass c m t A = ∑ w ∈ A, signMass c (c*m) w • S w := by
    funext j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    exact prefixEventSiteMass_mixture c ht A hA j
  simp only [he,map_sum,map_smul,smul_eq_mul,S,rankDifference_shift]

/-- The prefactor is the probability of the prefix event. This preserves
the difference cancellation inside each independent suffix. -/
theorem prefix_difference_bound (c : ℝ) {m t : ℕ} (ht : t ≤ m) (A : Finset (List Bool))
    (hA : A ⊆ words t) (r : Fin 3) {U : ℝ} (hU : ∀ j : ℤ, |rankDifference r j (freeRankMass c (m-t))| ≤ U)
    (k : ℤ) : |rankDifference r k (prefixEventSiteMass c m t A)| ≤ (∑ w ∈ A, signMass c (c*m) w)*U := by
  rw [prefix_difference_mixture c ht A hA r k,Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply Finset.sum_le_sum
  intro w _
  rw [abs_mul,abs_of_pos (signMass_pos ..)]
  exact mul_le_mul_of_nonneg_left (hU _) (signMass_pos ..).le

/-- Rank-resolved form of the time-bin bound (6) for all three signed
orders. The tilt factor on the left is common to every neighboring site. -/
theorem first_hit_rank_bin {m d : ℕ} (ht : 2*d+1 ≤ m) {c z s γ Δ v e : ℝ}
    (hc : 0 ≤ c) (hz : 0 ≤ z) (hs : s^2=(m:ℝ)^3) (hγ : γ=2*c*s) (hΔ : Δ=2*z*s)
    (hsmall : γ^2 ≤ 6*m) (he : e ≤ 2) (hlo : v*m ≤ 2*(d:ℝ)+1) (hhi : 2*(d:ℝ)+1 ≤ e*m)
    (r : Fin 3) {U : ℝ} (hU : ∀ j : ℤ, |rankDifference r j (freeRankMass (c+z) (m-(2*d+1)))| ≤ U)
    (k : ℤ) :
    rankChange c z (meanRank c m) m *
      |rankDifference r k (prefixEventSiteMass (c+z) m (2*d+1) (hitWords 1 (2*d+1)))| ≤
      exp (Δ^2*(labelSquares m/(m:ℝ)^3)/8 - v*(1-e/2)^2*(γ+Δ)*(γ*(1-γ^2/(6*m))+Δ)/8) *
        (∑ w ∈ hitWords 1 (2*d+1), signMass (c+z) ((c+z)*d) w) * U := by
  have H := first_hit_bin ht hc hz hs hγ hΔ hsmall he hlo hhi
  rw [mass_prefix (c+z) ((c+z)*m) ht (hitWords 1 (2*d+1)) (Finset.filter_subset ..)] at H
  have hr := prefix_difference_bound (c+z) ht (hitWords 1 (2*d+1)) (Finset.filter_subset ..) r hU k
  apply (mul_le_mul_of_nonneg_left hr (rankChange_pos ..).le).trans
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right H ((abs_nonneg _).trans (hU 0))

end CentralUnimodality.MarkedExcursion
