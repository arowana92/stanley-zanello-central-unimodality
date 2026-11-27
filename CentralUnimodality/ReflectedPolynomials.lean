module

public import CentralUnimodality.AllReflected
public import CentralUnimodality.DyckReduction

/-! Put the all-size reflected comparison into the exact polynomial form
used on the right-hand side of the prefix recurrences. -/
@[expose] public section

namespace CentralUnimodality

theorem odd_reflected_polynomial (n : ℕ) (hu : UnimodalOn (rankCount (2*n)) 0 (n*n)) :
    ReflectedCoeffs (ballotPoly (2*n)) ⌊oddCutoff n⌋ := by
  intro i j hij hcut
  have h : (i:ℝ)+j ≤ oddCutoff n := by exact_mod_cast (Int.le_floor.mp hcut)
  unfold oddCutoff at h
  have hd : j ≤ n*n := by
    apply (show j ≤ n*(n+0) → j ≤ n*n by simp) (Witness.reflected_cut_le_degree (δ := 0) (by decide) ?_)
    simp only [Nat.add_zero,Nat.cast_zero,sub_zero]
    linarith only [h,Nat.cast_nonneg (α := ℝ) i]
  have hc : i+j ≤ reflectedLimit (2*n+0) := by
    apply le_reflectedLimit
    have hN : (2*n+0+1)/2 = n := by omega
    rw [hN,show i+j+(2*n+0+1+n) = i+j+3*n+1 by omega]
    have hs : (Witness.cellScale n)^2 = (2*(n:ℝ))^3 := by
      rw [Witness.cellScale,mul_pow,Real.sq_sqrt (by positivity)]; ring
    have hle : 250*((i:ℝ)+j+3*n+1) ≤ 131*Witness.cellScale n := by linarith only [h]
    have hsq := (sq_le_sq₀ (by positivity) (by unfold Witness.cellScale; positivity)).mpr hle
    rw [mul_pow 131,hs] at hsq
    exact_mod_cast hsq
  have hr := reflected_of_unimodal (n := n) (δ := 0) (by decide) (by simpa using hu) hij hc
  have hcoeff (k : ℕ) (hk : k ≤ n*n) : (ballotPoly (2*n)).coeff k = rankCount (2*n) (n*n-k) := by
    simpa only [Nat.add_zero] using ballotPoly_coeff n 0 k (by decide) (by simpa using hk)
  rw [hcoeff i (hij.le.trans hd),hcoeff j hd]
  simpa only [Nat.add_zero] using hr

/-- The two remaining ingredients are the ordinary Dyck interval decomposition
with its endpoint estimate, and the central signs through the midpoint. -/
theorem conjecture34_of_dyck_and_midpoints (E : ℕ → ℤ)
    (hD : ∀ l, IntervalDecomposition (dyckPoly l) (E l))
    (hE : ∀ l, dyckLower l ≤ (E l:ℝ))
    (hc : ∀ n ≥ 96, ∀ δ ≤ 1, CentralToMidpoint n δ) : Conjecture34 :=
  central_from_midpoints E hD hE odd_reflected_polynomial hc

theorem conjecture34_of_comparisons_and_midpoints (hD : DyckComparisons)
    (hc : ∀ n ≥ 96, ∀ δ ≤ 1, CentralToMidpoint n δ) : Conjecture34 :=
  central_from_comparisons hD odd_reflected_polynomial hc

end CentralUnimodality
