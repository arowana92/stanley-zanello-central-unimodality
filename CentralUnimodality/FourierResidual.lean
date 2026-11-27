module

public import CentralUnimodality.ReturnInverse
public import Mathlib.Analysis.Complex.Basic

/-! A residual certificate for the no-return Fourier transform. Bounds through
a finite horizon suffice, independently of later coefficients. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries

noncomputable abbrev fairSeries (χ : ℤ → ℂ) (T : ℕ → Finset (List Bool)) : PowerSeries ℂ :=
  walkSeries (2 : ℂ)⁻¹ χ T

theorem norm_coeff_fairSeries (χ : ℤ → ℂ) (hχ : ∀ x, ‖χ x‖ ≤ 1)
    (T : ℕ → Finset (List Bool)) (n : ℕ) :
    ‖coeff n (fairSeries χ T)‖ ≤ (T n).card / (2:ℝ)^n := by
  rw [coeff_walkSeries, norm_mul, norm_pow, norm_inv]
  have hS : ‖∑ w ∈ T n, χ (walkArea w)‖ ≤ (T n).card := calc
    _ ≤ ∑ w ∈ T n, ‖χ (walkArea w)‖ := norm_sum_le _ _
    _ ≤ ∑ _w ∈ T n, (1:ℝ) := Finset.sum_le_sum (fun w _ => hχ (walkArea w))
    _ = _ := by simp
  simpa [div_eq_inv_mul] using mul_le_mul_of_nonneg_left hS
    (show 0 ≤ ‖(2:ℂ)‖⁻¹^n by positivity)

theorem firstReturn_fair_mass (n : ℕ) :
    ∑ t ∈ Finset.range (n+1), (firstReturns t).card / (2:ℝ)^t ≤ 1 := by
  apply (mul_le_mul_iff_left₀ (show 0 < (2:ℝ)^n by positivity)).mp
  rw [Finset.sum_mul, one_mul]
  calc
    _ = ∑ t ∈ Finset.range (n+1), ((firstReturns t).card : ℝ) * (2:ℝ)^(n-t) := by
      apply Finset.sum_congr rfl
      intro t ht
      have he : t + (n-t) = n := by have := Finset.mem_range.mp ht; omega
      have hp : (2:ℝ)^n = 2^t * (2:ℝ)^(n-t) := by rw [← pow_add, he]
      rw [hp, ← mul_assoc, div_mul_cancel₀ _ (by positivity)]
    _ ≤ _ := by exact_mod_cast firstReturn_kraft n

theorem norm_coeff_firstReturn_sum (χ : ℤ → ℂ) (hχ : ∀ x, ‖χ x‖ ≤ 1) (n : ℕ) :
    ∑ t ∈ Finset.range (n+1), ‖coeff t (fairSeries χ firstReturns)‖ ≤ 1 :=
  (Finset.sum_le_sum (fun t _ => norm_coeff_fairSeries χ hχ firstReturns t)).trans (firstReturn_fair_mass n)

/-- If the bridge equation is satisfied to accuracy e through n, the exact
no-return coefficient differs from the proposal at n by at most 2e. -/
theorem fairSeries_residual_bound (χ : ℤ → ℂ) (h₀ : χ 0 = 1)
    (hχ : ∀ x y, χ (x+y) = χ x * χ y) (hN : ∀ x, ‖χ x‖ ≤ 1)
    (V : PowerSeries ℂ) (n : ℕ) (e : ℝ)
    (hE : ∀ j ≤ n, ‖coeff j (fairSeries χ words - fairSeries χ bridges * V)‖ ≤ e) :
    ‖coeff n (fairSeries χ strictWords - V)‖ ≤ 2 * e := by
  let E := fairSeries χ words - fairSeries χ bridges * V
  let H := fairSeries χ firstReturns
  have hEj (j : ℕ) (hj : j ≤ n) : ‖coeff j E‖ ≤ e := hE j hj
  have he := (norm_nonneg _).trans (hEj n le_rfl)
  have hHE : ‖coeff n (H * E)‖ ≤ e := calc
    _ = ‖∑ i ∈ Finset.range (n+1), coeff i H * coeff (n-i) E‖ := by
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    _ ≤ ∑ i ∈ Finset.range (n+1), ‖coeff i H * coeff (n-i) E‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n+1), ‖coeff i H‖ * e := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hEj _ (Nat.sub_le ..)) (norm_nonneg _)
    _ = (∑ i ∈ Finset.range (n+1), ‖coeff i H‖) * e := (Finset.sum_mul ..).symm
    _ ≤ 1 * e := mul_le_mul_of_nonneg_right (norm_coeff_firstReturn_sum χ hN n) he
    _ = e := one_mul e
  have hId : fairSeries χ strictWords - V = E - H * E := by
    simpa only [sub_mul, one_mul] using walkSeries_residual (2:ℂ)⁻¹ χ h₀ hχ V
  rw [hId, map_sub]
  calc
    _ ≤ ‖coeff n E‖ + ‖coeff n (H * E)‖ := norm_sub_le ..
    _ ≤ e + e := add_le_add (hEj n le_rfl) hHE
    _ = 2 * e := (two_mul e).symm

end CentralUnimodality
