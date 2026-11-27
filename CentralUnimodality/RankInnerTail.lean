module

public import CentralUnimodality.InnerArcs
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Condition the inner-arc block estimates on actual staircase rows. The
constants 100, 0.186 and 0.157 are the ones used in Fourier inversion. -/
@[expose] public section

namespace CentralUnimodality

noncomputable def corankCharacteristic (θ : ℝ) (n δ : ℕ) : ℂ :=
  (∑ j ∈ Finset.range (n*(n+δ)+1),
    rankCount (2*n+δ) j • (areaCharacter (θ/2) 2)^(n*(n+δ)-j))/((2*n+δ).choose n:ℂ)

theorem norm_corankCharacteristic (θ : ℝ) (n δ : ℕ) :
    ‖corankCharacteristic θ n δ‖ =
      ‖∑ j ∈ Finset.range (n*(n+δ)+1),
        rankCount (2*n+δ) j • (areaCharacter (θ/2) 2)^(n*(n+δ)-j)‖/((2*n+δ).choose n:ℝ) := by
  simp [corankCharacteristic]

private theorem prefactor_bound : 16*Real.exp (7/4) ≤ 100 := by
  have h₁ : Real.exp 1 ≤ 11/4 := le_trans Real.exp_one_lt_d9.le (by norm_num)
  have h₂ : 5/4 ≤ Real.exp (1/4) := by linarith only [Real.add_one_le_exp (1/4)]
  have he : Real.exp (7/4)*Real.exp (1/4) = (Real.exp 1)^2 := by
    rw [← Real.exp_add,← Real.exp_nat_mul]
    norm_num
  have h := mul_le_mul_of_nonneg_left h₂ (Real.exp_pos (7/4)).le
  have hs := pow_le_pow_left₀ (Real.exp_pos 1).le h₁ 2
  linarith only [he,h,hs]

private theorem conditioned_inner {n δ : ℕ} {z γ β : ℝ} (hδ : δ ≤ 1) (hn : 2049 ≤ n+δ)
    (hz : 0 < z) (hγ : 0 ≤ γ)
    (h : KilledBound (z^3/2) (innerLength z) (Real.exp (-(γ*z^2)*innerLength z)))
    (hscale : γ*(9+z^2) ≤ 7/4)
    (hβ : β*(2*((n:ℝ)+δ)) ≤ γ*(63/64)*(2*n+δ)) :
    ‖corankCharacteristic (z^3) n δ‖ ≤ 100*Real.exp (-(β*(2*((n:ℝ)+δ))*z^2)) := by
  have hl := innerLength_bounds hz
  have hL : 0 < innerLength z := by
    by_contra! hzero
    rw [Nat.le_zero.mp hzero,Nat.cast_zero,mul_zero] at hl
    norm_num at hl
  rw [norm_corankCharacteristic]
  have hb := conditional_rank_arc hL (mul_nonneg hγ (sq_nonneg z)) h n δ hδ (by omega)
  apply hb.trans
  have he : γ*z^2*innerLength z ≤ 7/4 := by
    nlinarith only [mul_le_mul_of_nonneg_left hl.2 hγ,hscale]
  have htail := mul_le_mul_of_nonneg_right hβ (sq_nonneg z)
  rw [sub_eq_add_neg,Real.exp_add,← mul_assoc]
  apply mul_le_mul ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by norm_num : (0:ℝ) ≤ 16)).trans prefactor_bound)
    (Real.exp_le_exp.mpr (by linarith only [htail])) (Real.exp_pos _).le (by norm_num)

theorem corank_inner_001 {n δ : ℕ} (hδ : δ ≤ 1) (hn : 2049 ≤ n+δ) {z : ℝ} (hz : 0 < z) (hZ : z ≤ 0.1) :
    ‖corankCharacteristic (z^3) n δ‖ ≤ 100*Real.exp (-(0.186*(2*((n:ℝ)+δ))*z^2)) := by
  apply conditioned_inner hδ hn hz (by norm_num) (killed_inner_001 hz hZ)
  · nlinarith only [pow_le_pow_left₀ hz.le hZ 2]
  · have hN : 2049 ≤ (n:ℝ)+δ := by exact_mod_cast hn
    have hp : (δ:ℝ) ≤ 1 := by exact_mod_cast hδ
    linarith only [hN,hp]

theorem corank_inner_008 {n δ : ℕ} (hδ : δ ≤ 1) (hn : 2049 ≤ n+δ) {z : ℝ} (hz : 0 < z) (hZ : z ≤ 0.2) :
    ‖corankCharacteristic (z^3) n δ‖ ≤ 100*Real.exp (-(0.157*(2*((n:ℝ)+δ))*z^2)) := by
  apply conditioned_inner hδ hn hz (by norm_num) (killed_inner_008 hz hZ)
  · nlinarith only [pow_le_pow_left₀ hz.le hZ 2]
  · have hN : 2049 ≤ (n:ℝ)+δ := by exact_mod_cast hn
    have hp : (δ:ℝ) ≤ 1 := by exact_mod_cast hδ
    linarith only [hN,hp]

end CentralUnimodality
