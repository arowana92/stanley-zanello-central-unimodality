module

public import CentralUnimodality.NormalizedCells
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Frequency scaling on the corrected split. The logarithmic expansions
are needed only through rescaled time 114. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open Real Set Witness

theorem peak_frequency_scale {N : ℕ} (np : 0<N) {ξ : ℝ} (hξ : |ξ|≤1728) :
    let u := |ξ|^(2/3:ℝ)
    u∈Icc (0:ℝ) 144 ∧ (ξ/cellScale N/2)^2=(u/N)^3/32 := by
  let u := |ξ|^(2/3:ℝ)
  have cube : u^3=ξ^2 := by
    dsimp only [u]; rw [← rpow_natCast _ 3,← rpow_mul (abs_nonneg ξ)]; norm_num
  have scale : (cellScale N)^2=(2*(N:ℝ))^3 := by
    unfold cellScale; rw [mul_pow,sq_sqrt (by positivity)]; ring
  constructor
  · refine ⟨rpow_nonneg (abs_nonneg ξ) _,?_⟩
    apply le_of_pow_le_pow_left₀ (n:=3) (by decide) (by norm_num)
    rw [cube,← sq_abs]
    exact (pow_le_pow_left₀ (abs_nonneg ξ) hξ 2).trans (by norm_num)
  · rw [div_pow,div_pow,div_pow,scale,← cube]
    field_simp; ring

theorem peak_local_angle {N : ℕ} (hn : 150000≤N) {ξ : ℝ} (hu : |ξ|^(2/3:ℝ)≤114) :
    |ξ/cellScale N/2| *(2*(N:ℝ)+1)≤9/8 := by
  have nr : (150000:ℝ)≤N := by exact_mod_cast hn
  have cube : (|ξ|^(2/3:ℝ))^3=|ξ|^2 := by
    rw [← rpow_natCast _ 3,← rpow_mul (abs_nonneg ξ)]; norm_num
  have size : |ξ|≤1218 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤1218)).mp
    rw [← cube]
    exact (pow_le_pow_left₀ (rpow_nonneg (abs_nonneg _) _) hu 3).trans (by norm_num)
  have root : (547:ℝ)≤sqrt (2*N) := le_sqrt_of_sq_le (by linarith only [nr])
  have lower := mul_le_mul_of_nonneg_left root (by positivity : 0≤2*(N:ℝ))
  have upper := mul_le_mul_of_nonneg_right size (by positivity : 0≤2*(N:ℝ)+1)
  have sp := cellScale_pos (by omega : 0<N)
  rw [abs_div,abs_div,abs_of_pos sp,abs_of_pos (by norm_num : (0:ℝ)<2)]
  field_simp [sp]
  unfold cellScale
  linarith only [upper,lower,nr]

end CentralUnimodality.ReturnSplit
