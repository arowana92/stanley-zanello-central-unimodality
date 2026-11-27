module

public import CentralUnimodality.SpectralMajorant
import Mathlib.Analysis.Real.Pi.Bounds

/-! The two inner-arc reserves in the scaled first and second differences.
A right-endpoint Fourier grid may have any spacing and any finite length. -/
@[expose] public section

namespace CentralUnimodality

noncomputable def spectralGridSum (r J k : ℕ) (Δ : ℝ) : ℝ :=
  (2/Real.pi)*∑ i ∈ Finset.range k, let x := Δ*((J+i+1:ℕ):ℝ)
    Δ*(100*x^r*Real.exp (-(0.157*x^(2/3:ℝ))))

private def expUnit := upperNegExp (0.157*161/16)

private theorem spectral_exp : Real.exp (-(0.157*161)) ≤ (expUnit:ℝ)^16 := by
  have h := upperNegExp_sound (by norm_num : (0:ℚ) ≤ 0.157*161/16)
  apply le_trans _ (pow_le_pow_left₀ (Real.exp_pos _).le h 16)
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  norm_num

private theorem grid_constants :
    200/3.14*10.38*12.69^4*expUnit^16 ≤ 0.000182 ∧
    200/3.14*11.1*12.69^7*expUnit^16 ≤ 0.396 := by decide +kernel

private theorem cutoff_cube : (Real.sqrt 161)^3 ≤ 2048 := by
  have h : Real.sqrt 161 ≤ 12.69 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  exact (pow_le_pow_left₀ (Real.sqrt_nonneg _) h 3).trans (by norm_num)

private theorem grid_bound {r J : ℕ} {Δ : ℝ} (hΔ : 0 < Δ) (hJ : 2048 ≤ Δ*J)
    (k : ℕ) {C cap : ℚ} (hC : 0 ≤ C) (hr : 0 < r) (hsize : 3*r ≤ 50)
    (hK : 0 ≤ 2*0.157*C-3) (hmargin : C*((3*r:ℕ)+1) ≤ (2*0.157*C-3)*161)
    (hc : 200/3.14*C*12.69^(3*r+1)*expUnit^16 ≤ cap) : spectralGridSum r J k Δ ≤ cap := by
  let y (i : ℕ) := (Δ*((J+i:ℕ):ℝ))^(1/3:ℝ)
  have hbase (i : ℕ) : 0 ≤ Δ*((J+i:ℕ):ℝ) := by positivity
  have h₃ (i : ℕ) : (y i)^3 = Δ*((J+i:ℕ):ℝ) := by
    dsimp [y]
    rw [← Real.rpow_natCast,← Real.rpow_mul (hbase _)]
    norm_num
  have h₂ (i : ℕ) : (y i)^2 = (Δ*((J+i:ℕ):ℝ))^(2/3:ℝ) := by
    dsimp [y]
    rw [← Real.rpow_natCast,← Real.rpow_mul (hbase _)]
    norm_num
  have hy : Real.sqrt 161 ≤ y 0 := by
    apply le_of_pow_le_pow_left₀ (n := 3) (by decide) (Real.rpow_nonneg (hbase _) _)
    change (Real.sqrt 161)^3 ≤ (y 0)^3
    rw [h₃,Nat.add_zero]
    exact cutoff_cube.trans hJ
  have hm : Monotone y := by
    intro a b hab
    apply Real.rpow_le_rpow (hbase _) _ (by norm_num)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_left hab J) hΔ.le
  have hd (i : ℕ) : (y (i+1))^3-(y i)^3 = Δ := by simp only [h₃]; push_cast; ring
  have hCr : (0:ℝ) ≤ C := by exact_mod_cast hC
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 161)
  have hc₁ : (3*r:ℕ) ≤ 2*(0.157:ℝ)*(Real.sqrt 161)^2 := by
    rw [hsq]
    have h' : ((3*r:ℕ):ℝ) ≤ 50 := by exact_mod_cast hsize
    linarith only [h']
  have hh : (C:ℝ)*(((3*r:ℕ):ℝ)+1) ≤ (2*0.157*(C:ℝ)-3)*(Real.sqrt 161)^2 := by
    rw [hsq]
    simpa using (Rat.cast_le (K := ℝ)).mpr hmargin
  have hsum := spectral_grid (by norm_num : (0:ℝ) ≤ 0.157) hCr (Real.sqrt_nonneg _) (Nat.mul_pos (by decide) hr)
    hc₁ (by simpa using (Rat.cast_le (K := ℝ)).mpr hK) hh y hy hm hd k
  have he (i : ℕ) : spectralTerm 0.157 (3*r) (y (i+1)) =
      (Δ*((J+i+1:ℕ):ℝ))^r*Real.exp (-(0.157*(Δ*((J+i+1:ℕ):ℝ))^(2/3:ℝ))) := by
    simp only [spectralTerm,pow_mul,h₃,h₂,Nat.add_assoc,neg_mul]
  have hgrid : spectralGridSum r J k Δ = (200/Real.pi)*
      ∑ i ∈ Finset.range k, Δ*spectralTerm 0.157 (3*r) (y (i+1)) := by
    unfold spectralGridSum
    simp_rw [he]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hgrid]
  apply (mul_le_mul_of_nonneg_left hsum (by positivity)).trans
  have hroot : Real.sqrt 161 ≤ 12.69 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have hπ : (200:ℝ)/Real.pi ≤ 200/3.14 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) Real.pi_gt_d2.le
  have htail : spectralTerm 0.157 (3*r+1) (Real.sqrt 161) ≤ 12.69^(3*r+1)*(expUnit:ℝ)^16 := by
    unfold spectralTerm
    rw [hsq]
    exact mul_le_mul (pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot _) (by simpa only [neg_mul] using spectral_exp) (Real.exp_pos _).le (by positivity)
  have hcap : (200/3.14:ℝ)*C*12.69^(3*r+1)*(expUnit:ℝ)^16 ≤ cap := by simpa using (Rat.cast_le (K := ℝ)).mpr hc
  apply le_trans _ hcap
  calc
    _ ≤ (200/3.14:ℝ)*((C:ℝ)*(12.69^(3*r+1)*(expUnit:ℝ)^16)) :=
      mul_le_mul hπ (mul_le_mul_of_nonneg_left htail hCr)
        (mul_nonneg hCr (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (Real.exp_pos _).le)) (by norm_num)
    _ = _ := by ring

theorem inner_grid_first {Δ : ℝ} {J : ℕ} (hΔ : 0 < Δ) (hJ : 2048 ≤ Δ*J) (k : ℕ) :
    spectralGridSum 1 J k Δ ≤ 0.000182 := by
  apply grid_bound (C := 10.38) (cap := 0.000182) hΔ hJ k
  all_goals first | exact grid_constants.1 | norm_num

theorem inner_grid_second {Δ : ℝ} {J : ℕ} (hΔ : 0 < Δ) (hJ : 2048 ≤ Δ*J) (k : ℕ) :
    spectralGridSum 2 J k Δ ≤ 0.396 := by
  apply grid_bound (C := 11.1) (cap := 0.396) hΔ hJ k
  all_goals first | exact grid_constants.2 | norm_num

end CentralUnimodality
