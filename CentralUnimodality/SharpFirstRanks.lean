module

public import CentralUnimodality.SharpShortSuffix
public import CentralUnimodality.RankBinSetup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Attach sharp mass and difference bounds to the remaining independent
suffix at each first-hit time, then convert to the common prefix scale. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
open Real

theorem sharp_first_hit_ranks {m d : ℕ} (hm : 4096≤m) (ht : 2*d+1≤m) (hB : 255≤m-(2*d+1))
    {c z γ D v e Q : ℝ} (hc : 0≤c) (hz : 0≤z) (hγ : γ=2*c*sizeScale m)
    (hD : D=2*z*sizeScale m) (hmax : γ+D≤57) (hsmall : γ^2≤6*m) (he : e≤2)
    (hl : v*m≤2*(d:ℝ)+1) (hh : 2*(d:ℝ)+1≤e*m)
    (hQ : exp (D^2*(labelSquares m/(m:ℝ)^3)/8-v*(1-e/2)^2*(γ+D)*(γ*(1-γ^2/(6*m))+D)/8)*
      (∑ w∈hitWords 1 (2*d+1),signMass (c+z) ((c+z)*d) w)≤Q/sizeScale m)
    (r : Fin 3) (k : ℤ) :
    let b := √(suffixVariance (c+z) (m-(2*d+1)))
    b^(r.val+1)*rankChange c z (meanRank c m) m*
      |rankDifference r k (prefixEventSiteMass (c+z) m (2*d+1) (hitWords 1 (2*d+1)))| ≤
      Q/sizeScale m*(shortSharpLimit r:ℝ) := by
  let B := m-(2*d+1)
  let b := √(suffixVariance (c+z) B)
  have hsum : 2*(c+z)*((m:ℝ)*√m)≤57 := by change γ=2*c*((m:ℝ)*√m) at hγ; change D=2*z*((m:ℝ)*√m) at hD; linarith only [hmax,hγ,hD]
  have sites := suffix_label_bounds hm (Nat.sub_le m (2*d+1)) (add_nonneg hc hz) hsum
  have hp (i : ℕ) (hi : i∈Finset.range B) : 49/250≤labelVariance (c+z) (i+1) ∧ labelVariance (c+z) (i+1)≤1/4 :=
    ⟨(by norm_num : (49/250:ℝ)≤(1-(57/128)^2)/4).trans (sites i hi).2.1,(sites i hi).2.2⟩
  have hB' : (0:ℝ)<B := by exact_mod_cast (show 0<B by dsimp [B]; omega)
  have hv := (suffix_variance_bounds _ B (by norm_num : (0:ℝ)≤49/250) hp).1
  have hb : 0<b := sqrt_pos.mpr ((by positivity : 0<(49/250)/3*(B:ℝ)^3).trans_le hv)
  have hlim : 0≤(shortSharpLimit r:ℝ) := by fin_cases r <;> norm_num [shortSharpLimit]
  have inv (j : ℤ) : |rankDifference r j (freeRankMass (c+z) B)|≤(shortSharpLimit r:ℝ)/b^(r.val+1) := by
    apply (le_div_iff₀ (pow_pos hb _)).mpr
    have I := sharp_free_differences hB hb (sq_sqrt (sqrt_pos.mp hb).le).symm hp r j
    simpa only [mul_comm (b^(r.val+1)) _] using I
  have hpow : (sizeScale m)^2=(m:ℝ)^3 := by dsimp [sizeScale]; rw [mul_pow,sq_sqrt (Nat.cast_nonneg _)]; ring
  have H := (first_hit_rank_bin ht hc hz hpow hγ hD hsmall he hl hh r inv k).trans (mul_le_mul_of_nonneg_right hQ (by positivity))
  rw [← mul_div_assoc] at H
  have K := (le_div_iff₀ (pow_pos hb _)).mp H
  change b^(r.val+1)*_*_≤_
  linarith only [K]

theorem scale_first_charge {m : ℕ} {σ b z Z P den Q X A : ℝ} (hm : 0<m)
    (hz : 0<z) (hZ : 0≤Z) (hden : 0<den) (hQ : 0≤Q) (hX : 0≤X) (hA : 0≤A)
    (hσ : 0≤σ) (hP : den≤P*√m) (hlo : sizeScale m*z≤b) (hhi : σ≤sizeScale m*Z)
    (n : ℕ) (h : b^n*X≤Q/sizeScale m*A) :
    σ^n*X≤P/m*((Q/den)*(Z/z)^n*A) := by
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hp := pos_of_mul_pos_left (hden.trans_le hP) (sqrt_nonneg _)
  have hscale : σ≤(Z/z)*b := by
    rw [div_mul_eq_mul_div]; apply (le_div_iff₀ hz).mpr
    linarith only [mul_le_mul_of_nonneg_right hhi hz.le,mul_le_mul_of_nonneg_left hlo hZ]
  have hq : Q/sizeScale m≤P/m*(Q/den) := by
    rw [div_mul_div_comm]
    apply (div_le_div_iff₀ (mul_pos hm' (sqrt_pos.mpr hm')) (mul_pos hm' hden)).mpr
    linarith only [mul_le_mul_of_nonneg_left hP (mul_nonneg hm'.le hQ)]
  have hpow := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hσ hscale n) hX
  rw [mul_pow,mul_assoc] at hpow
  exact hpow.trans ((mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_right hq hA))
    (pow_nonneg (div_nonneg hZ hz.le) n)).trans_eq (by ring))

end CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
