module

public import CentralUnimodality.PeakGrowthChecks
public import CentralUnimodality.PeakPrefixScales
public import CentralUnimodality.PeakGaussianSlope
public import CentralUnimodality.PeakGrowthTransfer
public import CentralUnimodality.RankBinGaussian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! The exact computed prefix margin bounds the true single-step growth
charge for all lengths and integer saddle sites in each of seven bins. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
open Real

theorem prefix_actual_margin {m j : ℕ} {i : Fin 7} {c : ℝ} (h : SaddleAt (tabulated i) m c)
    (hj : meanRank c m=(j+1:ℕ)) :
    let B := tabulated i
    let L := timeCut m firstCut
    let σ := √(suffixVariance c (m-L))
    let P := live c (c*m) L 1
    (prefixMargin B:ℝ) ≤ σ^2/P*growthDifference c (j+1:ℕ) (prefixSiteMass c m L) := by
  have hb := (checked_growth_budgets i).1
  rw [tabulated_eq] at h hb ⊢
  let B := bin i
  let L := timeCut m firstCut
  let f := firstCut+epsilon
  let σ := √(suffixVariance c (m-L))
  let P := live c (c*m) L 1
  let A := prefixSiteMass c m L
  let k : ℤ := (j+1:ℕ)
  obtain ⟨hg,_,hG,hd,hz,_,hκ,hV,hvCap,hx,hpos⟩ := hb
  have hM : (4096:ℝ)≤m := by exact_mod_cast h.large
  have hm : (0:ℝ)<m := by linarith
  have hmn : 0<m := by exact_mod_cast hm
  have hr := sqrt_pos.mpr hm
  have hr64 : 64≤√(m:ℝ) := (le_sqrt (by norm_num) hm.le).mpr (by linarith only [hM])
  have hs : 262144≤sizeScale m := by dsimp [sizeScale]; nlinarith only [mul_le_mul hM hr64 (by norm_num) hm.le]
  have ⟨_,hlt,htm,hfree,hLf,_⟩ := cut_geometry h.large (show 1/14≤firstCut by decide +kernel) (show firstCut≤1/10 by decide +kernel)
  have hLm : L≤m := hlt.le.trans htm
  have hG' : (B.upper:ℝ)≤9 := by exact_mod_cast hG
  have hg' : 0≤(B.lower:ℝ) := by exact_mod_cast hg
  have hd' : 0<(B.denom:ℝ) := by exact_mod_cast hd
  have hz' : 0<(B.zlo:ℝ) := by exact_mod_cast hz
  have hk' : 0<(B.drift:ℝ) := by exact_mod_cast hκ
  have hV' : 0≤(B.variance:ℝ) := by exact_mod_cast hV
  have hzlo := (prefix_scales h hG).1
  change sizeScale m*(B.zlo:ℝ)≤σ at hzlo
  have hσ : 0<σ := (mul_pos (by linarith only [hs]) hz').trans_le hzlo
  have hden := prefix_denominator h hg hx
  have hP : 0<P := pos_of_mul_pos_left (hd'.trans_le hden) hr.le
  have eqκ : (B.drift:ℝ)=(B.lower:ℝ)/2*(1-(B.lower:ℝ)^2/(12*4096)) := by
    change (((B.lower/2*(1-B.lower^2*epsilon/12):ℚ):ℝ))=_
    dsimp [epsilon]; push_cast; ring
  have hk : (B.drift:ℝ)≤tanh (c*m)*√m := by rw [eqκ,mul_comm (tanh (c*m))]; exact bin_drift_lower h.large hg' h.lower
  have hgU : 2*(c*m)*√m≤(B.upper:ℝ) := by
    simpa only [sizeScale,mul_assoc] using h.upper
  have H := normalized_occupation_variance hmn hLm h.positive.le (mul_pos h.positive hm) hz'
    (by norm_num [f,firstCut,epsilon] : 0≤(f:ℝ)) hk' hd' hLf hgU hk hden hzlo
  let raw := (f*B.upper+1/B.drift)/(4*B.zlo^2*B.denom)
  have cmp := (Rat.cast_le (K:=ℝ)).mpr (charge_upper raw)
  change (raw:ℝ)≤(B.variance:ℝ) at cmp
  have var : _≤(B.variance:ℝ) := H.trans (le_trans (le_of_eq (by dsimp only [raw]; push_cast; ring)) cmp)
  have hup : 2*c*sizeScale m≤9 := h.upper.trans hG'
  have hVσ : suffixVariance c (m-L)=σ^2 := (sq_sqrt ((sqrt_pos.mp hσ).le : 0≤suffixVariance c (m-L))).symm
  have approx := right_free_suffix h.large hfree (Nat.sub_le m L) h.positive.le (hup.trans (by norm_num)) hσ hVσ
  have ⟨mass,slope⟩ := prefix_growth_gaussian hLm hσ hP var approx (j:=k) (by exact_mod_cast hj)
  let M : ℝ := (3989/10000)*(B.gaussian:ℝ)-5/1000
  let J : ℝ := (399/1000)*(406/1000+293/1000*(B.variance:ℝ))+7/1000
  have hM₀ : 0≤M := by
    have hh := (Rat.cast_nonneg (K:=ℝ)).mpr hpos
    push_cast at hh; exact hh
  have hex := lowerExp_le hvCap
  change (B.gaussian:ℝ)≤exp (-((B.variance/2:ℚ):ℝ)) at hex
  push_cast at hex
  rw [← neg_div] at hex
  have hmarg : P*M≤σ*A k := by
    apply le_trans _ mass
    apply mul_le_mul_of_nonneg_left _ hP.le
    dsimp only [M]
    linarith only [mul_le_mul_of_nonneg_left hex (by norm_num : (0:ℝ)≤3989/10000),
      mul_le_mul_of_nonneg_right normal_height_bounds.1 (exp_pos (-(B.variance:ℝ)/2)).le]
  have hsl : -P*J≤σ^2*(A (k+1)-A k) := by
    apply le_trans _ slope
    apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hP.le)
    dsimp only [J]
    linarith only [mul_le_mul_of_nonneg_right normal_height_bounds.2
      (show 0≤406/1000+293/1000*(B.variance:ℝ) by positivity)]
  have hsmall : 2*c≤1/1000 := by
    linarith only [mul_le_mul_of_nonneg_left hs (show 0≤2*c by linarith only [h.positive]),hup]
  let u := 1-exp (-2*c)
  have hstep := tiny_tilt_step (show 0≤2*c by linarith only [h.positive]) hsmall
  rw [← neg_mul] at hstep
  have hu : 0≤u := (by linarith only [h.positive] : (0:ℝ)≤999/1000*(2*c)).trans hstep
  have factor : (999/1000)*(B.lower:ℝ)*(B.zlo:ℝ)≤σ*u := by
    linarith only [mul_le_mul_of_nonneg_left hstep hσ.le,mul_le_mul_of_nonneg_right hzlo h.positive.le,
      mul_le_mul_of_nonneg_right h.lower hz'.le]
  let pre := (999/1000)*B.lower*B.zlo*((3989/10000)*B.gaussian-5/1000)-
    (399/1000)*(406/1000+(293/1000)*B.variance)-7/1000
  apply ((Rat.cast_le (K:=ℝ)).mpr (lowerGrid_le pre)).trans
  change (pre:ℝ)≤σ^2/P*(A (k+1)-exp (-2*c)*A k)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hP).mpr
  have charge₀ := mul_le_mul_of_nonneg_left hmarg (mul_nonneg hσ.le hu)
  have charge₁ := mul_le_mul_of_nonneg_right factor (mul_nonneg hP.le hM₀)
  dsimp only [pre]; push_cast
  dsimp only [M,J,u] at charge₀ charge₁ hsl
  linarith only [charge₀,charge₁,hsl]

end CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
