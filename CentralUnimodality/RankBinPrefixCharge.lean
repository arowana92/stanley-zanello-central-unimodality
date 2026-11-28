module

public import CentralUnimodality.RankBinSetup
public import CentralUnimodality.RankBinGaussian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Compare the surviving-prefix saddle law to the same rational margin
used in the nine growth rows and seven curvature rows. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic
open Real

def binCentral (B : SaddleBin) := B.variance/(1+B.variance/2)-B.gaussian

def binPrefix (B : SaddleBin) (r : Fin 3) : ℚ :=
  if r=0 then (3989/10000)*B.gaussian-5/1000
  else if r=1 then -(1/4) else -((3989/10000)*binCentral B+10/1000)

theorem bin_prefix_margins {curve : Bool} {i m j : ℕ} {c : ℝ}
    (hcheck : checkSigns curve i=true) (h : SaddleAt (saddleBin curve i) m c)
    (hj : meanRank c m=(j+1:ℕ)) (hN : 3989/10000 ≤ normalHeight) (r : Fin 3) :
    let B := saddleBin curve i
    let L := timeCut m B.fraction
    let σ := √(suffixVariance c (m-L))
    let P := live c (c*m) L 1
    (binPrefix B r:ℝ) ≤ σ^(r.val+1)/P*signedRank r (j+1:ℕ) (prefixSiteMass c m L) := by
  let B := saddleBin curve i
  let L := timeCut m B.fraction
  let f := ((B.fraction+epsilon:ℚ):ℝ)
  let σ := √(suffixVariance c (m-L))
  let V := varianceLimit m c f σ
  have ⟨_,_,hG,_,_,_,_,hvar,hl,hl'⟩ := checked_bin_data hcheck
  have hcheck' := of_decide_eq_true hcheck
  have hcenter : binCentral B<0 := hcheck'.2.2.2.2.2.2.2.2.2.1
  have ⟨_,_,_,hM,hLf,_⟩ := cut_geometry h.large hl hl'
  have ⟨_,_,_,_,hV⟩ := bin_actual_scales hcheck h
  have hflo : (0:ℚ) ≤ B.fraction+epsilon := by dsimp [epsilon]; linarith only [hl]
  have hfhi : B.fraction+epsilon<1 := by dsimp [epsilon]; linarith only [hl']
  have hf : 0 ≤ f := (Rat.cast_nonneg (K:=ℝ)).mpr hflo
  have hf' : f<1 := by simpa only [Rat.cast_one] using (Rat.cast_lt (K:=ℝ)).mpr hfhi
  have hd : 0 ≤ tanh (c*m) := by
    rw [tanh_eq_sinh_div_cosh]; exact div_nonneg (sinh_nonneg_iff.mpr (mul_nonneg h.positive.le (Nat.cast_nonneg _))) (cosh_pos _).le
  have hV₀ : 0 ≤ V := by
    have hfn : 0 ≤ 1-f := sub_nonneg.mpr hf'.le
    dsimp only [V,varianceLimit]; positivity
  have ⟨H₀,H₂⟩ := bin_gaussian_comparison hV₀ (by exact_mod_cast hvar : 0 ≤ (B.variance:ℝ)) hV
  have he : (B.gaussian:ℝ)=1-(B.variance:ℝ)/2+((B.variance:ℝ)/2)^2/2-((B.variance:ℝ)/2)^3/6 := by
    change (((1-B.variance/2+(B.variance/2)^2/2-(B.variance/2)^3/6):ℚ):ℝ)=_
    push_cast; rfl
  rw [← he] at H₀ H₂
  have hctr : (binCentral B:ℝ)=(B.variance:ℝ)/(1+(B.variance:ℝ)/2)-B.gaussian := by
    dsimp only [binCentral]; push_cast; rfl
  rw [← hctr] at H₂
  have hctr' : (binCentral B:ℝ) ≤ 0 := by exact_mod_cast hcenter.le
  have HH := (mul_le_mul_of_nonneg_left H₂ (by linarith only [hN] : 0 ≤ normalHeight)).trans
    (mul_le_mul_of_nonpos_right hN hctr')
  have hlim : 2*c*((m:ℝ)*√m) ≤ 25 := h.upper.trans (by exact_mod_cast hG)
  have hj' : meanRank c m=((j+1:ℕ):ℤ) := by exact_mod_cast hj
  have H := prefix_signed_margins h.large hM h.positive hlim hf hf' hLf hj' r
  apply le_trans _ H
  fin_cases r
  · change (((3989/10000*B.gaussian-5/1000):ℚ):ℝ) ≤ 3989/10000*exp (-V/2)-5/1000
    push_cast; linarith only [H₀]
  · norm_num [binPrefix]
  · change (((-(3989/10000*binCentral B+10/1000)):ℚ):ℝ) ≤ -(normalHeight*(V/(1+V/2)-exp (-V/2))+10/1000)
    push_cast; linarith only [HH]

end CentralUnimodality.MarkedExcursion.BinArithmetic
