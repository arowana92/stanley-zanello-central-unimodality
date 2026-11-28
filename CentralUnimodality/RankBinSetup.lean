module

public import CentralUnimodality.RankBinChecks
public import CentralUnimodality.RankBinSurvival
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Match the rational input data with the actual ceiling cuts, standard
deviation and prefix probability at a saddle in the chosen bin. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic
open Real

noncomputable def timeCut (m : ℕ) (v : ℚ) := ⌈(v:ℝ)*m⌉₊
noncomputable def sizeScale (m : ℕ) : ℝ := (m:ℝ)*√m

/-- Geometric coverage for both choices of early cut. -/
theorem cut_geometry {m : ℕ} (hm : 4096 ≤ m) {l : ℚ} (hl : 1/14 ≤ l) (hl' : l ≤ 1/10) :
    let L := timeCut m l
    let T := timeCut m lateCut
    0<L ∧ L<T ∧ T≤m ∧ 3685≤m-L ∧
      (L:ℝ) ≤ ((l+epsilon:ℚ):ℝ)*m ∧ (837/1000)*(m:ℝ) ≤ (T-L:ℕ) := by
  let L := timeCut m l
  let T := timeCut m lateCut
  have hm' : (4096:ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : 0<(m:ℝ) := by linarith
  have h₁ := (Rat.cast_le (K := ℝ)).mpr hl
  have h₂ := (Rat.cast_le (K := ℝ)).mpr hl'
  push_cast at h₁ h₂
  have hlpos : 0<(l:ℝ) := by linarith
  have hL₀ : (l:ℝ)*m ≤ L := Nat.le_ceil _
  have hL₁ : (L:ℝ)<(l:ℝ)*m+1 := Nat.ceil_lt_add_one (by positivity)
  have hT₀ : (15/16:ℝ)*m ≤ T := by
    have H : (lateCut:ℝ)*m ≤ T := Nat.le_ceil _
    simpa [lateCut] using H
  have hTm : T ≤ m := Nat.ceil_le.mpr (by
    change ((15/16:ℚ):ℝ)*m ≤ m; push_cast; linarith)
  have hLpos : 0<L := by
    have H := (mul_pos hlpos hmpos).trans_le hL₀; exact_mod_cast H
  have hf : (L:ℝ) ≤ ((l+epsilon:ℚ):ℝ)*m := by
    push_cast; dsimp [epsilon]; push_cast; linarith
  have hLcap := mul_le_mul_of_nonneg_right h₂ hmpos.le
  have hLT : L<T := by
    have h : (L:ℝ)<T := by linarith only [hL₁,hLcap,hT₀,hm']
    exact_mod_cast h
  have hrs : (3685:ℝ)+L ≤ m := by linarith only [hL₁,hLcap,hm']
  have hrs' : 3685+L ≤ m := by exact_mod_cast hrs
  refine ⟨hLpos,hLT,hTm,by omega,hf,?_⟩
  change _ ≤ ((T-L:ℕ):ℝ)
  rw [Nat.cast_sub hLT.le]
  linarith only [hL₁,hT₀,hLcap,hm']

structure SaddleAt (B : SaddleBin) (m : ℕ) (c : ℝ) : Prop where
  large : 4096 ≤ m
  positive : 0<c
  lower : (B.lower:ℝ) ≤ 2*c*sizeScale m
  upper : 2*c*sizeScale m ≤ B.upper

/-- The positive numeric data are checked at the same bin that supplies
the shifts for the actual first and late events. -/
theorem checked_bin_data {curve : Bool} {i : ℕ} (hc : checkSigns curve i=true) :
    let B := saddleBin curve i
    0 ≤ B.lower ∧ B.lower≤B.upper ∧ B.upper≤25 ∧ 0<B.denom ∧ 0<B.zlo ∧ B.zhi≤259/1000 ∧
      0<B.drift ∧ 0≤B.variance ∧ 1/14 ≤ B.fraction ∧ B.fraction ≤ 1/10 := by
  have H := of_decide_eq_true hc
  change _ ∧ _ at H
  let B := saddleBin curve i
  have hg : 0 ≤ B.lower := by
    dsimp only [B,saddleBin]; cases curve <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> positivity
  refine ⟨hg,H.2.1,H.2.2.1,H.2.2.2.1,H.2.2.2.2.1,H.2.2.2.2.2.1,
    H.2.2.2.2.2.2.1,H.2.2.2.2.2.2.2.1,?_⟩
  cases curve <;> norm_num [saddleBin,binFraction]

theorem bin_actual_scales {curve : Bool} {i m : ℕ} {c : ℝ}
    (hcheck : checkSigns curve i=true) (h : SaddleAt (saddleBin curve i) m c) :
    let B := saddleBin curve i
    let L := timeCut m B.fraction
    let σ := √(suffixVariance c (m-L))
    let P := live c (c*m) L 1
    sizeScale m*B.zlo ≤ σ ∧ σ ≤ sizeScale m*B.zhi ∧ B.denom ≤ P*√m ∧ 0<P ∧
      varianceLimit m c ((B.fraction+epsilon:ℚ):ℝ) σ ≤ B.variance := by
  let B := saddleBin curve i
  let l : ℝ := B.fraction
  let f : ℝ := ((B.fraction+epsilon:ℚ):ℝ)
  let L := timeCut m B.fraction
  let σ := √(suffixVariance c (m-L))
  have ⟨hgn,hgG,hG,hden,hz,_,hk,_,hfrac,hfrac'⟩ := checked_bin_data hcheck
  obtain ⟨_,hLT,hTm,_,hLf,_⟩ := cut_geometry h.large hfrac hfrac'
  have hLm : L ≤ m := hLT.le.trans hTm
  have hM : (4096:ℝ) ≤ m := by exact_mod_cast h.large
  have hmp : 0<(m:ℝ) := by linarith
  have hs : 0 ≤ sizeScale m := by dsimp [sizeScale]; positivity
  have hl₀ : 1/14 ≤ l := by simpa [l,B] using (Rat.cast_le (K := ℝ)).mpr hfrac
  have hl₁ : l ≤ 1/10 := by simpa [l,B] using (Rat.cast_le (K := ℝ)).mpr hfrac'
  have fe : f=l+1/4096 := by dsimp [f,l,epsilon]; push_cast; rfl
  have hf₀ : 0 ≤ f := by linarith only [hl₀,fe]
  have hf₁ : f<1 := by linarith only [hl₁,fe]
  have hG' : (B.upper:ℝ) ≤ 25 := by exact_mod_cast hG
  have hg' : 0 ≤ (B.lower:ℝ) := by exact_mod_cast hgn
  have hGpos : 0 ≤ (B.upper:ℝ) := by exact_mod_cast hgn.trans hgG
  have hlarge : (1-f)*(m:ℝ) ≤ (m-L:ℕ) := by rw [Nat.cast_sub hLm]; change (L:ℝ) ≤ f*m at hLf; linarith
  have hsmall : ((m-L:ℕ):ℝ) ≤ (1-l)*m := by
    have hlc : l*m ≤ L := Nat.le_ceil _
    rw [Nat.cast_sub hLm]; linarith
  have hBcap : (B.upper:ℝ) ≤ 128 := by linarith
  have ls := (bin_suffix_scale h.large h.positive.le h.upper (sub_nonneg.mpr hf₁.le) zero_le_one hlarge
    (show ((m-L:ℕ):ℝ) ≤ 1*m by rw [one_mul]; exact_mod_cast Nat.sub_le m L) (by simpa using hBcap)).1
  have us := (bin_suffix_scale h.large h.positive.le h.upper (sub_nonneg.mpr hf₁.le)
    (show 0≤1-l by linarith) hlarge hsmall (by nlinarith only [hBcap,mul_nonneg hGpos (by linarith : 0 ≤ l)])).2
  let X : ℚ := (1-(B.upper/128)^2)*(1-(B.fraction+epsilon))^3/12
  let Y : ℚ := (1-B.fraction+epsilon)^3/12
  have hX : 0≤X := by
    have hg : B.upper/128 ≤ 1 := by linarith only [hG]
    have hn : 0 ≤ B.upper/128 := by exact div_nonneg (hgn.trans hgG) (by norm_num)
    have hf : 0 ≤ 1-(B.fraction+epsilon) := by dsimp [epsilon]; linarith only [hfrac']
    dsimp [X]; exact div_nonneg (mul_nonneg (by nlinarith only [pow_le_pow_left₀ hn hg 2]) (pow_nonneg hf 3)) (by norm_num)
  have hY : 0≤Y := by
    have h' : 0≤1-B.fraction+epsilon := by dsimp [epsilon]; linarith only [hfrac']
    exact div_nonneg (pow_nonneg h' 3) (by norm_num)
  have lower : sizeScale m*(B.zlo:ℝ) ≤ σ := by
    apply (mul_le_mul_of_nonneg_left (root_enclosure hX).1 hs).trans
    dsimp only [X]
    push_cast
    dsimp only [sizeScale,σ,f] at *
    push_cast at ls
    simpa only [mul_one] using ls
  have upper : σ ≤ sizeScale m*(B.zhi:ℝ) := by
    change σ ≤ sizeScale m*(rootHi Y:ℝ)
    apply le_trans _ (mul_le_mul_of_nonneg_left (root_enclosure hY).2 hs)
    dsimp only [sizeScale,Y,epsilon,l]
    push_cast
    exact us
  obtain ⟨hd,hd',hP,hPpos⟩ := bin_prefix_survival h.large h.positive hg' h.lower h.upper hf₀ hf₁ hLf
  have kd : (B.drift:ℝ)=(B.lower:ℝ)/2*(1-(B.lower:ℝ)^2/(12*4096)) := by
    change ((((B.lower/2*(1-B.lower^2*epsilon/12)):ℚ):ℝ))=_
    dsimp [epsilon]; push_cast; ring
  have den : (B.denom:ℝ)=2*(B.drift:ℝ)*(1-f)/(1+B.upper/128) := by
    change (((2*B.drift*(1-(B.fraction+epsilon))/(1+B.upper/128):ℚ):ℝ))=_
    dsimp only [f]; push_cast; rfl
  refine ⟨lower,upper,den ▸ kd ▸ hP,hPpos,?_⟩
  have hdr : 0<tanh (c*m) := by
    rw [tanh_eq_sinh_div_cosh]; exact div_pos (sinh_pos_iff.mpr (mul_pos h.positive hmp)) (cosh_pos _)
  have HV := bin_prefix_variance hmp hf₀ hf₁ (by exact_mod_cast hz : 0<(B.zlo:ℝ))
    (by exact_mod_cast hk : 0<(B.drift:ℝ)) hdr hd lower (kd ▸ hd')
  apply HV.trans_eq
  let fq := B.fraction+epsilon
  change _ = (((fq+(1+B.upper/128)/(1-fq)*(fq^2+1/(2*B.drift^2)))/(4*B.zlo^2):ℚ):ℝ)
  push_cast; rfl

end CentralUnimodality.MarkedExcursion.BinArithmetic
