module

public import CentralUnimodality.PeakPrefixMargin
public import CentralUnimodality.PeakLateProbability
public import CentralUnimodality.RankBinExponent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! The reflected two-harmonic estimate pays the actual signed charge for
all first crossings after the late cut, with the tilt stored in each row. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
open Real FrequencyGrid

theorem actual_late_margin {m j : ℕ} {i : Fin 7} {c : ℝ} (h : SaddleAt (tabulated i) m c)
    (hj : meanRank c m=(j+1:ℕ)) :
    let L := timeCut m firstCut
    let T := timeCut m finalCut
    let σ := √(suffixVariance c (m-L))
    let P := live c (c*m) L 1
    σ^2/P*growthDifference c (j+1:ℕ) (eventSiteMass c m (lateHitEvent m T)) ≤ (lateTotal i:ℝ) := by
  let B := tabulated i
  let C := lateBin i
  let L := timeCut m firstCut
  let T := timeCut m finalCut
  let P := live c (c*m) L 1
  let σ := √(suffixVariance c (m-L))
  let s := sizeScale m
  let z := (C.shift:ℝ)/(2*s)
  let a := (C.height:ℝ)
  let cap := (C.cap:ℝ)
  let A := lateHitEvent m T
  have K := checked_growth_budgets i
  obtain ⟨hg,hgg,hG,hd,hzlo,hzh,_,_,_,hx,_⟩ := K.1
  obtain ⟨ha,hc,hau,hcu,hΔ₀,hΔmax,hex⟩ := of_decide_eq_true K.2.1
  have hM : (4096:ℝ)≤m := by exact_mod_cast h.large
  have hm : (0:ℝ)<m := by linarith only [hM]
  have hr := sqrt_pos.mpr hm
  have hr64 : 64≤√(m:ℝ) := (le_sqrt (by norm_num) hm.le).mpr (by linarith only [hM])
  have hs : 0<s := mul_pos hm hr
  have hz : 0≤z := div_nonneg (by exact_mod_cast hΔ₀) (by positivity)
  have hΔ : (C.shift:ℝ)=2*z*sizeScale m := by change (C.shift:ℝ)=2*((C.shift:ℝ)/(2*s))*s; field_simp
  have ⟨lo,hi⟩ := prefix_scales (tabulated_eq i ▸ h) (tabulated_eq i ▸ hG)
  have hden := prefix_denominator (tabulated_eq i ▸ h) (tabulated_eq i ▸ hg) (tabulated_eq i ▸ hx)
  rw [← tabulated_eq] at lo hi hden
  change s*(B.zlo:ℝ)≤σ at lo
  change σ≤s*(B.zhi:ℝ) at hi
  change (B.denom:ℝ)≤P*√m at hden
  have hσ : 0<σ := (mul_pos hs (by exact_mod_cast hzlo)).trans_le lo
  have hP : 0<P := pos_of_mul_pos_left ((show 0<(B.denom:ℝ) by exact_mod_cast hd).trans_le hden) hr.le
  have hgz : 0≤(B.lower:ℝ) := by exact_mod_cast hg
  have hgz' : (B.lower:ℝ)≤9 := by exact_mod_cast hgg.trans hG
  have had : 0<a := by dsimp only [a]; exact_mod_cast ha
  have hca : 0<cap := by dsimp only [cap]; exact_mod_cast hc
  have hσu : σ≤259/1000*sizeScale m := hi.trans (by
    have H := (Rat.cast_le (K:=ℝ)).mpr hzh; push_cast at H
    linarith only [mul_le_mul_of_nonneg_left H hs.le])
  have hhT : (finalCut:ℝ)*m≤T := Nat.le_ceil _
  have hT : T≤m := Nat.ceil_le.mpr (by norm_num [finalCut]; linarith only [hm])
  have hdr : (B.drift:ℝ)=(B.lower:ℝ)/2*(1-(B.lower:ℝ)^2/(12*4096)) := by
    dsimp only [B]; rw [tabulated_eq]
    change ((((bin i).lower/2*(1-(bin i).lower^2*epsilon/12):ℚ):ℝ))=_
    dsimp only [epsilon]; push_cast; ring
  have heqa : lateHeightParameter B.lower C.shift finalCut=a := by
    have e : C.height=(B.drift+C.shift/2)*finalCut*(1-finalCut/2) := rfl
    dsimp only [a,lateHeightParameter]; rw [e]; push_cast; rw [hdr]; ring
  have heqc : ((B.upper:ℝ)+C.shift)/2-a=cap := by
    have e : C.cap=(B.upper+C.shift)/2-C.height := rfl
    dsimp only [cap,a]; rw [e]; push_cast; rfl
  obtain ⟨_,hcond,ex⟩ := late_bin_parameters h.large hT h.positive.le hz hgz h.lower
    (by nlinarith only [pow_le_pow_left₀ hgz hgz' 2]) (by norm_num [finalCut]) (by norm_num [finalCut]) hhT
  have hΔ' : (C.shift:ℝ)=2*z*((m:ℝ)*√m) := hΔ
  rw [← hΔ'] at hcond ex
  change lateHeightParameter B.lower C.shift finalCut/√m*m≤_ at hcond
  change z^2*labelSquares m/2-m*(lateHeightParameter B.lower C.shift finalCut/√m)^2/2=
    (C.shift:ℝ)^2*(labelSquares m/(m:ℝ)^3)/8-(lateHeightParameter B.lower C.shift finalCut)^2/2 at ex
  rw [heqa] at hcond ex
  have hau' : a/√m≤6/25 := (div_le_iff₀ hr).mpr (by
    have H := (Rat.cast_le (K:=ℝ)).mpr hau; push_cast at H; linarith only [H,hr64])
  have hcu' : cap/√m≤6/25 := (div_le_iff₀ hr).mpr (by
    have H := (Rat.cast_le (K:=ℝ)).mpr hcu; push_cast at H; linarith only [H,hr64])
  have harg : (c+z)*m-a/√m≤cap/√m := by
    rw [sub_div' hr.ne',div_le_div_iff_of_pos_right hr]
    have H := h.upper
    change 2*c*((m:ℝ)*√m)≤(B.upper:ℝ) at H
    change (C.shift:ℝ)=2*z*((m:ℝ)*√m) at hΔ
    linarith only [heqc,hΔ,H]
  let E := exp (z^2*labelSquares m/2-m*(a/√m)^2/2)
  have hE : E≤(decay (-C.expo):ℝ) := by
    dsimp only [E]; rw [ex]
    exact late_bin_exponential h.large (a:=C.height) (d:=C.shift) rfl hex
  have hprob := late_prob_bound (C:=C) h.large hd ha hc.le hcu hden (exp_pos _).le hE
  let Q := (lateProb B C:ℝ)
  have H (r : Fin 3) : σ^(r.val+1)*rankChange c z (meanRank c m) m*
      |rankDifference r (j+1:ℕ) (eventSiteMass (c+z) m A)|≤P*(Q*(markedLimit r:ℝ)) := by
    have hu := marked_late_rank_bound h.large h.positive.le hz (div_pos had hr) hau' (div_nonneg hca.le hr.le)
      hcu' harg hcond hσ.le hσu r (j+1:ℕ)
    have hlim : 0≤(markedLimit r:ℝ) := by fin_cases r <;> norm_num [markedLimit]
    exact hu.trans ((mul_le_mul_of_nonneg_right hprob hlim).trans_eq (by ring))
  let Λ := ((B.upper:ℝ)+C.shift)*B.zhi
  have htilt : 2*(c+z)*σ≤Λ := by
    have hu : 2*(c+z)*s≤(B.upper:ℝ)+C.shift := by linarith only [h.upper,hΔ]
    have hzp : 0≤(B.zhi:ℝ) := nonneg_of_mul_nonneg_right (hσ.le.trans hi) hs
    have H₁ := mul_le_mul_of_nonneg_left hi (show 0≤2*(c+z) by linarith only [h.positive,hz])
    dsimp only [Λ]; linarith only [H₁,mul_le_mul_of_nonneg_right hu hzp]
  have V := scaled_growth_event h.positive.le hz (small_rank_shift h.large hz hΔ (by exact_mod_cast hΔmax)) hσ hP htilt A
    (Finset.filter_subset ..) hj (by simpa only [Fin.val_zero,Nat.zero_add,pow_one] using H 0) (H 1)
  apply V.trans (le_trans (le_of_eq _) ((Rat.cast_le (K:=ℝ)).mpr (charge_upper (lateCost B C))))
  dsimp only [lateCost,Q,lateProb,Λ]; push_cast; norm_num [markedLimit]; ring

end CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
