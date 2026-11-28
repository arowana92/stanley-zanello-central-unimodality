module

public import CentralUnimodality.SharpFirstRanks
public import CentralUnimodality.PeakFirstProbability
public import CentralUnimodality.PeakPrefixMargin
public import CentralUnimodality.RankBinFirstGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! For every actual first-hit time and every overlapping time bin, the
recorded cost bounds the restored growth difference at the original tilt. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
open Real

theorem actual_first_cell {m d j : ℕ} {i : Fin 7} {k : ℕ} (hk : k<timeBins i) {c : ℝ}
    (h : SaddleAt (tabulated i) m c) (hj : meanRank c m=(j+1:ℕ))
    (hl : (timeEdge i k:ℝ)*m-1≤2*(d:ℝ)+1) (hh : 2*(d:ℝ)+1≤(timeEdge i (k+1):ℝ)*m+1) :
    let C := timeBin i k
    let L := timeCut m firstCut
    let σ := √(suffixVariance c (m-L))
    let P := live c (c*m) L 1
    ((C.right:ℝ)-C.left)/2*(σ^2/(P/m)*
      growthDifference c (j+1:ℕ) (prefixEventSiteMass c m (2*d+1) (hitWords 1 (2*d+1))))≤
      (timeCost (tabulated i) C:ℝ) := by
  let B := tabulated i
  let C := timeBin i k
  let L := timeCut m firstCut
  let σ := √(suffixVariance c (m-L))
  let P := live c (c*m) L 1
  let s := sizeScale m
  let z := (C.shift:ℝ)/(2*s)
  let u := c+z
  let t := 2*d+1
  let b := √(suffixVariance u (m-t))
  let γ := 2*c*s
  let Q := (earlyProb B C:ℝ)
  let A := (words m).filter (fun w => w.take t∈hitWords 1 t)
  let g := (B.lower:ℝ)
  let G := (B.upper:ℝ)
  have H := checked_growth_budgets i
  have OK := H.2.2.1 ⟨k,hk⟩
  obtain ⟨hg,hgG,hG,hd,hzlo,_,_,_,_,hx,_⟩ := H.1
  obtain ⟨_,hwid,hv₀,_,he,_,_,_,hz',hD,hDmax,hLam,_,_,_,_⟩ := of_decide_eq_true OK
  have hM : (4096:ℝ)≤m := by exact_mod_cast h.large
  have hm : (0:ℝ)<m := by linarith only [hM]
  have hs : 0<s := mul_pos hm (sqrt_pos.mpr hm)
  have hz₀ : 0≤z := div_nonneg (by exact_mod_cast hD) (by positivity)
  have hΔ : (C.shift:ℝ)=2*z*s := by dsimp only [z]; field_simp
  have heq : C.e=C.right+epsilon := rfl
  have hvq : C.v=C.left-epsilon := rfl
  have hlq : C.left≤C.right := hwid.le
  have hright : C.right≤lateCut := (min_le_left ..).trans (by decide +kernel : finalCut+2*epsilon≤lateCut)
  have hel : (C.e:ℝ)≤15/16+1/4096 := by
    rw [heq]; push_cast; simpa [epsilon,lateCut] using add_le_add_right ((Rat.cast_le (K:=ℝ)).mpr hright) (1/4096)
  have hl' : (C.v:ℝ)*m≤2*(d:ℝ)+1 := by
    rw [hvq]; dsimp only [epsilon]; push_cast
    change (C.left:ℝ)*m-1≤_ at hl
    linarith only [hl,hM]
  have hh' : 2*(d:ℝ)+1≤(C.e:ℝ)*m := by
    rw [heq]; dsimp only [epsilon]; push_cast
    change _≤(C.right:ℝ)*m+1 at hh
    linarith only [hh,hM]
  have hvn : 0≤C.v := by change 0<C.v-epsilon at hv₀; dsimp only [epsilon] at hv₀; linarith only [hv₀]
  have hvw : C.v≤C.right := by rw [hvq]; dsimp only [epsilon]; linarith only [hlq]
  have ht : 2*d+1+255≤m := by
    exact_mod_cast (show 2*(d:ℝ)+1+255≤m by linarith only [hh',mul_le_mul_of_nonneg_right hel hm.le,hM])
  have hg' : g≤γ := h.lower
  have hG' : γ≤G := h.upper
  have hg₀ : 0≤γ := by dsimp [γ]; positivity [h.positive]
  have hγ : γ≤25 := hG'.trans ((show G≤9 by dsimp only [G]; exact_mod_cast hG).trans (by norm_num))
  have hlam : (C.lam:ℝ)=G+C.shift := by change ((B.upper+C.shift:ℚ):ℝ)=_; push_cast; rfl
  have hcap : γ+C.shift≤C.lam := by rw [hlam]; linarith only [hG']
  have hu : 2*u*sizeScale m=γ+C.shift := by dsimp only [u,γ,s] at *; linarith only [hΔ]
  have hLam' : (C.lam:ℝ)≤57 := by exact_mod_cast hLam
  have hGmax : G+C.shift≤57 := hlam ▸ hLam'
  have hbase := early_hit_probability h.large (add_nonneg h.positive.le hz₀) B C OK hg hg' hγ rfl rfl hu hcap hl' hh'
  have hQ : 0≤Q := by
    have Hq : 0≤Q/s := (mul_nonneg (exp_pos _).le (Finset.sum_nonneg
      fun w (_ : w∈hitWords 1 (2*d+1)) => (signMass_pos u (u*d) w).le)).trans hbase
    by_contra! hn; exact (not_le_of_gt (div_neg_of_neg_of_pos hn hs)) Hq
  have raw (r : Fin 3) := sharp_first_hit_ranks h.large (by omega : 2*d+1≤m) (by omega)
    h.positive.le hz₀ (show γ=2*c*sizeScale m from rfl) hΔ (hcap.trans hLam')
    (by nlinarith only [pow_le_pow_left₀ hg₀ hγ 2,hM]) (by linarith only [hel]) hl' hh' hbase r (j+1:ℕ)
  obtain ⟨hlo,hhi⟩ := prefix_scales (tabulated_eq i ▸ h) (tabulated_eq i ▸ hG)
  have hprob := prefix_denominator (tabulated_eq i ▸ h) (tabulated_eq i ▸ hg) (tabulated_eq i ▸ hx)
  rw [← tabulated_eq] at hlo hhi hprob
  change s*(B.zlo:ℝ)≤σ at hlo
  change σ≤s*(B.zhi:ℝ) at hhi
  change (B.denom:ℝ)≤P*√m at hprob
  have hσ : 0<σ := (mul_pos hs (by exact_mod_cast hzlo)).trans_le hlo
  have hZ : 0≤(B.zhi:ℝ) := nonneg_of_mul_nonneg_right (hσ.le.trans hhi) hs
  have hdR : 0<(B.denom:ℝ) := by exact_mod_cast hd
  have hP : 0<P := pos_of_mul_pos_left (hdR.trans_le hprob) (sqrt_nonneg _)
  have hZ' : 0<(C.z:ℝ) := by exact_mod_cast hz'
  have hitScale : s*(C.z:ℝ)≤b := hit_suffix_scale h.large h.positive.le hz₀ rfl hΔ hG' hGmax hvn hvw hright heq hl' hh' (by omega) hlam rfl
  let ratio := (B.zhi:ℝ)/(C.z:ℝ)
  let V (r : Fin 3) := Q/(B.denom:ℝ)*ratio^(r.val+1)*(shortSharpLimit r:ℝ)
  have hrow (v : ℝ) : eventSiteMass v m A=prefixEventSiteMass v m t (hitWords 1 t) := by
    funext x; simp [eventSiteMass,prefixEventSiteMass,A]
  have bound (r : Fin 3) : σ^(r.val+1)*rankChange c z (meanRank c m) m*
      |rankDifference r (j+1:ℕ) (eventSiteMass u m A)|≤P/m*V r := by
    rw [mul_assoc]
    apply scale_first_charge (by exact_mod_cast hm) hZ' hZ hdR hQ (mul_nonneg (rankChange_pos ..).le (abs_nonneg _))
      (by fin_cases r <;> norm_num [shortSharpLimit]) hσ.le hprob hitScale hhi
    rw [hrow]; simpa only [mul_assoc] using raw r
  have hΛ : 2*(c+z)*σ≤(C.lam:ℝ)*B.zhi := by
    have H₁ := mul_le_mul_of_nonneg_left hhi (show 0≤2*(c+z) by linarith only [h.positive,hz₀])
    have H₂ : 2*(c+z)*s≤C.lam := hu.le.trans hcap
    linarith only [H₁,mul_le_mul_of_nonneg_right H₂ hZ]
  have U := scaled_growth_event h.positive.le hz₀ (small_rank_shift h.large hz₀ hΔ (by exact_mod_cast hDmax)) hσ
    (div_pos hP hm) hΛ A (Finset.filter_subset ..) hj (by simpa only [Fin.val_zero,Nat.zero_add,pow_one] using bound 0) (bound 1)
  rw [hrow] at U
  have hwR : (C.left:ℝ)<C.right := (Rat.cast_lt (K:=ℝ)).mpr hwid
  apply (mul_le_mul_of_nonneg_left U (div_nonneg (sub_nonneg.mpr hwR.le) (by norm_num : (0:ℝ)≤2))).trans_eq
  dsimp only [V,ratio,Q,earlyProb,timeCost,hitFactor]; push_cast
  norm_num [shortSharpLimit]; field_simp; ring

end CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
