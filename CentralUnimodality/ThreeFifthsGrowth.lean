module

public import CentralUnimodality.PeakTimeSum
public import CentralUnimodality.PeakLateCharge
public import CentralUnimodality.UpperHalfGrowth
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Strict adjacent growth from the midpoint through corank three fifths
of the Brownian scale, for every length m ≥ 4096 and either parity. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
open Real

theorem bin_strict_growth {m j : ℕ} {i : Fin 7} {c : ℝ} (h : SaddleAt (tabulated i) m c)
    (hj : meanRank c m=(j+1:ℕ)) : rankCount m (j+1)<rankCount m (j+2) := by
  let B := tabulated i
  let L := timeCut m firstCut
  let T := timeCut m finalCut
  let σ := √(suffixVariance c (m-L))
  let P := live c (c*m) L 1
  have H := checked_growth_budgets i
  obtain ⟨hg,_,hG,hd,hz,_,_,_,_,hx,_⟩ := H.1
  have hm : (0:ℝ)<m := by have hh := h.large; exact_mod_cast (show 0<m by omega)
  have hs : 0<sizeScale m := mul_pos hm (sqrt_pos.mpr hm)
  have hscale := (prefix_scales (tabulated_eq i ▸ h) (tabulated_eq i ▸ hG)).1
  have hden := prefix_denominator (tabulated_eq i ▸ h) (tabulated_eq i ▸ hg) (tabulated_eq i ▸ hx)
  rw [← tabulated_eq] at hscale hden
  have hσ : 0<σ := (mul_pos hs (by exact_mod_cast hz)).trans_le hscale
  have hP : 0<P := pos_of_mul_pos_left ((show 0<(B.denom:ℝ) by exact_mod_cast hd).trans_le hden) (sqrt_nonneg _)
  have hLT : L≤T := Nat.ceil_mono (mul_le_mul_of_nonneg_right (by norm_num [firstCut,finalCut] : (firstCut:ℝ)≤finalCut) hm.le)
  have hT : T≤m := Nat.ceil_le.mpr (by norm_num [finalCut]; linarith only [hm])
  have gap : earlyTotal i+lateTotal i<prefixMargin B := by linarith only [H.2.2.2]
  have hgR := (Rat.cast_lt (K:=ℝ)).mpr gap
  rw [Rat.cast_add] at hgR
  exact growth_from_hit_margins hLT hT (div_pos (sq_pos_of_pos hσ) hP) hgR
    (prefix_actual_margin h hj) (all_first_charges h hj) (actual_late_margin h hj)

private theorem covering_edges (e : ℕ→ℝ) {x : ℝ} (h₀ : e 0≤x) (n : ℕ) (hn : x≤e (n+1)) :
    ∃ k≤n,e k≤x ∧ x≤e (k+1) := by
  induction n with
  | zero => exact ⟨0,le_rfl,h₀,hn⟩
  | succ n IH =>
    by_cases h : x≤e (n+1)
    · obtain ⟨k,hk,l,r⟩ := IH h
      exact ⟨k,hk.trans (Nat.le_succ _),l,r⟩
    · exact ⟨n+1,le_rfl,(lt_of_not_ge h).le,hn⟩

theorem peak_cover {γ : ℝ} (hl : (1199/100)*(3/5)≤γ) (hu : γ≤(1199/100)*(3/4)) :
    ∃ i : Fin 7, ((tabulated i).lower:ℝ)≤γ ∧ γ≤((tabulated i).upper:ℝ) := by
  have h₀ : (edge 0:ℝ)≤γ := by simpa [edge] using hl
  have h₇ : γ≤(edge 7:ℝ) := by simpa [edge] using hu
  obtain ⟨k,hk,l,r⟩ := covering_edges (fun j => (edge j:ℝ)) h₀ 6 h₇
  let i : Fin 7 := ⟨k,by omega⟩
  refine ⟨i,?_⟩
  rw [tabulated_eq]
  exact ⟨l,r⟩

theorem growth_three_fifths_to_two {m j : ℕ} (hm : 4096≤m) (hj : j+1≤staircaseDegree m)
    (hl : (3/5)*sizeScale m≤(staircaseDegree m:ℝ)-(j+1))
    (hu : (staircaseDegree m:ℝ)-(j+1)≤2*sizeScale m) : rankCount m (j+1)<rankCount m (j+2) := by
  obtain ⟨c,_,he,h₁,h₂⟩ := saddle_rank hm hj (by simpa only [sizeScale,Nat.cast_add,Nat.cast_one] using hu)
  let γ := 2*c*sizeScale m
  have hs : 0<sizeScale m := by
    have hp : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
    exact mul_pos hp (sqrt_pos.mpr hp)
  have hlow : (1199/100)*(3/5)≤γ := by
    apply le_of_mul_le_mul_right (a:=sizeScale m) _ hs
    change _≤γ*sizeScale m at h₁
    push_cast at h₁
    linarith only [hl,h₁]
  have hc : 0<c := by
    by_contra! h
    have hγ : γ≤0 := mul_nonpos_of_nonpos_of_nonneg (by linarith only [h]) hs.le
    linarith only [hlow,hγ]
  by_cases H : γ≤(1199/100)*(3/4)
  · obtain ⟨i,l,r⟩ := peak_cover hlow H
    exact bin_strict_growth (i:=i) ⟨hm,hc,l,r⟩ he
  · have hl' : (1199/100)*(corankStart false:ℝ)≤γ := by simpa [corankStart] using (lt_of_not_ge H).le
    obtain ⟨i,hi,l,r⟩ := checked_cover false hl' h₂.le
    exact certified_bin_sign (curve:=false) hi ⟨hm,hc,l,r⟩ he normal_height_bounds.1

/-- The midpoint condition and lower cutoff refer to the lower integer
rank j+1. No finite maximum length or rank sampling enters the theorem. -/
theorem upper_half_three_fifths {m j : ℕ} (hm : 4096≤m) (hmid : staircaseDegree m≤2*(j+1))
    (hj : j+1≤staircaseDegree m) (hl : (3/5)*sizeScale m≤(staircaseDegree m:ℝ)-(j+1)) :
    rankCount m (j+1)<rankCount m (j+2) := by
  by_cases H : (staircaseDegree m:ℝ)-(j+1)≤2*sizeScale m
  · exact growth_three_fifths_to_two hm hj hl H
  · exact far_corank_growth hm hmid hj (lt_of_not_ge H).le

end CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
