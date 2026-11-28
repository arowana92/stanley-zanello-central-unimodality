module

public import CentralUnimodality.SaddleRank
import Mathlib.Analysis.Complex.ExponentialBounds

/-! A saddle for every rank from the real midpoint to the staircase
degree, including coranks beyond twice the Brownian scale. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real Set

private theorem drift_at_one : 19/25 ≤ tanh 1 := by
  have hp := exp_pos 1
  have he : (2718/1000:ℝ) ≤ exp 1 := by linarith only [exp_one_gt_d9]
  rw [tanh_eq,exp_neg]
  apply (le_div_iff₀ (by positivity)).mpr
  field_simp
  nlinarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2718/1000) he 2]

theorem upper_half_drift {u : ℝ} (hu : 0 ≤ u) (hcap : u ≤ 1) :
    (19/25)*u ≤ tanh u := by
  have H := (mul_le_mul_of_nonneg_left drift_at_one hu).trans (tanh_chord (by norm_num) hu hcap)
  simpa only [mul_one,one_mul,mul_comm u] using H

theorem mean_rank_chord {m : ℕ} (hm : 0<m) {u : ℝ} (hu : 0 ≤ u) :
    tanh u/(2*m)*labelSquares m ≤ meanRank 0 m-meanRank (u/m) m := by
  have hp : 0<(m:ℝ) := by exact_mod_cast hm
  have series (v : ℝ) :
      meanRank v m = ∑ i ∈ Finset.range m, ((m:ℝ)-i)*(1-tanh (v*(m-i)))/2 :=
    reverse_labels m (fun r => r*(1-tanh (v*r))/2)
  rw [series,series,← Finset.sum_sub_distrib,← sum_labelSquares,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  let a := (m:ℝ)-i
  have ha : 0 ≤ a := sub_nonneg.mpr (by exact_mod_cast (Finset.mem_range.mp hi).le)
  have hcap : a ≤ (m:ℝ) := sub_le_self _ (Nat.cast_nonneg _)
  have hh := tanh_chord hu (div_nonneg ha hp.le) ((div_le_one hp).mpr hcap)
  have eq : a/m*u=u/m*a := by ring
  rw [eq] at hh
  simp only [zero_mul,tanh_zero,sub_zero,mul_one]
  change tanh u/(2*m)*a^2 ≤ a/2-a*(1-tanh (u/m*a))/2
  have hstep := mul_le_mul_of_nonneg_left hh ha
  simp only [div_eq_mul_inv] at hstep ⊢
  linear_combination (1/2:ℝ)*hstep

/-- The scaled tilt is at least 11.9 times the scaled corank, and the
largest one-step natural parameter is strictly below one. -/
theorem upper_half_saddle {m j : ℕ} (hm : 770 ≤ m) (hmid : staircaseDegree m ≤ 2*j)
    (hmax : j ≤ staircaseDegree m) :
    ∃ c : ℝ, 0 ≤ c ∧ meanRank c m=j ∧ c*m<1 ∧
      (119/10)*((staircaseDegree m:ℝ)-j) ≤ (2*c*((m:ℝ)*√m))*((m:ℝ)*√m) := by
  have hM : (770:ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0<(m:ℝ) := by linarith
  have hD := degree_offset m
  have hmj : (staircaseDegree m:ℝ) ≤ 2*j := by exact_mod_cast hmid
  have hupper : (j:ℝ) ≤ meanRank 0 m := by
    have hj : (j:ℝ) ≤ staircaseDegree m := by exact_mod_cast hmax
    linarith only [hj,hD.1]
  have H := mean_rank_chord (by omega : 0<m) (by norm_num : (0:ℝ) ≤ 1)
  have hQ : 0 ≤ labelSquares m := by dsimp [labelSquares]; positivity
  have hbound := (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right drift_at_one (by positivity)) hQ).trans H
  have he : (19/25:ℝ)/(2*m)*labelSquares m=(19/300)*(m+1)*(2*m+1) := by
    dsimp [labelSquares]; field_simp; ring
  rw [he,meanRank_zero] at hbound
  have hd := hD.2
  rw [meanRank_zero] at hd
  have hlow : meanRank (1/m) m < j := by
    nlinarith only [hbound,hmj,hd,hM,mul_nonneg (sub_nonneg.mpr hM) hp.le]
  obtain ⟨c,hc,hj⟩ := intermediate_value_Icc' (by positivity : (0:ℝ)≤1/m)
    (meanRank_continuous m).continuousOn
    (show (j:ℝ) ∈ Icc (meanRank (1/m) m) (meanRank 0 m) from ⟨hlow.le,hupper⟩)
  change meanRank c m=j at hj
  have hc' : c<1/m := lt_of_le_of_ne hc.2 (by rintro rfl; linarith only [hj,hlow])
  have hQscale : (119/10:ℝ)*labelSquares m ≤ 4*(m:ℝ)^3 := by
    have h₁ : (m:ℝ)+1 ≤ (771/770)*m := by linarith only [hM]
    have h₂ : 2*(m:ℝ)+1 ≤ (1541/770)*m := by linarith only [hM]
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul h₁ h₂ (by positivity) (by positivity)) hp.le
    dsimp [labelSquares]; nlinarith only [hh,pow_nonneg hp.le 3]
  have hu := (meanRank_displacement hc.1 m).2
  rw [hj] at hu
  refine ⟨c,hc.1,hj,(lt_div_iff₀ hp).mp hc',?_⟩
  have hs : ((m:ℝ)*√m)^2=(m:ℝ)^3 := by rw [mul_pow,sq_sqrt hp.le]; ring
  rw [mul_assoc (2*c),← sq,hs]
  nlinarith only [hu,hD.1,mul_le_mul_of_nonneg_left hQscale hc.1]

end CentralUnimodality.MarkedExcursion
