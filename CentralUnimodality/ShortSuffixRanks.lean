module

public import CentralUnimodality.ShortSuffixEnvelope
public import CentralUnimodality.FirstHitRankMixture
import Mathlib.Analysis.Real.Pi.Bounds

/-! Unrestricted suffix bounds at all ranks after an early first hit, and
their insertion into the rank-resolved first-hit time-bin estimate. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real MeasureTheory Set

/-- Constants for the mass, forward difference and centered second difference. -/
noncomputable def shortSuffixLimit (r : Fin 3) : ℝ := if r=2 then 14/25 else 23/50

private theorem box_integral {T : ℝ} (hT : 0 ≤ T) (C : ℝ) (r : ℕ) :
    Integrable (frequencyBox T C r) ∧ (∫ x, frequencyBox T C r x) = 2*T^(r+1)*C := by
  unfold frequencyBox
  constructor
  · rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  · rw [integral_indicator_const _ measurableSet_Icc,Real.volume_real_Icc_of_le (by linarith),smul_eq_mul,pow_succ]
    ring

private theorem envelope_budget {B : ℝ} (hB : 255 ≤ B) (r : Fin 3) :
    Integrable (shortEnvelope B r.val) ∧ (∫ x, shortEnvelope B r.val x) ≤ (2*π)*shortSuffixLimit r := by
  have hr : r.val ≤ 2 := by omega
  have h₀ := momentKernel_integrable (b := 9/20) (by norm_num) r.val
  obtain ⟨h₁,i₁⟩ := laplaceShoulders_integral 4
  obtain ⟨h₂,i₂⟩ := laplaceShoulders_integral 8
  obtain ⟨h₃,i₃⟩ := box_integral (by linarith only [hB] : 0 ≤ 32*B/15) (exp (-(49/500)*B)) r.val
  obtain ⟨h₄,i₄⟩ := box_integral (by positivity : 0 ≤ 4*B^2) (exp (-(147/800)*B)) r.val
  have hu := h₁.const_mul (16/250)
  have hv := h₂.const_mul (64/100000)
  refine ⟨(((h₀.add hu).add hv).add h₃).add h₄,?_⟩
  unfold shortEnvelope
  rw [integral_add (f := fun x => _+_+_+_) (((h₀.add hu).add hv).add h₃) h₄,
    integral_add (f := fun x => _+_+_) ((h₀.add hu).add hv) h₃,
    integral_add (f := fun x => _+_) (h₀.add hu) hv,integral_add h₀ hu,integral_const_mul,integral_const_mul,
    i₁,i₂,i₃,i₄]
  obtain ⟨hb₁,hb₂⟩ := short_outer_budgets hB r.val hr
  have H := add_le_add (add_le_add (le_refl (absoluteGaussianMoment (9/20) r.val+16/250*2+64/100000*2)) hb₁) hb₂
  apply H.trans
  obtain ⟨G₀,G₁,G₂⟩ := inner_gaussian_low_moments
  fin_cases r <;> norm_num [shortSuffixLimit] <;> linarith only [pi_gt_d2,G₀,G₁,G₂]

/-- An integrable envelope on the normalized frequency line bounds the
scaled integer difference, with the exact Jacobian and lattice span. -/
theorem free_difference_of_envelope (c : ℝ) (B : ℕ) {σ : ℝ} (hσ : 0 < σ) (r : Fin 3)
    {g : ℝ → ℝ} (hg : Integrable g) (hb : ∀ x : ℝ, ‖bandTransform c B (x/σ)‖*|x|^r.val ≤ g x) (k : ℤ) :
    σ^(r.val+1)*|rankDifference r k (freeRankMass c B)| ≤ (∫ x, g x)/(2*π) := by
  have hgi := (MeasureTheory.integrable_comp_mul_left_iff g hσ.ne').mpr hg
  have hb' (θ : ℝ) : ‖bandTransform c B θ‖*|θ|^r.val ≤ (σ^r.val)⁻¹*g (σ*θ) := by
    have H := hb (σ*θ)
    rw [mul_div_cancel_left₀ _ hσ.ne',abs_mul,abs_of_pos hσ,mul_pow] at H
    rw [← div_eq_inv_mul,le_div_iff₀ (pow_pos hσ _)]
    linarith only [H]
  have hi (j : ℤ) := band_integrable c B (g := fun θ => phase (-θ*((j:ℝ)-meanRank c B))) (by unfold phase; fun_prop)
  have H := lattice_difference_integral (bandTransform c B) (meanRank c B)
    (fun j => (2*π)*freeRankMass c B j) hi (band_inverse c B) r k (hgi.const_mul _) hb'
  have he : (fun j => (2*π)*freeRankMass c B j)=(2*π) • freeRankMass c B := rfl
  rw [he,map_smul,smul_eq_mul,abs_mul,abs_of_pos (by positivity : 0 < 2*π),
    integral_const_mul,Measure.integral_comp_mul_left,abs_of_pos (inv_pos.mpr hσ),smul_eq_mul] at H
  rw [le_div_iff₀ (by positivity)]
  field_simp at H
  rw [pow_succ]
  linarith only [H]

/-- Whenever the B≥255 remaining sites have label variances at least .196,
all three rank bounds hold for their true positive variance σ². -/
theorem short_free_differences {B : ℕ} (hB : 255 ≤ B) {c σ : ℝ} (hσ : 0 < σ) (hV : suffixVariance c B=σ^2)
    (hp : ∀ i ∈ Finset.range B, 49/250 ≤ labelVariance c (i+1) ∧ labelVariance c (i+1) ≤ 1/4)
    (r : Fin 3) (k : ℤ) : |rankDifference r k (freeRankMass c B)| ≤ shortSuffixLimit r/σ^(r.val+1) := by
  have hr : r.val ≤ 2 := by omega
  have hB' : (255:ℝ) ≤ B := by exact_mod_cast hB
  obtain ⟨hi,H⟩ := envelope_budget hB' r
  have K := free_difference_of_envelope c B hσ r hi (short_suffix_envelope B hB hσ hV hp r.val hr) k
  rw [le_div_iff₀ (pow_pos hσ _),mul_comm]
  exact K.trans ((div_le_iff₀ (by positivity)).mpr (by linarith only [H]))

/-- The rank-resolved early-hit bin has its explicit .46, .46 and .56
constants for every admissible changed tilt and every integer rank. -/
theorem first_hit_rank_bound {m d : ℕ} (hm : 4096 ≤ m) (ht : 2*d+1 ≤ m) (hB : 255 ≤ m-(2*d+1))
    {c z γ Δ v e : ℝ} (hc : 0 ≤ c) (hz : 0 ≤ z)
    (hγ : γ=2*c*((m:ℝ)*√m)) (hΔ : Δ=2*z*((m:ℝ)*√m)) (hmax : γ+Δ ≤ 57)
    (hsmall : γ^2 ≤ 6*m) (he : e ≤ 2) (hlo : v*m ≤ 2*(d:ℝ)+1) (hhi : 2*(d:ℝ)+1 ≤ e*m)
    (r : Fin 3) (k : ℤ) :
    let B := m-(2*d+1)
    let σ := √(suffixVariance (c+z) B)
    rankChange c z (meanRank c m) m *
      |rankDifference r k (prefixEventSiteMass (c+z) m (2*d+1) (hitWords 1 (2*d+1)))| ≤
      exp (Δ^2*(labelSquares m/(m:ℝ)^3)/8 - v*(1-e/2)^2*(γ+Δ)*(γ*(1-γ^2/(6*m))+Δ)/8) *
        (∑ w ∈ hitWords 1 (2*d+1), signMass (c+z) ((c+z)*d) w) * (shortSuffixLimit r/σ^(r.val+1)) := by
  let B := m-(2*d+1)
  have hs : 2*(c+z)*((m:ℝ)*√m) ≤ 57 := by linarith only [hγ,hΔ,hmax]
  have ht' := suffix_label_bounds hm (Nat.sub_le m (2*d+1)) (add_nonneg hc hz) hs
  have hp (i : ℕ) (hi : i ∈ Finset.range B) : 49/250 ≤ labelVariance (c+z) (i+1) ∧ labelVariance (c+z) (i+1) ≤ 1/4 :=
    ⟨(by norm_num : (49/250:ℝ) ≤ (1-(57/128)^2)/4).trans (ht' i hi).2.1,(ht' i hi).2.2⟩
  have hb' : (0:ℝ) < B := by exact_mod_cast (by dsimp [B]; omega : 0 < B)
  have hv := (suffix_variance_bounds _ B (by norm_num : (0:ℝ) ≤ 49/250) hp).1
  have hpos : 0 < suffixVariance (c+z) B := (by positivity : 0 < (49/250)/3*(B:ℝ)^3).trans_le hv
  have scale : ((m:ℝ)*√m)^2=(m:ℝ)^3 := by rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]; ring
  exact first_hit_rank_bin ht hc hz scale hγ hΔ hsmall he hlo hhi r
    (short_free_differences hB (Real.sqrt_pos.mpr hpos) (Real.sq_sqrt hpos.le).symm hp r) k

/-- Fully explicit first-hit rank bound using the marked-excursion estimate
for the recentered prefix. The split-prefix estimate can improve it. -/
theorem first_hit_rank_marked {m d : ℕ} (hm : 4096 ≤ m) (ht : 2*d+1 ≤ m) (hB : 255 ≤ m-(2*d+1))
    {c z γ Δ v e : ℝ} (hc : 0 ≤ c) (hz : 0 ≤ z)
    (hγ : γ=2*c*((m:ℝ)*√m)) (hΔ : Δ=2*z*((m:ℝ)*√m)) (hmax : γ+Δ ≤ 57)
    (hsmall : γ^2 ≤ 6*m) (he : e ≤ 2) (hlo : v*m ≤ 2*(d:ℝ)+1) (hhi : 2*(d:ℝ)+1 ≤ e*m)
    (r : Fin 3) (k : ℤ) :
    let σ := √(suffixVariance (c+z) (m-(2*d+1)))
    let t := 2*(d:ℝ)+1
    let y := (c+z)*t*√((d:ℝ)+1)
    let L := (c+z)^2*d*(d+1)*t/6*(1-((c+z)*d)^2/6)
    let G := (survival d/(2*(d+1)))*exp ((c+z)*d+y^2/4-L)*(1+y/2*(√π+min (√π) y))
    rankChange c z (meanRank c m) m *
      |rankDifference r k (prefixEventSiteMass (c+z) m (2*d+1) (hitWords 1 (2*d+1)))| ≤
      exp (Δ^2*(labelSquares m/(m:ℝ)^3)/8 - v*(1-e/2)^2*(γ+Δ)*(γ*(1-γ^2/(6*m))+Δ)/8) *
        G * (shortSuffixLimit r/σ^(r.val+1)) := by
  apply (first_hit_rank_bound hm ht hB hc hz hγ hΔ hmax hsmall he hlo hhi r k).trans
  apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (tilted_hit_gaussian d (add_nonneg hc hz)) (exp_pos _).le)
  have h : 0 ≤ shortSuffixLimit r := by unfold shortSuffixLimit; split <;> norm_num
  positivity

end CentralUnimodality.MarkedExcursion
