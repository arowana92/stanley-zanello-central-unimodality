module

public import CentralUnimodality.ShortSuffixTails
import Mathlib.Analysis.Real.Pi.Bounds

/-! Fourier envelope for the short independent suffix at a first hit.
B is its own length and σ is its own standard deviation. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real MeasureTheory Set

noncomputable def frequencyBox (T C : ℝ) (r : ℕ) : ℝ → ℝ :=
  (Icc (-T) T).indicator (fun _ => T^r*C)

noncomputable def shortEnvelope (B : ℝ) (r : ℕ) (x : ℝ) :=
  momentKernel (9/20) r x + 16/250*laplaceShoulders 4 x + 64/100000*laplaceShoulders 8 x +
    frequencyBox (32*B/15) (exp (-(49/500)*B)) r x + frequencyBox (4*B^2) (exp (-(147/800)*B)) r x

theorem short_suffix_scale {B : ℕ} (hB : 255 ≤ B) {c σ : ℝ} (hσ : 0 < σ) (hV : suffixVariance c B=σ^2)
    (hp : ∀ i ∈ Finset.range B, 49/250 ≤ labelVariance c (i+1) ∧ labelVariance c (i+1) ≤ 1/4) :
    4*(B:ℝ) ≤ σ ∧ σ ≤ (B:ℝ)^2/15 := by
  have hB' : (255:ℝ) ≤ B := by exact_mod_cast hB
  obtain ⟨hl,hu⟩ := suffix_variance_bounds c B (by norm_num : (0:ℝ) ≤ 49/250) hp
  rw [hV] at hl hu
  constructor
  · apply (sq_le_sq₀ (by positivity) hσ.le).mp
    nlinarith only [hl,mul_le_mul_of_nonneg_right hB' (sq_nonneg (B:ℝ)),sq_nonneg (B:ℝ)]
  · apply (sq_le_sq₀ hσ.le (by positivity)).mp
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ (B:ℝ)+1) (by linarith only [hB'] : (B:ℝ)+1 ≤ 2*B) 3
    have h₃ : 0 ≤ (B:ℝ)^3 := by positivity
    nlinarith only [hu,h,mul_le_mul_of_nonneg_right hB' h₃,h₃]

private theorem box_nonneg {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C) (r : ℕ) (x : ℝ) :
    0 ≤ frequencyBox T C r x := by
  apply indicator_nonneg
  intro _ _; exact mul_nonneg (pow_nonneg hT _) hC

private theorem box_bound {T C x : ℝ} (hx : |x| ≤ T) (hC : 0 ≤ C) (r : ℕ) : C*|x|^r ≤ frequencyBox T C r x := by
  have h : x ∈ Icc (-T) T := abs_le.mp hx
  rw [frequencyBox,indicator_of_mem h,mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hx r) hC

/-- The normalized frequency envelope has no dependence on the test rank. -/
theorem short_suffix_envelope (B : ℕ) (hB : 255 ≤ B) {c σ : ℝ} (hσ : 0 < σ)
    (hV : suffixVariance c B=σ^2)
    (hp : ∀ i ∈ Finset.range B, 49/250 ≤ labelVariance c (i+1) ∧ labelVariance c (i+1) ≤ 1/4)
    (r : ℕ) (hr : r ≤ 2) (x : ℝ) :
    ‖bandTransform c B (x/σ)‖*|x|^r ≤ shortEnvelope B r x := by
  obtain ⟨hl,hu⟩ := short_suffix_scale hB hσ hV hp
  let θ := x/σ
  let t := |θ|
  have hB' : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have ht : 0 ≤ t := abs_nonneg _
  have hx : σ*t=|x| := by dsimp [t,θ]; rw [abs_div,abs_of_pos hσ]; field_simp
  have hv : suffixVariance c B*t^2=x^2 := by
    rw [hV,← mul_pow,hx,sq_abs]
  have h₀ : 0 ≤ momentKernel (9/20) r x := by unfold momentKernel; positivity
  have h₁ : 0 ≤ 16/250*laplaceShoulders 4 x := mul_nonneg (by norm_num) (laplaceShoulders_pos ..).le
  have h₂ : 0 ≤ 64/100000*laplaceShoulders 8 x := mul_nonneg (by norm_num) (laplaceShoulders_pos ..).le
  have h₃ := box_nonneg (by positivity : 0 ≤ 32*(B:ℝ)/15) (exp_pos (-(49/500)*(B:ℝ))).le r x
  have h₄ := box_nonneg (by positivity : 0 ≤ 4*(B:ℝ)^2) (exp_pos (-(147/800)*(B:ℝ))).le r x
  unfold shortEnvelope
  change ‖bandTransform c B θ‖*|x|^r ≤ _
  by_cases hb : θ ∈ Ioc (-π) π
  · have he : ‖bandTransform c B θ‖=‖suffixTransform c t B‖ := by
      rw [bandTransform,indicator_of_mem hb]; dsimp only [t]
      rcases le_total 0 θ with h|h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h,suffix_norm_even]
    rw [he]
    have trans (b : ℝ) (H : ‖suffixTransform c t B‖ ≤ exp (-(b*suffixVariance c B*t^2))) :
        ‖suffixTransform c t B‖*|x|^r ≤ momentKernel b r x := by
      rw [momentKernel,mul_comm (|x|^r)]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [mul_assoc,hv,← neg_mul] at H
      exact H
    by_cases hs : B*t ≤ 1
    · have h := trans _ (suffix_inner_modulus c t B (by rwa [abs_of_nonneg ht]))
      linarith only [h,h₁,h₂,h₃,h₄]
    have hdist := mul_le_mul_of_nonneg_right hl ht
    rw [hx] at hdist
    by_cases htwo : B*t ≤ 2
    · have h := (trans _ ((suffix_middle_arcs c ht B).1 htwo)).trans
        ((short_middle_tails x r hr).1 (by nlinarith only [le_of_not_ge hs,hdist]))
      linarith only [h,h₀,h₂,h₃,h₄]
    by_cases hpi : B*t ≤ π
    · have h := (trans _ ((suffix_middle_arcs c ht B).2 hpi)).trans
        ((short_middle_tails x r hr).2 (by nlinarith only [le_of_not_ge htwo,hdist]))
      linarith only [h,h₀,h₁,h₃,h₄]
    have hπ : t ≤ π := abs_le.mpr ⟨hb.1.le,hb.2⟩
    have H := suffix_outer_arcs c ht hπ B (p := 49/250) (by norm_num) (fun i hi => (hp i hi).1)
    by_cases near : B*t ≤ 8*π
    · have hx' : |x| ≤ 32*B/15 := by
        have h := mul_le_mul_of_nonneg_right hu ht
        rw [hx] at h
        have h' := mul_le_mul_of_nonneg_left near hB'.le
        nlinarith only [h,h',mul_le_mul_of_nonneg_left pi_lt_four.le hB'.le]
      have hh := (mul_le_mul_of_nonneg_right (H.1 (le_of_not_ge hpi)) (by positivity : 0 ≤ |x|^r))
      rw [show -(49/250*(B:ℝ)/2)=-(49/500)*B by ring] at hh
      have h := hh.trans (box_bound hx' (exp_pos _).le r)
      linarith only [h,h₀,h₁,h₂,h₄]
    · have hx' : |x| ≤ 4*(B:ℝ)^2 := by
        nlinarith only [mul_le_mul_of_nonneg_left (hπ.trans pi_lt_four.le) hσ.le,hu,hx,sq_nonneg (B:ℝ)]
      have hh := mul_le_mul_of_nonneg_right (H.2 (le_of_not_ge near)) (by positivity : 0 ≤ |x|^r)
      rw [show -(15*(49/250)*(B:ℝ)/16)=-(147/800)*B by ring] at hh
      have h := hh.trans (box_bound hx' (exp_pos _).le r)
      linarith only [h,h₀,h₁,h₂,h₃]
  · rw [bandTransform,indicator_of_notMem hb,norm_zero,zero_mul]
    linarith only [h₀,h₁,h₂,h₃,h₄]

end CentralUnimodality.MarkedExcursion
