module

public import CentralUnimodality.UniformSuffixEnvelope
import Mathlib.Analysis.Real.Pi.Bounds

/-! A single integrable majorant on the normalized frequency line for the
right-flank suffix. The indicator retains the actual lattice bandwidth. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real Set MeasureTheory

noncomputable def innerCubic : ℝ := 4/21*(25/128)/17
noncomputable def innerQuartic : ℝ := 1/21/17^2

noncomputable def lastArc (M σ : ℝ) (r : ℕ) : ℝ → ℝ :=
  (Ioc (-π*σ) (π*σ)).indicator (fun _ => (π*σ)^r*exp (-(3*M/25)))

noncomputable def suffixEnvelope (M σ : ℝ) (r : ℕ) (x : ℝ) :=
  innerCubic*momentKernel (9/20) (r+3) x + innerQuartic*momentKernel (9/20) (r+4) x +
    (2/1000000)*momentKernel (1/10) r x + lastArc M σ r x

private theorem exp_tail : exp (-28) ≤ 1/1000000 := by
  have h : 2 ≤ exp 1 := by linarith only [Real.add_one_le_exp 1]
  have H := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h 28
  rw [← exp_nat_mul] at H
  norm_num at H
  rw [exp_neg,← one_div,div_le_div_iff₀ (exp_pos _) (by norm_num)]
  linarith only [H]

theorem right_suffix_scale {M : ℕ} (hM : 3685 ≤ M) {σ : ℝ} (hσ : 0 < σ)
    (hl : 2/25*(M:ℝ)^3 ≤ σ^2) (hu : σ^2 ≤ ((M:ℝ)+1)^3/12) :
    17*(M:ℝ) ≤ σ ∧ σ ≤ (M:ℝ)^2 := by
  have hm : (3685:ℝ) ≤ M := by exact_mod_cast hM
  have hm' : 1 ≤ (M:ℝ) := by linarith
  constructor
  · apply (sq_le_sq₀ (by positivity) hσ.le).mp
    nlinarith only [hl,mul_le_mul_of_nonneg_right hm (sq_nonneg (M:ℝ)),sq_nonneg (M:ℝ)]
  · apply (sq_le_sq₀ hσ.le (sq_nonneg _)).mp
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ (M:ℝ)+1) (by linarith only [hm'] : (M:ℝ)+1 ≤ 2*M) 3
    have ht := pow_le_pow_right₀ hm' (by norm_num : 3 ≤ 4)
    nlinarith only [hu,h,ht,pow_nonneg (Nat.cast_nonneg (α:=ℝ) M) 3]

theorem right_gaussian_tail : exp (-((17:ℝ)^2/10)) ≤ 1/1000000 :=
  (exp_le_exp.mpr (by norm_num : -((17:ℝ)^2/10) ≤ -28)).trans exp_tail

/-- Inner, middle, outer and out-of-band bounds all use x=σθ. -/
theorem right_suffix_envelope (c : ℝ) (M : ℕ) {σ : ℝ} (hσ : 0 < σ) (hs : 17*(M:ℝ) ≤ σ)
    (hM : 0 < M) (hV : suffixVariance c M=σ^2)
    (hp : ∀ i ∈ Finset.range M, |1-2*upChance (-(c*(i+1)))| ≤ 25/128 ∧
      6/25 ≤ labelVariance c (i+1)) (r : ℕ) (x : ℝ) :
    ‖suffixSpectralError c σ M (x/σ)‖*|x|^r ≤ suffixEnvelope M σ r x := by
  apply (uniform_suffix_envelope (by norm_num) (by norm_num) (by norm_num) right_gaussian_tail c M hσ hs hM hV hp r x).trans_eq
  unfold uniformEnvelope suffixEnvelope cubicFactor quarticFactor innerCubic innerQuartic
  unfold bandTerm lastArc
  rw [show (6/25)*(M:ℝ)/2=3*M/25 by ring]
  ring

end CentralUnimodality.MarkedExcursion
