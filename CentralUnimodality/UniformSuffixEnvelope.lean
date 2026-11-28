module

public import CentralUnimodality.SuffixGaussianMoments
import Mathlib.Analysis.Real.Pi.Bounds

/-! A local normal approximation envelope with variable drift and
variance floors, valid over the whole real frequency axis. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real Set MeasureTheory

noncomputable def cubicFactor (a D : ℝ) := 4/21*D/a
noncomputable def quarticFactor (a : ℝ) := 1/21/a^2

noncomputable def bandTerm (p M σ : ℝ) (r : ℕ) : ℝ → ℝ :=
  (Ioc (-π*σ) (π*σ)).indicator (fun _ => (π*σ)^r*exp (-(p*M/2)))

noncomputable def uniformEnvelope (a D p ε M σ : ℝ) (r : ℕ) (x : ℝ) :=
  cubicFactor a D*momentKernel (9/20) (r+3) x + quarticFactor a*momentKernel (9/20) (r+4) x +
    (2*ε)*momentKernel (1/10) r x + bandTerm p M σ r x

private theorem exp_inner : exp (9/80) ≤ 8/7 := by
  have h := Real.add_one_le_exp (-(9/80))
  rw [exp_neg,← one_div] at h
  have H : 7/8 ≤ 1/exp (9/80) := by linarith only [h]
  have := (le_div_iff₀ (exp_pos _)).mp H
  linarith

private theorem gaussian_tail {a ε b x : ℝ} (hε : exp (-(a^2/10)) ≤ ε)
    (hb : 1/5 ≤ b) (ha : 0 ≤ a) (hx : a ≤ |x|) :
    exp (-b*x^2) ≤ ε*exp (-(1/10)*x^2) := by
  have hx' := pow_le_pow_left₀ ha hx 2
  rw [sq_abs] at hx'
  apply le_trans _ (mul_le_mul_of_nonneg_right hε (exp_pos _).le)
  rw [← exp_add]
  apply exp_le_exp.mpr
  nlinarith only [hx',mul_le_mul_of_nonneg_right hb (sq_nonneg x)]

private theorem inner_bound {a D : ℝ} (ha : 0<a) (hD : 0 ≤ D) (c : ℝ) (M : ℕ) {σ x : ℝ} (hσ : 0 < σ) (hs : a*(M:ℝ) ≤ σ)
    (hV : suffixVariance c M=σ^2) (hθ : M*|x/σ| ≤ 1)
    (hd : ∀ i ∈ Finset.range M, |1-2*upChance (-(c*(i+1)))| ≤ D) :
    ‖suffixTransform c (x/σ) M - (exp (-(x^2/2)):ℂ)‖ ≤
      (cubicFactor a D*|x|^3+quarticFactor a*|x|^4)*exp (-(9/20)*x^2) := by
  have h := suffix_small_error c (x/σ) M (D) hθ hd
  have hv : suffixVariance c M*(x/σ)^2=x^2 := by rw [hV]; field_simp
  dsimp only at h
  rw [hv,exp_sub,neg_div] at h
  have hz : M*|x/σ| ≤ |x|/a := by
    rw [abs_div,abs_of_pos hσ,mul_div_assoc',div_le_div_iff₀ hσ ha]
    nlinarith only [mul_le_mul_of_nonneg_right hs (abs_nonneg x)]
  have hq := pow_le_pow_left₀ (by positivity : 0 ≤ M*|x/σ|) hz 2
  have hp : 0 ≤ D*(M*|x/σ|)/6+(M*|x/σ|)^2/24 := by positivity
  have H : (D)*(M*|x/σ|)/6+(M*|x/σ|)^2/24 ≤ (D)*(|x|/a)/6+(|x|/a)^2/24 := by
    linarith only [mul_le_mul_of_nonneg_left hz hD,hq]
  apply h.trans
  rw [div_eq_mul_inv,← exp_neg]
  apply le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right exp_inner (exp_pos _).le) (sq_nonneg x)) hp)
  apply le_trans (mul_le_mul_of_nonneg_left H (by positivity))
  apply le_of_eq
  rw [← sq_abs x]
  unfold cubicFactor quarticFactor
  ring

private theorem inner_nonneg {a D : ℝ} (ha : 0 ≤ a) (hD : 0 ≤ D) (r : ℕ) (x : ℝ) :
    0 ≤ cubicFactor a D*momentKernel (9/20) (r+3) x + quarticFactor a*momentKernel (9/20) (r+4) x := by
  unfold cubicFactor quarticFactor momentKernel; positivity

private theorem band_nonneg (p M : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) (r : ℕ) (x : ℝ) : 0 ≤ bandTerm p M σ r x := by
  unfold bandTerm
  apply indicator_nonneg
  intro _ _; positivity

/-- Inner, middle, outer and out-of-band bounds all use x=σθ. -/
theorem uniform_suffix_envelope {a D p ε : ℝ} (ha' : 0<a) (hD : 0 ≤ D) (hp₀ : 0 ≤ p)
    (hε : exp (-(a^2/10)) ≤ ε) (c : ℝ) (M : ℕ) {σ : ℝ} (hσ : 0 < σ) (hs : a*(M:ℝ) ≤ σ)
    (hM : 0 < M) (hV : suffixVariance c M=σ^2)
    (hp : ∀ i ∈ Finset.range M, |1-2*upChance (-(c*(i+1)))| ≤ D ∧
      p ≤ labelVariance c (i+1)) (r : ℕ) (x : ℝ) :
    ‖suffixSpectralError c σ M (x/σ)‖*|x|^r ≤ uniformEnvelope a D p ε M σ r x := by
  let θ := x/σ
  have hε₀ := (exp_pos _).le.trans hε
  have hm : 0 < (M:ℝ) := by exact_mod_cast hM
  have hv : σ^2*θ^2=x^2 := by dsimp [θ]; field_simp
  have ha : |θ|=|x|/σ := by rw [abs_div,abs_of_pos hσ]
  have hband : θ ∈ Ioc (-π) π ↔ x ∈ Ioc (-π*σ) (π*σ) := by
    exact and_congr (lt_div_iff₀ hσ) (div_le_iff₀ hσ)
  have hlast := band_nonneg p (M:ℝ) hσ.le r x
  have hfirst := inner_nonneg ha'.le hD r x
  have hmid : 0 ≤ ((2*ε))*momentKernel (1/10) r x := by unfold momentKernel; positivity
  have hdist (hh : 1 ≤ M*|θ|) : a ≤ |x| := by
    rw [ha,mul_div_assoc'] at hh
    have := (le_div_iff₀ hσ).mp hh
    apply le_of_mul_le_mul_left (a := (M:ℝ)) _ hm
    linarith only [this,hs]
  have normalize (H : ‖suffixSpectralError c σ M θ‖ ≤
      (2*ε)*exp (-(1/10)*x^2) + (if θ ∈ Ioc (-π) π then exp (-(p*M/2)) else 0)) :
      ‖suffixSpectralError c σ M θ‖*|x|^r ≤ uniformEnvelope a D p ε M σ r x := by
    apply (mul_le_mul_of_nonneg_right H (by positivity)).trans
    rw [add_mul]
    unfold uniformEnvelope
    have ha' : (2*ε)*exp (-(1/10)*x^2)*|x|^r=(2*ε)*momentKernel (1/10) r x := by
      unfold momentKernel; ring
    rw [ha']
    apply add_le_add (by linarith only [hfirst])
    by_cases hb : θ ∈ Ioc (-π) π
    · rw [ite_eq_left hb,bandTerm,indicator_of_mem (hband.mp hb)]
      have hx : |x| ≤ π*σ := abs_le.mpr ⟨by linarith only [(hband.mp hb).1],(hband.mp hb).2⟩
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hx r) (exp_pos _).le
    · simp only [ite_eq_right hb,zero_mul]
      exact hlast
  by_cases hb : θ ∈ Ioc (-π) π
  · by_cases hi : M*|θ| ≤ 1
    · have H := inner_bound ha' hD c M hσ hs hV hi (fun i h => (hp i h).1)
      change ‖suffixSpectralError c σ M θ‖*|x|^r ≤ _
      rw [suffixSpectralError_inside hb,hv]
      apply (mul_le_mul_of_nonneg_right H (by positivity)).trans
      unfold uniformEnvelope
      have he : (cubicFactor a D*|x|^3+quarticFactor a*|x|^4)*exp (-(9/20)*x^2)*|x|^r =
          cubicFactor a D*momentKernel (9/20) (r+3) x+quarticFactor a*momentKernel (9/20) (r+4) x := by
        unfold momentKernel; rw [pow_add,pow_add]; ring
      rw [he]; linarith only [hlast,hmid]
    · have hx := hdist (le_of_not_ge hi)
      have hn := gaussian_tail hε (b := 1/2) (by norm_num) ha'.le hx
      have he : ‖((exp (-(σ^2*θ^2/2)):ℝ):ℂ)‖ ≤ ε*exp (-(1/10)*x^2) := by
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (exp_pos _),hv]
        convert hn using 2; ring
      have hnθ : ‖suffixTransform c θ M‖ = ‖suffixTransform c |θ| M‖ := by
        rcases le_total 0 θ with h|h
        · rw [abs_of_nonneg h]
        · rw [abs_of_nonpos h,suffix_norm_even]
      apply normalize
      rw [suffixSpectralError_inside hb,ite_eq_left hb]
      apply (norm_sub_le _ _).trans
      rw [hnθ]
      by_cases hmθ : M*|θ| ≤ π
      · have H := (suffix_middle_arcs c (abs_nonneg θ) M).2 hmθ
        rw [sq_abs,hV,mul_assoc, hv] at H
        have hp2 : (1/5:ℝ) ≤ 2/π^2 := by
          apply (le_div_iff₀ (by positivity)).mpr
          nlinarith only [pow_le_pow_left₀ pi_pos.le pi_lt_d2.le 2]
        have hh := gaussian_tail hε hp2 ha'.le hx
        have HG : ‖suffixTransform c |θ| M‖ ≤ ε*exp (-(1/10)*x^2) := by
          exact H.trans (by convert hh using 2; ring)
        linarith only [HG,he,(exp_pos (-(p*(M:ℝ)/2))).le]
      · have hπ : |θ| ≤ π := abs_le.mpr ⟨hb.1.le,hb.2⟩
        have H := (suffix_outer_arcs c (abs_nonneg θ) hπ M (p := p) hp₀
          (fun i h => (hp i h).2)).1 (le_of_not_ge hmθ)
        linarith only [he,H,mul_nonneg hε₀ (exp_pos (-(1/10)*x^2)).le]
  · have hθ : π ≤ |θ| := by
      by_contra! h
      exact hb ⟨(abs_lt.mp h).1,(abs_lt.mp h).2.le⟩
    have hm1 : (1:ℝ) ≤ M := by exact_mod_cast hM
    have hx := hdist (by nlinarith only [mul_le_mul_of_nonneg_right hm1 (abs_nonneg θ),hθ,pi_gt_three])
    apply normalize
    rw [suffixSpectralError_outside hb,hv,ite_eq_right hb,add_zero]
    have H := gaussian_tail hε (b := 1/2) (by norm_num) ha'.le hx
    rw [show -(x^2/2)=-(1/2)*x^2 by ring]
    linarith only [H,mul_nonneg hε₀ (exp_pos (-(1/10)*x^2)).le]

end CentralUnimodality.MarkedExcursion
