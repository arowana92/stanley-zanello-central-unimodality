module

public import CentralUnimodality.FreeSuffixArcs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Label variances for the full upper-half tilt. The suffix variance
ratio uses the monotonicity of the individual label variances. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

theorem label_variance_cosh (c x : ℝ) : labelVariance c x=1/(4*cosh (c*x)^2) := by
  dsimp only [labelVariance,upChance]
  rw [cosh_neg,exp_neg]
  field_simp; ring

theorem label_variance_antitone (c : ℝ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    labelVariance c y ≤ labelVariance c x := by
  have H := cosh_le_cosh.mpr (show |c*x| ≤ |c*y| by
    simpa only [abs_mul,abs_of_nonneg hx,abs_of_nonneg (hx.trans hxy)] using mul_le_mul_of_nonneg_left hxy (abs_nonneg c))
  rw [label_variance_cosh,label_variance_cosh]
  apply one_div_le_one_div_of_le (by positivity)
  linarith only [pow_le_pow_left₀ (cosh_pos _).le H 2]

theorem suffix_weighted_squares (c : ℝ) {B M : ℕ} (hBM : B ≤ M) :
    suffixVariance c M*labelSquares B ≤ suffixVariance c B*labelSquares M := by
  have qsum (u : ℕ) : labelSquares u=∑ i ∈ Finset.range u, ((i:ℝ)+1)^2 := by
    rw [reverse_labels u (fun x => x^2),sum_labelSquares]
  induction M, hBM using Nat.le_induction with
  | base => rfl
  | succ M hBM ih =>
    let x := (M:ℝ)+1
    have hsmall : labelVariance c x*labelSquares B ≤ suffixVariance c B := by
      rw [qsum,Finset.mul_sum,suffixVariance]
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply label_variance_antitone c (by positivity)
      dsimp only [x]
      have hi' : (i:ℝ) ≤ M := by exact_mod_cast (Finset.mem_range.mp hi).le.trans hBM
      linarith only [hi']
    have hs : suffixVariance c (M+1)=suffixVariance c M+labelVariance c x*x^2 := Finset.sum_range_succ ..
    have hq : labelSquares (M+1)=labelSquares M+x^2 := by rw [qsum,qsum M,Finset.sum_range_succ]
    rw [hs,hq]
    linarith only [ih,mul_le_mul_of_nonneg_right hsmall (sq_nonneg x)]

/-- In particular the variance ratio is bounded by the cube of the length
ratio, including arbitrarily large positive tilts. -/
theorem suffix_variance_ratio (c : ℝ) {B M : ℕ} (hB : 0<B) (hBM : B ≤ M) :
    suffixVariance c M*(B:ℝ)^3 ≤ suffixVariance c B*(M:ℝ)^3 := by
  have hb : 0<(B:ℝ) := by exact_mod_cast hB
  have hm : 0<(M:ℝ) := by exact_mod_cast hB.trans_le hBM
  have hle : (B:ℝ) ≤ M := by exact_mod_cast hBM
  have H := one_div_le_one_div_of_le hb hle
  have hx := mul_le_mul (add_le_add_left H 1) (add_le_add_left H 2) (by positivity) (by positivity)
  have form (u : ℕ) (h : 0<(u:ℝ)) :
      labelSquares u/(u:ℝ)^3=(1+1/(u:ℝ))*(2+1/(u:ℝ))/6 := by dsimp [labelSquares]; field_simp
  have hq : labelSquares M*(B:ℝ)^3 ≤ labelSquares B*(M:ℝ)^3 := by
    apply (div_le_div_iff₀ (pow_pos hm 3) (pow_pos hb 3)).mp
    rw [form _ hm,form _ hb]; linarith only [hx]
  have hV : 0 ≤ suffixVariance c B := by
    dsimp only [suffixVariance]; apply Finset.sum_nonneg
    intro i _; rw [label_variance_cosh]; positivity
  have hQ : 0<labelSquares B := by dsimp only [labelSquares]; positivity
  apply le_of_mul_le_mul_right _ hQ
  linarith only [mul_le_mul_of_nonneg_left hq hV,
    mul_le_mul_of_nonneg_right (suffix_weighted_squares c hBM) (pow_nonneg hb.le 3)]

private theorem cosh_one_upper : cosh 1 ≤ 31/20 := by
  have hlo : 100/37 ≤ exp 1 := by linarith only [exp_one_gt_d9]
  have hhi : exp 1 ≤ 68/25 := by linarith only [exp_one_lt_d9]
  have hi : (exp 1)⁻¹ ≤ 37/100 := by
    rw [← one_div,div_le_iff₀ (exp_pos _)]; linarith only [hlo]
  rw [cosh_eq,exp_neg]; linarith only [hhi,hi]

/-- The three variance floors for the successive suffix ranges in the
first-passage proof. The parameter is bounded at the last label. -/
theorem upper_half_label_floors {u : ℝ} (hu : 0 ≤ u) (h1 : u ≤ 1) :
    13/125 ≤ 1/(4*cosh u^2) ∧
    (u ≤ 1/2 → 49/250 ≤ 1/(4*cosh u^2)) ∧
    (u ≤ 1/4 → 117/500 ≤ 1/(4*cosh u^2)) := by
  have mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) := cosh_strictMonoOn.monotoneOn ha (ha.trans hab) hab
  have H := (mono hu h1).trans cosh_one_upper
  have double (x : ℝ) : 2*cosh x^2-1=cosh (2*x) := by
    rw [cosh_two_mul]; linarith only [cosh_sq_sub_sinh_sq x]
  have half (h : u ≤ 1/2) : cosh u^2 ≤ 51/40 := by
    have d := (mono (mul_nonneg (by norm_num) hu) (show 2*u ≤ 1 by linarith only [h])).trans cosh_one_upper
    linarith only [d,double u]
  have pos : 0 < 4*cosh u^2 := by positivity
  refine ⟨(le_div_iff₀ pos).mpr (by linarith only [pow_le_pow_left₀ (cosh_pos _).le H 2]),?_,?_⟩
  · intro h; apply (le_div_iff₀ pos).mpr; linarith only [half h]
  · intro h
    have hd : 0 ≤ 2*u := by positivity
    have H := (mono (by positivity : 0 ≤ 2*(2*u)) (show 2*(2*u) ≤ 1 by linarith only [h])).trans cosh_one_upper
    have H₂ : cosh (2*u)^2 ≤ 51/40 := by linarith only [H,double (2*u)]
    have Hu : cosh (2*u) ≤ 113/100 := by nlinarith only [H₂,sq_nonneg (cosh (2*u)-113/100)]
    apply (le_div_iff₀ pos).mpr
    linarith only [Hu,double u]

/-- Apply the variance floors at every actual suffix label. -/
theorem upper_half_suffix_labels {B m : ℕ} (hB : B ≤ m) {c : ℝ} (hc : 0 ≤ c) (hu : c*m ≤ 1)
    (i : ℕ) (hi : i ∈ Finset.range B) :
    13/125 ≤ labelVariance c (i+1) ∧ labelVariance c (i+1) ≤ 1/4 ∧
      (2*B ≤ m → 49/250 ≤ labelVariance c (i+1)) ∧
      (4*B ≤ m → 117/500 ≤ labelVariance c (i+1)) := by
  let u := c*((i:ℝ)+1)
  have hz : 0 ≤ u := by dsimp [u]; positivity
  have hil : (i:ℝ)+1 ≤ B := by exact_mod_cast Finset.mem_range.mp hi
  have hsub : u ≤ c*B := mul_le_mul_of_nonneg_left hil hc
  have h₁ : u ≤ 1 := hsub.trans ((mul_le_mul_of_nonneg_left (by exact_mod_cast hB) hc).trans hu)
  obtain ⟨hl,hh,hq⟩ := upper_half_label_floors hz h₁
  rw [label_variance_cosh]
  have hx : (1:ℝ) ≤ cosh u := one_le_cosh _
  refine ⟨hl,one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 4)
    (by nlinarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hx 2]),?_,?_⟩
  · intro h; apply hh
    have ht : 2*(B:ℝ) ≤ m := by exact_mod_cast h
    linarith only [hsub,hu,mul_le_mul_of_nonneg_left ht hc]
  · intro h; apply hq
    have ht : 4*(B:ℝ) ≤ m := by exact_mod_cast h
    linarith only [hsub,hu,mul_le_mul_of_nonneg_left ht hc]

end CentralUnimodality.MarkedExcursion
