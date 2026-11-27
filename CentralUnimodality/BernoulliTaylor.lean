module

public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Sharp exponential Taylor remainders for the centered Bernoulli factors
in the unrestricted suffix. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Set MeasureTheory intervalIntegral

/-- In the closed left half-plane the integral Taylor remainder costs exactly
the next factorial, with no exponential growth factor. -/
theorem exp_taylor_left (z : ℂ) (hz : z.re ≤ 0) (n : ℕ) :
    ‖Complex.exp z - ∑ k ∈ Finset.range (n+1), z^k/(Nat.factorial k:ℂ)‖ ≤
      ‖z‖^(n+1)/(Nat.factorial (n+1):ℝ) := by
  let f := fun t : ℝ => Complex.exp ((t:ℂ)*z)
  have hf (t : ℝ) : HasDerivAt f (Complex.exp ((t:ℂ)*z)*z) t := by
    have h : HasDerivAt (fun w : ℂ => Complex.exp (w*z)) (Complex.exp ((t:ℂ)*z)*z) (t:ℂ) := by
      simpa using ((hasDerivAt_id (t:ℂ)).mul_const z).cexp
    exact h.comp_ofReal
  have hc (k : ℕ) : ContDiff ℝ k f :=
    ((Complex.ofRealCLM.contDiff : ContDiff ℝ k ((↑) : ℝ → ℂ)).mul contDiff_const).cexp
  have hdiff (k : ℕ) : iteratedDeriv k f = fun t => z^k*f t := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iteratedDeriv_succ,ih]
      funext t
      convert ((hf t).const_mul (z^k)).deriv using 1; simp [f,pow_succ]; ring
  have hs (k : ℕ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      iteratedDerivWithin k f (uIcc 0 1) t = z^k*f t := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by norm_num)) (hc k).contDiffAt
      (by simpa using ht),hdiff]
  have H := taylor_integral_remainder (f := f) (x₀ := (0:ℝ)) (x := 1) (n := n) (hc _).contDiffOn
  have H₀ : taylorWithinEval f n (uIcc 0 1) 0 1 = ∑ k ∈ Finset.range (n+1), z^k/(Nat.factorial k:ℂ) := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [hs k 0 (by simp)]
    simp [f,Complex.real_smul,div_eq_inv_mul]
  rw [H₀] at H
  change Complex.exp ((1:ℂ)*z)-_ = _ at H
  rw [one_mul] at H
  rw [H]
  apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0:ℝ) ≤ 1)).trans
  let G := fun t : ℝ => (1-t)^n/(Nat.factorial n:ℝ)*‖z‖^(n+1)
  have hu (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ‖((1-t)^n/(Nat.factorial n:ℝ)) • iteratedDerivWithin (n+1) f (uIcc 0 1) t‖ ≤ G t := by
    rw [hs _ t ht,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity [sub_nonneg.mpr ht.2]),
      norm_mul,norm_pow]
    dsimp [G]
    have he : ‖f t‖ ≤ 1 := by
      simp only [f,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ht.1 hz)
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (pow_nonneg (norm_nonneg z) _) he)
      (by positivity [sub_nonneg.mpr ht.2])
  apply (intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) _ _ hu).trans_eq
  · change (∫ t in (0:ℝ)..1, (1-t)^n/(n.factorial:ℝ)*‖z‖^(n+1)) = _
    rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_div,
      intervalIntegral.integral_comp_sub_left (fun t : ℝ => t^n) 1,integral_pow]
    simp [Nat.factorial_succ]
    field_simp
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.norm
    have hcont : Continuous f := (hc 0).continuous
    apply ContinuousOn.congr (f := fun t : ℝ => ((1-t)^n/(n.factorial:ℝ)) • (z^(n+1)*f t))
      (by fun_prop)
    intro t ht
    exact congrArg (fun a : ℂ => ((1-t)^n/(n.factorial:ℝ)) • a) (hs _ t (by simpa using ht))
  · apply Continuous.intervalIntegrable
    dsimp [G]; fun_prop

/-- Characteristic function of a Bernoulli(p) variable after centering. -/
noncomputable def bernoulliFactor (p t : ℝ) : ℂ :=
  (1-p)*Complex.exp (((-p*t:ℝ):ℂ)*Complex.I) +
    p*Complex.exp ((((1-p)*t:ℝ):ℂ)*Complex.I)

private noncomputable def phaseCubic (x : ℝ) : ℂ :=
  1-(x:ℂ)^2/2+((x:ℂ)-(x:ℂ)^3/6)*Complex.I

private theorem phase_remainder (x : ℝ) :
    ‖Complex.exp ((x:ℂ)*Complex.I)-phaseCubic x‖ ≤ |x|^4/24 := by
  have h := exp_taylor_left ((x:ℂ)*Complex.I) (by simp) 3
  have he : ∑ k ∈ Finset.range (3+1), ((x:ℂ)*Complex.I)^k/(Nat.factorial k:ℂ) = phaseCubic x := by
    norm_num [Finset.sum_range_succ,Nat.factorial,phaseCubic,mul_pow,Complex.I_sq,pow_succ]
    ring
  rw [he] at h
  norm_num [norm_mul,Real.norm_eq_abs,Nat.factorial] at h ⊢
  exact h

private theorem gaussian_linear {h : ℝ} (hh : 0 ≤ h) :
    ‖(1-(h:ℂ))-(Real.exp (-h):ℂ)‖ ≤ h^2/2 := by
  have H := exp_taylor_left (-(h:ℂ)) (by simpa using hh) 1
  rw [norm_sub_rev] at H
  simpa [Finset.sum_range_succ,Complex.ofReal_exp,Real.norm_eq_abs,abs_of_nonneg hh,sub_eq_add_neg] using H

/-- The signed third Bernoulli moment supplies the drift factor in the
cubic error. The fourth-order error is at most w |t|⁴/24 for w=p(1-p). -/
theorem bernoulli_gaussian_error {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (t : ℝ) :
    let w := p*(1-p)
    ‖bernoulliFactor p t - (Real.exp (-(w*t^2/2)):ℂ)‖ ≤
      w*(|1-2*p| * |t|^3/6+|t|^4/24) := by
  let q := 1-p
  let w := p*q
  let x := -p*t
  let y := q*t
  let h := w*t^2/2
  let L := (q:ℂ)*phaseCubic x + (p:ℂ)*phaseCubic y
  let g := 1-(h:ℂ)
  have hq : 0 ≤ q := sub_nonneg.mpr hp'
  have hw : 0 ≤ w := mul_nonneg hp hq
  have hh : 0 ≤ h := by dsimp only [h]; positivity
  have hL : L-g = -((w*(1-2*p)*t^3/6:ℝ):ℂ)*Complex.I := by
    dsimp [L,g,h,w,x,y,q,phaseCubic]; push_cast; ring
  have h₃ : ‖L-g‖ = w* |1-2*p| * |t|^3/6 := by
    rw [hL,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs]
    simp [abs_of_nonneg hw,abs_mul,abs_div,abs_pow]
  have he : bernoulliFactor p t-L = (q:ℂ)*(Complex.exp ((x:ℂ)*Complex.I)-phaseCubic x) +
      (p:ℂ)*(Complex.exp ((y:ℂ)*Complex.I)-phaseCubic y) := by
    dsimp [bernoulliFactor,L,x,y,q]; push_cast; ring
  have h₄ : ‖bernoulliFactor p t-L‖ ≤ q* |x|^4/24 + p* |y|^4/24 := by
    rw [he]
    apply (norm_add_le ..).trans
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hq,abs_of_nonneg hp]
    have hu := mul_le_mul_of_nonneg_left (phase_remainder x) hq
    have hv := mul_le_mul_of_nonneg_left (phase_remainder y) hp
    linarith only [hu,hv]
  have HG := gaussian_linear hh
  change ‖g-(Real.exp (-h):ℂ)‖ ≤ h^2/2 at HG
  have tri : ‖bernoulliFactor p t - (Real.exp (-h):ℂ)‖ ≤
      ‖bernoulliFactor p t-L‖ + ‖L-g‖ + ‖g-(Real.exp (-h):ℂ)‖ :=
    by simpa only [dist_eq_norm] using (dist_triangle (bernoulliFactor p t) g (Real.exp (-h):ℂ)).trans
         (add_le_add_left (dist_triangle (bernoulliFactor p t) L g) _)
  rw [h₃] at tri
  change ‖bernoulliFactor p t - (Real.exp (-h):ℂ)‖ ≤ w*(|1-2*p| * |t|^3/6+|t|^4/24)
  apply tri.trans
  apply (add_le_add (add_le_add_left h₄ _) HG).trans_eq
  simp only [x,y,abs_mul,abs_neg,abs_of_nonneg hp,abs_of_nonneg hq]
  dsimp only [h,w,q]
  have hₜ : |t|^4=t^4 := by rw [← abs_pow,abs_of_nonneg (by positivity : 0 ≤ t^4)]
  simp only [mul_pow,hₜ]
  ring

end CentralUnimodality.MarkedExcursion
