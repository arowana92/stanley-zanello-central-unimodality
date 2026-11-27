module

public import CentralUnimodality.SuffixGaussianMoments
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Real.Pi.Bounds

/-! Integrated tails for suffixes remaining after an individual first hit.
The two middle arcs use translates of the two-sided exponential density. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real MeasureTheory Set

noncomputable def laplaceShoulders (a x : ℝ) := exp (-2*|x-a|)+exp (-2*|x+a|)

theorem laplaceShoulders_integral (a : ℝ) :
    Integrable (laplaceShoulders a) ∧ (∫ x, laplaceShoulders a x)=2 := by
  let f (x : ℝ) := exp (-2*|x|)
  have hi : (∫ x, f x)=1 := by
    dsimp [f]
    rw [integral_comp_abs (f := fun x : ℝ => exp (-2*x)),integral_exp_mul_Ioi (by norm_num)]
    norm_num
  have trans (u : ℝ) : (∫ x : ℝ, f (x+u))=1 := (integral_add_right_eq_self f u).trans hi
  have ht (u : ℝ) : Integrable (fun x : ℝ => f (x+u)) := by
    by_contra hn
    have H := trans u
    rw [integral_undef hn] at H
    norm_num at H
  have he (x : ℝ) : laplaceShoulders a x=f (x+(-a))+f (x+a) := by rfl
  simp_rw [show laplaceShoulders a = fun x => f (x+(-a))+f (x+a) by funext x; exact he x]
  refine ⟨(ht _).add (ht _),?_⟩
  rw [integral_add (ht _) (ht _),trans,trans]; norm_num

theorem laplaceShoulders_pos (a x : ℝ) : 0 < laplaceShoulders a x := add_pos (exp_pos _) (exp_pos _)

private theorem tail_kernel {a b x : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b) (hba : 2+2/a ≤ 2*b*a)
    (hx : a ≤ |x|) (r : ℕ) (hr : r ≤ 2) :
    |x|^r*exp (-b*x^2) ≤ a^2*exp (-b*a^2)*laplaceShoulders a x := by
  let u := |x|-a
  have hu : 0 ≤ u := sub_nonneg.mpr hx
  have ha' : 0 < a := by linarith
  have hlin : |x| ≤ a*exp (u/a) := by
    have H := mul_le_mul_of_nonneg_left (add_one_le_exp (u/a)) ha'.le
    dsimp [u] at H; field_simp at H; nlinarith only [H]
  have hpow := (pow_le_pow_right₀ (ha.trans hx) hr).trans (pow_le_pow_left₀ (abs_nonneg _) hlin 2)
  have harg : 2*(u/a)-b*x^2 ≤ -b*a^2-2*u := by
    have H := mul_le_mul_of_nonneg_right hba hu
    have hsq : x^2=(a+u)^2 := by dsimp [u]; rw [add_sub_cancel, sq_abs]
    rw [hsq]; simp only [div_eq_mul_inv] at H ⊢
    nlinarith only [H,mul_nonneg hb (sq_nonneg u)]
  have hLap : exp (-2*u) ≤ laplaceShoulders a x := by
    rcases le_total 0 x with hx' | hx'
    · rw [laplaceShoulders,show |x-a|=u by dsimp [u]; rw [abs_of_nonneg hx'] at hx ⊢; exact abs_of_nonneg (sub_nonneg.mpr hx)]
      linarith only [(exp_pos (-2*|x+a|)).le]
    · have hy : x+a ≤ 0 := by rw [abs_of_nonpos hx'] at hx; linarith
      rw [laplaceShoulders,show |x+a|=u by dsimp [u]; rw [abs_of_nonpos hx',abs_of_nonpos hy]; ring]
      linarith only [(exp_pos (-2*|x-a|)).le]
  apply (mul_le_mul_of_nonneg_right hpow (exp_pos _).le).trans
  rw [mul_pow,← exp_nat_mul,mul_assoc,← exp_add]
  push_cast
  rw [neg_mul,← sub_eq_add_neg]
  apply le_trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr harg) (sq_nonneg _))
  rw [sub_eq_add_neg,exp_add,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
  convert hLap using 2; ring

private theorem exp_lower_rat {a C : ℝ} (h : C ≤ exp a) (hC : 0 < C) : exp (-a) ≤ 1/C := by
  rw [exp_neg,← one_div]; exact one_div_le_one_div_of_le hC h

/-- Actual unscaled integrands on 1/B...2/B and 2/B...π/B, where
the normalized frequencies are at least 4 and 8, respectively. -/
theorem short_middle_tails (x : ℝ) (r : ℕ) (hr : r ≤ 2) :
    (4 ≤ |x| → momentKernel (7/20) r x ≤ 16/250*laplaceShoulders 4 x) ∧
    (8 ≤ |x| → momentKernel (2/π^2) r x ≤ 64/100000*laplaceShoulders 8 x) := by
  have h₄ : 250 ≤ exp (28/5) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 28/5) 14
    norm_num [Finset.sum_range_succ,Nat.factorial] at h; linarith only [h]
  have h₈ : 100000 ≤ exp (64/5) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 64/5) 15
    norm_num [Finset.sum_range_succ,Nat.factorial] at h; linarith only [h]
  constructor
  · intro hx
    apply (tail_kernel (a := 4) (b := 7/20) (by norm_num) (by norm_num) (by norm_num) hx r hr).trans
    apply mul_le_mul_of_nonneg_right _ (laplaceShoulders_pos ..).le
    norm_num
    linarith only [exp_lower_rat h₄ (by norm_num)]
  · intro hx
    have hb : 1/5 ≤ 2/π^2 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith only [pow_le_pow_left₀ pi_pos.le pi_lt_d2.le 2]
    apply le_trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr
      (show -(2/π^2)*x^2 ≤ -(1/5)*x^2 by nlinarith only [mul_le_mul_of_nonneg_right hb (sq_nonneg x)])) (by positivity))
    apply (tail_kernel (a := 8) (b := 1/5) (by norm_num) (by norm_num) (by norm_num) hx r hr).trans
    apply mul_le_mul_of_nonneg_right _ (laplaceShoulders_pos ..).le
    norm_num
    linarith only [exp_lower_rat h₈ (by norm_num)]

/-- Reduce a polynomial times a decreasing exponential to its value at
255 by bounding (B/255)^q by exp(a(B-255)). -/
theorem short_exp_decay {B a : ℝ} (hB : 255 ≤ B) (q : ℕ) (ha : q/255 ≤ a) :
    B^q*exp (-a*B) ≤ 255^q*exp (-a*255) := by
  have h : B/255 ≤ exp ((B-255)/255) := by linarith only [add_one_le_exp ((B-255)/255)]
  have H := pow_le_pow_left₀ (by linarith only [hB] : 0 ≤ B/255) h q
  rw [div_pow,← exp_nat_mul] at H
  have h' := (div_le_iff₀ (by positivity : (0:ℝ)<255^q)).mp H
  apply (mul_le_mul_of_nonneg_right h' (exp_pos _).le).trans
  rw [mul_comm _ (255^q),mul_assoc,← exp_add]
  apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr _) (by positivity)
  nlinarith only [mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hB)]

/-- Whole-line integral costs of the two outer bands, including both
signs of the frequency. B²/15 bounds σ for B≥255. -/
theorem short_outer_budgets {B : ℝ} (hB : 255 ≤ B) (r : ℕ) (hr : r ≤ 2) :
    2*(32*B/15)^(r+1)*exp (-(49/500)*B) ≤ 15/1000 ∧
    2*(4*B^2)^(r+1)*exp (-(147/800)*B) ≤ 1/1000 := by
  have hE : 27/10 ≤ exp 1 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 1) 7
    norm_num [Finset.sum_range_succ,Nat.factorial] at h; linarith only [h]
  have hi (n : ℕ) {v : ℝ} (hv : n ≤ v) : exp (-v) ≤ 1/(27/10)^n := by
    apply exp_lower_rat _ (by positivity)
    have H := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 27/10) hE n
    rw [← exp_nat_mul,mul_one] at H
    exact H.trans (exp_le_exp.mpr hv)
  have K {T : ℝ} (hT : 1 ≤ T) : T^(r+1) ≤ T^3 := pow_le_pow_right₀ hT (by omega)
  constructor
  · have h := short_exp_decay (a := 49/500) hB 3 (by norm_num)
    have he := hi 24 (v := (49/500)*255) (by norm_num)
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (K (by linarith only [hB])) (by norm_num)) (exp_pos _).le).trans
    nlinarith only [h,he]
  · have h := short_exp_decay (a := 147/800) hB 6 (by norm_num)
    have he := hi 46 (v := (147/800)*255) (by norm_num)
    have hT : 1 ≤ 4*B^2 := by nlinarith only [sq_nonneg (B-1),hB]
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (K hT) (by norm_num)) (exp_pos _).le).trans
    nlinarith only [h,he]

end CentralUnimodality.MarkedExcursion
