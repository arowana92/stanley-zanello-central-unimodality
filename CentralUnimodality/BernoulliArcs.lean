module

public import CentralUnimodality.FreeSuffixFourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Uniform modulus and Gaussian error on the small Fourier arc for a
product of centered, independently biased Bernoulli factors. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

theorem bernoulli_norm_sq (p t : ℝ) :
    ‖bernoulliFactor p t‖^2 = 1-4*p*(1-p)*sin (t/2)^2 := by
  have he : bernoulliFactor p t = phase (-p*t)*((1-(p:ℂ))+(p:ℂ)*phase t) := by
    change (1-(p:ℂ))*phase (-p*t)+(p:ℂ)*phase ((1-p)*t) = _
    rw [show (1-p)*t=(-p*t)+t by ring,phase_add]; ring
  rw [he,norm_mul,phase_norm,one_mul,Complex.sq_norm,Complex.normSq_apply]
  have hc := Real.cos_two_mul_eq_one_sub (t/2)
  rw [show 2*(t/2)=t by ring] at hc
  simp only [phase,Complex.exp_mul_I,← Complex.ofReal_sin,← Complex.ofReal_cos,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  linear_combination p^2 * Real.sin_sq_add_cos_sq t + 2*p*(1-p)*hc

theorem bernoulli_modulus (p t : ℝ) :
    ‖bernoulliFactor p t‖ ≤ exp (-2*p*(1-p)*sin (t/2)^2) := by
  apply (sq_le_sq₀ (norm_nonneg _) (exp_pos _).le).mp
  rw [bernoulli_norm_sq,sq (exp _),← exp_add]
  linarith only [add_one_le_exp (-2*p*(1-p)*sin (t/2)^2 + -2*p*(1-p)*sin (t/2)^2)]

theorem small_sine {t : ℝ} (ht : |t| ≤ 1) : 9/20*t^2 ≤ 2*sin (t/2)^2 := by
  have bound (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1/2) : 23/24*x ≤ sin x := by
    rcases hx.eq_or_lt with h|h
    · simp [← h]
    have h₂ := pow_le_pow_left₀ hx hx' 2
    nlinarith only [mul_le_mul_of_nonneg_right h₂ hx,Real.sin_gt_sub_cube h]
  have H := bound (|t|/2) (by positivity) (by linarith only [ht])
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 23/24*(|t|/2)) H 2
  have ht' : (23/24:ℝ)^2 ≥ 9/10 := by norm_num
  have hsq : sin (|t|/2)^2 = sin (t/2)^2 := by
    by_cases hp : 0 ≤ t
    · rw [abs_of_nonneg hp]
    · rw [abs_of_neg (lt_of_not_ge hp),neg_div,sin_neg,neg_sq]
  simp only [hsq,mul_pow,div_pow,sq_abs] at hs
  nlinarith only [hs,sq_nonneg t]

private theorem small_factor {p t : ℝ} (hp : 0 ≤ p) (hq : p ≤ 1) (ht : |t| ≤ 1) :
    ‖bernoulliFactor p t‖ ≤ exp (-(9/20*p*(1-p)*t^2)) := by
  apply (bernoulli_modulus p t).trans
  apply exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left (small_sine ht) (mul_nonneg hp (sub_nonneg.mpr hq))]

private theorem product_error {ι : Type*} (S : Finset ι) (A G : ι → ℂ) (E : ι → ℝ)
    (hA : ∀ i ∈ S, ‖A i‖ ≤ 1) (hG : ∀ i ∈ S, ‖G i‖ ≤ 1)
    (hE : ∀ i ∈ S, ‖A i-G i‖ ≤ E i) :
    ‖(∏ i ∈ S, A i)-(∏ i ∈ S, G i)‖ ≤ ∑ i ∈ S, E i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have sub {i} (hi : i ∈ S) : i ∈ insert a S := Finset.mem_insert_of_mem hi
    have H := ih (fun i hi => hA i (sub hi)) (fun i hi => hG i (sub hi)) (fun i hi => hE i (sub hi))
    have hg : ‖∏ i ∈ S, G i‖ ≤ 1 := by
      rw [norm_prod]; exact Finset.prod_le_one₀ (fun i _ => norm_nonneg (G i)) (fun i hi => hG i (sub hi))
    rw [Finset.prod_insert ha,Finset.prod_insert ha,Finset.sum_insert ha]
    rw [show A a*(∏ i ∈ S, A i)-G a*(∏ i ∈ S, G i) =
      A a*((∏ i ∈ S, A i)-(∏ i ∈ S, G i))+(A a-G a)*(∏ i ∈ S, G i) by ring]
    apply (norm_add_le ..).trans
    rw [norm_mul,norm_mul,add_comm]
    exact add_le_add ((mul_le_of_le_one_right (norm_nonneg _) hg).trans (hE a (Finset.mem_insert_self ..)))
      ((mul_le_of_le_one_left (norm_nonneg _) (hA a (Finset.mem_insert_self ..))).trans H)

/-- On the arc |tᵢ| ≤ 1 the product error retains Gaussian damping over
all sites. Only one factor of exp(9/80) is lost at every size. -/
theorem product_gaussian_error {ι : Type*} (S : Finset ι) (p t : ι → ℝ)
    (hp : ∀ i ∈ S, 0 ≤ p i ∧ p i ≤ 1) (ht : ∀ i ∈ S, |t i| ≤ 1) :
    let w := fun i => p i*(1-p i)
    let V := ∑ i ∈ S, w i*(t i)^2
    ‖(∏ i ∈ S, bernoulliFactor (p i) (t i)) - (exp (-V/2):ℂ)‖ ≤
      exp (9/80-9/20*V) * ∑ i ∈ S, w i*(|1-2*p i| * |t i|^3/6+|t i|^4/24) := by
  dsimp only
  let v := fun i => p i*(1-p i)*(t i)^2
  let α := (9/20:ℝ)
  let E := fun i => p i*(1-p i)*(|1-2*p i| * |t i|^3/6+|t i|^4/24)
  let A := fun i => (exp (α*v i):ℂ)*bernoulliFactor (p i) (t i)
  let G := fun i => (exp (α*v i):ℂ)*(exp (-(v i)/2):ℂ)
  have hv (i) (hi : i ∈ S) : 0 ≤ v i := mul_nonneg (mul_nonneg (hp i hi).1 (sub_nonneg.mpr (hp i hi).2)) (sq_nonneg _)
  have normexp (x : ℝ) : ‖(exp x:ℂ)‖ = exp x := by simp
  have hA (i) (hi : i ∈ S) : ‖A i‖ ≤ 1 := by
    simp only [A,norm_mul,normexp]
    have H := mul_le_mul_of_nonneg_left (small_factor (hp i hi).1 (hp i hi).2 (ht i hi)) (exp_pos (α*v i)).le
    convert H using 1
    rw [← exp_add]; dsimp [α,v]; ring_nf; simp
  have hG (i) (hi : i ∈ S) : ‖G i‖ ≤ 1 := by
    simp only [G,norm_mul,normexp,← exp_add]
    apply exp_le_one_iff.mpr; dsimp [α]; linarith only [hv i hi]
  have hE (i) (hi : i ∈ S) : ‖A i-G i‖ ≤ exp (9/80)*E i := by
    dsimp only [A,G]
    rw [← mul_sub,norm_mul,normexp]
    rw [show -(v i)/2= -(v i/2) by ring]
    apply mul_le_mul _ (bernoulli_gaussian_error (hp i hi).1 (hp i hi).2 (t i)) (norm_nonneg _) (exp_pos _).le
    apply exp_le_exp.mpr
    have h₂ : (t i)^2 ≤ 1 := by simpa using pow_le_pow_left₀ (abs_nonneg _) (ht i hi) 2
    have hw : p i*(1-p i) ≤ 1/4 := by nlinarith only [sq_nonneg (p i-1/2)]
    dsimp [α,v]
    nlinarith only [mul_le_mul hw h₂ (sq_nonneg _) (by norm_num : 0 ≤ (1:ℝ)/4)]
  have H := product_error S A G (fun i => exp (9/80)*E i) hA hG hE
  simp only [A,G,Finset.prod_mul_distrib,← Complex.ofReal_prod,← Real.exp_sum,← Finset.mul_sum] at H
  rw [← mul_sub,norm_mul,normexp] at H
  have he : (∑ i ∈ S, -(v i)/2) = -(∑ i ∈ S, v i)/2 := by
    rw [← Finset.sum_div,Finset.sum_neg_distrib]
  rw [he] at H
  have HH := mul_le_mul_of_nonneg_left H (exp_pos (-(α*∑ i ∈ S, v i))).le
  rw [← mul_assoc,← exp_add,neg_add_cancel,exp_zero,one_mul,← mul_assoc,← exp_add] at HH
  rw [show -(α*∑ i ∈ S, v i)+9/80=9/80-α*∑ i ∈ S, v i by ring] at HH
  exact HH

end CentralUnimodality.MarkedExcursion
