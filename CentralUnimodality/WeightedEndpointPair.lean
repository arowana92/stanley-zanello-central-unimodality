module

public import CentralUnimodality.BernoulliArcs
public import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Complex.Trigonometric

/-! The ℓ¹ norm of the endpoint coefficients for an independent pair of
biased signs. The mixed choices interfere at their common endpoint. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real Polynomial

noncomputable def endpointNorm (P : Polynomial ℂ) := ∑ k ∈ P.support, ‖P.coeff k‖

theorem endpointNorm_nonneg (P : Polynomial ℂ) : 0 ≤ endpointNorm P := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_over_cover (P : Polynomial ℂ) (s : Finset ℕ) (h : P.support ⊆ s) :
    endpointNorm P = ∑ k ∈ s, ‖P.coeff k‖ := by
  apply Finset.sum_subset h
  intro k _ hk
  rw [Polynomial.notMem_support_iff.mp hk,norm_zero]

theorem endpointNorm_add (P Q : Polynomial ℂ) : endpointNorm (P+Q) ≤ endpointNorm P+endpointNorm Q := by
  let s := P.support ∪ Q.support
  rw [norm_over_cover _ s support_add,norm_over_cover P s Finset.subset_union_left,
    norm_over_cover Q s Finset.subset_union_right,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun k _ => by rw [coeff_add]; exact norm_add_le ..)

@[simp] theorem endpointNorm_monomial (k : ℕ) (a : ℂ) : endpointNorm (monomial k a)=‖a‖ := by
  rw [norm_over_cover _ {k} (support_monomial_subset ..),Finset.sum_singleton]
  simp

theorem endpointNorm_sum {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℂ) :
    endpointNorm (∑ i ∈ s, P i) ≤ ∑ i ∈ s, endpointNorm (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [endpointNorm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    exact (endpointNorm_add ..).trans (add_le_add_right ih _)

theorem endpointNorm_mul (P Q : Polynomial ℂ) : endpointNorm (P*Q) ≤ endpointNorm P*endpointNorm Q := by
  have he (F : Polynomial ℂ) : (∑ k ∈ F.support, monomial k (F.coeff k))=F := F.sum_monomial_eq
  have H : P*Q=∑ i ∈ P.support, ∑ j ∈ Q.support, monomial (i+j) (P.coeff i*Q.coeff j) := by
    conv_lhs => rw [← he P,← he Q,Finset.sum_mul]
    simp only [Finset.mul_sum,monomial_mul_monomial]
  rw [H,endpointNorm,endpointNorm,Finset.sum_mul]
  apply (endpointNorm_sum ..).trans (Finset.sum_le_sum (fun i _ => ?_))
  apply (endpointNorm_sum ..).trans_eq
  simp only [endpointNorm_monomial,norm_mul]
  rw [endpointNorm,Finset.mul_sum]

theorem endpointNorm_prod {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℂ) :
    endpointNorm (∏ i ∈ s, P i) ≤ ∏ i ∈ s, endpointNorm (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [show (1 : Polynomial ℂ)=monomial 0 1 from rfl,endpointNorm_monomial,norm_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.prod_insert ha]
    exact (endpointNorm_mul ..).trans (mul_le_mul_of_nonneg_left ih (endpointNorm_nonneg _))

noncomputable def signFactor (p θ : ℝ) : Polynomial ℂ :=
  monomial 0 ((1-p:ℝ):ℂ)+monomial 1 ((p:ℂ)*phase θ)

private theorem mixed_square (A B x y : ℝ) :
    ‖(A:ℂ)*phase x+(B:ℂ)*phase y‖^2 = (A+B)^2-4*A*B*sin ((x-y)/2)^2 := by
  have h : (A:ℂ)*phase x+(B:ℂ)*phase y=phase y*((B:ℂ)+(A:ℂ)*phase (x-y)) := by
    nth_rw 1 [show x=(x-y)+y by ring]
    rw [phase_add]; ring
  rw [h,norm_mul,phase_norm,one_mul,Complex.sq_norm,Complex.normSq_apply]
  simp only [phase,Complex.exp_mul_I,← Complex.ofReal_sin,← Complex.ofReal_cos,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im]
  have H := cos_two_mul_eq_one_sub ((x-y)/2)
  rw [show 2*((x-y)/2)=x-y by ring] at H
  linear_combination A^2*sin_sq_add_cos_sq (x-y) + 2*A*B*H

/-- A rectangle bound on p,q can be inserted through w(A+B)≤2AB.
The equal mixed endpoints are combined before taking their norm. -/
theorem weighted_pair_bound {p q w : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (hw : 0 ≤ w) (hc : w*(p*(1-q)+(1-p)*q) ≤ 2*(p*(1-q))*((1-p)*q))
    (hpos : 0 < p*(1-q)+(1-p)*q) (x y : ℝ) :
    endpointNorm (signFactor p x*signFactor q y) ≤ exp (-w*sin ((x-y)/2)^2) := by
  let A := p*(1-q)
  let B := (1-p)*q
  let s := sin ((x-y)/2)^2
  have ha : 0 ≤ A := mul_nonneg hp (sub_nonneg.mpr hq')
  have hb : 0 ≤ B := mul_nonneg (sub_nonneg.mpr hp') hq
  change w*(A+B) ≤ 2*A*B at hc
  change 0 < A+B at hpos
  have hs : 0 ≤ s := sq_nonneg _
  have hs' : s ≤ 1 := sin_sq_le_one _
  have hw' : 2*w ≤ A+B := by
    apply le_of_mul_le_mul_right (a := A+B) _ hpos
    nlinarith only [hc,sq_nonneg (A-B)]
  have hnon : 0 ≤ A+B-w*s := by
    nlinarith only [hw',mul_le_mul_of_nonneg_left hs' hw,hw]
  have hmix : ‖(A:ℂ)*phase x+(B:ℂ)*phase y‖ ≤ A+B-w*s := by
    apply (sq_le_sq₀ (norm_nonneg _) hnon).mp
    rw [mixed_square]
    change (A+B)^2-4*A*B*s ≤ _
    nlinarith only [mul_le_mul_of_nonneg_right hc hs,sq_nonneg (w*s)]
  have he : signFactor p x*signFactor q y =
      monomial 0 (((1-p)*(1-q):ℝ):ℂ)+monomial 1 ((A:ℂ)*phase x+(B:ℂ)*phase y)+
      monomial 2 (((p*q:ℝ):ℂ)*phase x*phase y) := by
    unfold signFactor
    rw [add_mul,mul_add,mul_add]
    simp only [monomial_mul_monomial,zero_add,add_zero,show 1+1=2 from rfl]
    simp only [A,B,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one,map_add]
    ring_nf
  rw [he]
  apply (endpointNorm_add ..).trans ((add_le_add_left (endpointNorm_add ..) _).trans _)
  simp only [endpointNorm_monomial,Complex.norm_real,Real.norm_eq_abs,norm_mul,phase_norm,mul_one,
    abs_of_nonneg hp,abs_of_nonneg hq,abs_of_nonneg (sub_nonneg.mpr hp'),abs_of_nonneg (sub_nonneg.mpr hq')]
  apply le_trans _ (Real.add_one_le_exp (-w*s))
  dsimp only [A,B] at hmix
  linarith only [hmix]

end CentralUnimodality.MarkedExcursion
