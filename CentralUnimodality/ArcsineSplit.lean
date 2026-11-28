module

public import CentralUnimodality.GammaPolynomialSplit
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Integration of the last-return polynomial product against the arcsine
law. The angular representation is nonsingular at both split endpoints. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit

open Real Polynomial intervalIntegral

noncomputable def arc (f : ℝ → ℝ) : ℝ := (∫ t in 0..π, f (sin t ^ 2))/π

theorem sin_sq_unit (t : ℝ) : sin t ^ 2 ∈ Set.Icc (0:ℝ) 1 :=
  ⟨sq_nonneg _, by nlinarith only [sin_sq_add_cos_sq t,sq_nonneg (cos t)]⟩

theorem arc_congr {f g : ℝ → ℝ} (h : ∀ x ∈ Set.Icc (0:ℝ) 1, f x=g x) :
    arc f=arc g := by
  unfold arc
  congr 1
  apply integral_congr
  intro t _
  exact h _ (sin_sq_unit t)

theorem arc_bound (f : ℝ → ℝ) {C : ℝ} (h : ∀ x ∈ Set.Icc (0:ℝ) 1, |f x|≤C) :
    |arc f|≤C := by
  rw [arc,abs_div,abs_of_pos pi_pos,div_le_iff₀ pi_pos]
  simpa [Real.norm_eq_abs,abs_of_pos pi_pos] using
    (norm_integral_le_of_norm_le_const (a:=0) (b:=π) (f:=fun t => f (sin t^2))
      (fun t _ => (Real.norm_eq_abs _).trans_le (h _ (sin_sq_unit t))))

theorem arc_const (c : ℝ) : arc (fun _ => c)=c := by simp [arc,pi_ne_zero]

theorem arc_const_mul (c : ℝ) (f : ℝ → ℝ) : arc (fun x => c*f x)=c*arc f := by
  rw [arc,integral_const_mul,arc]; ring

theorem arc_sub {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    arc (fun x => f x-g x)=arc f-arc g := by
  rw [arc,integral_sub,arc,arc,sub_div]
  all_goals apply Continuous.intervalIntegrable; fun_prop

theorem arc_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) : arc (fun x => ∑ i ∈ s, f i x)=∑ i ∈ s, arc (f i) := by
  simp only [arc,← Finset.sum_div]
  congr 1
  exact integral_finsetSum (f:=fun i t => f i (sin t^2))
    (fun i hi => ((hf i hi).comp (continuous_sin.pow 2)).intervalIntegrable 0 π)

theorem arc_power (a : ℕ) : arc (fun x => x^a)=survival a := by
  rw [arc]
  simp only [← pow_mul,integral_sin_pow_even]
  rw [mul_div_cancel_left₀ _ pi_ne_zero]
  induction a with
  | zero => simp [survival]
  | succ a ih =>
    rw [Finset.prod_range_succ,ih,survival_succ]
    ring

theorem betaWeight_step (a b : ℕ) :
    betaWeight a (b+1)=betaWeight a b-betaWeight (a+1) b := by
  simp only [betaWeight,Nat.factorial_succ,survival_succ,Nat.cast_mul,
    Nat.add_succ,show a+1+b=(a+b)+1 by omega,Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem arc_mixed (a b : ℕ) : arc (fun x => x^a*(1-x)^b)=betaWeight a b := by
  induction b generalizing a with
  | zero => simp [arc_power,betaWeight,survival,Nat.factorial_ne_zero]
  | succ b ih =>
    have eq : (fun x : ℝ => x^a*(1-x)^(b+1))=
        fun x => x^a*(1-x)^b-x^(a+1)*(1-x)^b := by funext x; rw [pow_succ,pow_succ]; ring
    rw [eq,arc_sub (by fun_prop) (by fun_prop),ih,ih,betaWeight_step]

/-- The angular integral and the discrete gamma convolution have the
same product polynomial, with no size or degree restriction. -/
theorem arc_polynomial (v : ℝ) (B F : ℝ[X]) :
    arc (fun x => B.eval (v*x)*F.eval (v*(1-x)))=(betaProduct B F).eval v := by
  let h := fun a b : ℕ => B.coeff a*F.coeff b*v^(a+b)
  have expand (x : ℝ) : B.eval (v*x)*F.eval (v*(1-x))=
      ∑ a ∈ B.support, ∑ b ∈ F.support, h a b*(x^a*(1-x)^b) := by
    rw [B.eval_eq_sum,F.eval_eq_sum]
    simp only [Polynomial.sum_def,Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [h,pow_add,mul_pow]; ring
  simp_rw [expand]
  rw [arc_sum _ _ (by intro i _; fun_prop)]
  simp only [betaProduct,Polynomial.eval_finsetSum,Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro a _
  rw [arc_sum _ _ (by intro i _; fun_prop)]
  apply Finset.sum_congr rfl
  intro b _
  rw [arc_const_mul,arc_mixed]
  dsimp [h]; ring

end CentralUnimodality.ReturnSplit
