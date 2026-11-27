module

public import CentralUnimodality.FreeSuffixFourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Fourier inversion for the mass, forward difference and centered
second difference with any integrable lattice transform. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real MeasureTheory

noncomputable def rankDifference {K : Type*} [Field K] (r : Fin 3) (k : ℤ) : (ℤ → K) →ₗ[K] K :=
  let ev (j : ℤ) : (ℤ → K) →ₗ[K] K := LinearMap.proj j
  match r with
  | 0 => ev k
  | 1 => ev (k+1)-ev k
  | _ => ev (k-1)+ev (k+1)-(2:K) • ev k

theorem rankDifference_shift {K : Type*} [Field K] (r : Fin 3) (k z : ℤ) (A : ℤ → K) :
    rankDifference r k (fun j => A (j-z)) = rankDifference r (k-z) A := by
  fin_cases r <;> simp [rankDifference,show k-1-z=k-z-1 by omega,show k+1-z=k-z+1 by omega]

private theorem chord (θ : ℝ) : ‖phase θ-1‖ ≤ |θ| := by
  simpa only [phase,mul_comm,Real.norm_eq_abs] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ))

/-- The exact multiplier costs at the three orders are bounded by |θ|ʳ,
uniformly in the phase center and the lattice site. -/
theorem rankDifference_phase (r : Fin 3) (k : ℤ) (θ μ : ℝ) (v : ℂ) :
    ‖rankDifference r k (fun j => v*phase (-θ*((j:ℝ)-μ)))‖ ≤ ‖v‖*|θ|^r.val := by
  let F := fun j : ℤ => v*phase (-θ*((j:ℝ)-μ))
  have shifts : F (k+1)=F k*phase (-θ) ∧ F (k-1)=F k*phase θ := by
    simp only [F,Int.cast_add,Int.cast_one,Int.cast_sub,mul_assoc,← phase_add]
    constructor <;> congr 2 <;> ring
  have hf : ‖F k‖=‖v‖ := by simp [F]
  change ‖rankDifference r k F‖ ≤ _
  fin_cases r
  · simp [rankDifference,hf]
  · change ‖F (k+1)-F k‖ ≤ ‖v‖*|θ|^1
    rw [shifts.1,← mul_sub_one,norm_mul,hf,pow_one]
    exact mul_le_mul_of_nonneg_left (by simpa using chord (-θ)) (norm_nonneg _)
  · change ‖F (k-1)+F (k+1)-2*F k‖ ≤ ‖v‖*|θ|^2
    have hp : phase θ*phase (-θ)=1 := by rw [← phase_add]; simp
    have he : F k*phase θ+F k*phase (-θ)-2*F k = -F k*(phase θ-1)*(phase (-θ)-1) := by
      linear_combination F k*hp
    rw [shifts.1,shifts.2,he,norm_mul,norm_mul,norm_neg,hf,pow_two,← mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (chord θ) (norm_nonneg _))
      (by simpa using chord (-θ)) (norm_nonneg _) (by positivity)

theorem lattice_difference_integral (B : ℝ → ℂ) (μ : ℝ) (A : ℤ → ℝ)
    (hi : ∀ k : ℤ, Integrable (fun θ => B θ*phase (-θ*((k:ℝ)-μ))))
    (inv : ∀ k : ℤ, (∫ θ, B θ*phase (-θ*((k:ℝ)-μ))) = (A k:ℂ))
    (r : Fin 3) (k : ℤ) {g : ℝ → ℝ} (hg : Integrable g)
    (hdom : ∀ θ : ℝ, ‖B θ‖*|θ|^r.val ≤ g θ) : |rankDifference r k A| ≤ ∫ θ, g θ := by
  let F := fun (j : ℤ) (θ : ℝ) => B θ*phase (-θ*((j:ℝ)-μ))
  have H := norm_integral_le_of_norm_le hg (f := fun θ => rankDifference r k (fun j => F j θ))
    (Filter.Eventually.of_forall (fun θ => (rankDifference_phase r k θ μ (B θ)).trans (hdom θ)))
  have he : (∫ θ, rankDifference r k (fun j => F j θ)) = ((rankDifference r k A:ℝ):ℂ) := by
    fin_cases r
    · exact inv k
    · change (∫ θ, F (k+1) θ-F k θ)=((A (k+1)-A k:ℝ):ℂ)
      rw [integral_sub (hi _) (hi _),inv,inv,Complex.ofReal_sub]
    · change (∫ θ, F (k-1) θ+F (k+1) θ-2*F k θ)=((A (k-1)+A (k+1)-2*A k:ℝ):ℂ)
      have hp : Integrable (fun θ => F (k-1) θ+F (k+1) θ) := (hi _).add (hi _)
      rw [integral_sub hp ((hi k).const_mul (2:ℂ)),integral_add (hi _) (hi _),integral_const_mul]
      rw [inv,inv,inv]; push_cast; rfl
  rwa [he,Complex.norm_real,Real.norm_eq_abs] at H

end CentralUnimodality.MarkedExcursion
