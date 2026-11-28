module

public import CentralUnimodality.GammaSplitMoments
public import CentralUnimodality.GaussianResidual
public import Mathlib.Algebra.Polynomial.Coeff

/-! The polynomial last-return convolution is independent of the time
step. Its evaluation at full rising moments equals the actual discrete
split of two half-rising evaluations, at every size. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit

open Polynomial PowerSeries

noncomputable def gammaValue (mom : ℕ → ℝ) (τ : ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum (fun a => (τ^a*mom a) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))

theorem gammaValue_expand (mom : ℕ → ℝ) (τ : ℝ) (P : ℝ[X]) :
    gammaValue mom τ P=∑ a ∈ P.support, τ^a*mom a*P.coeff a := by
  simp [gammaValue,Polynomial.sum_def]

theorem gammaValue_monomial (mom : ℕ → ℝ) (τ c : ℝ) (a : ℕ) :
    gammaValue mom τ (Polynomial.monomial a c)=τ^a*mom a*c := by
  simp [gammaValue,Polynomial.sum_monomial_index]

noncomputable def betaProduct (B F : ℝ[X]) : ℝ[X] :=
  ∑ a ∈ B.support, ∑ b ∈ F.support,
    Polynomial.monomial (a+b) (B.coeff a*F.coeff b*betaWeight a b)

private theorem average_sum {ι : Type*} (s : Finset ι) (N : ℕ) (v : ι → ℕ → ℝ) :
    average N (fun k => ∑ i ∈ s, v i k)=∑ i ∈ s, average N (v i) := by
  simp only [average,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem gamma_polynomial_split (N : ℕ) (τ : ℝ) (B F : ℝ[X]) :
    average N (fun k => gammaValue (halfRising k) τ B *
      gammaValue (halfRising (N-k)) τ F)=gammaValue (fullRising N) τ (betaProduct B F) := by
  simp only [gammaValue_expand,Finset.sum_mul,Finset.mul_sum]
  calc
    _ = ∑ a ∈ B.support, ∑ b ∈ F.support,
          (τ^(a+b)*B.coeff a*F.coeff b) *
            average N (fun k => halfRising k a*halfRising (N-k) b) := by
      rw [average_sum,Finset.sum_comm (s:=B.support) (t:=F.support)]
      apply Finset.sum_congr rfl
      intro b _
      rw [average_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [← average_mul]
      apply average_congr
      intro k _
      rw [pow_add]; ring
    _ = gammaValue (fullRising N) τ (betaProduct B F) := by
      simp only [rising_split,betaProduct,map_sum,gammaValue_monomial]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := gammaValue_expand ..

/-- Bounds for approximating the free and bridge symbols transfer to the
actual complex residual of a polynomial trial for either parity. -/
theorem gamma_residual_bound {ω τ e d M : ℝ} {σ N : ℕ} (hs : σ≤1) (P B F : ℝ[X])
    (hfree : ‖freeSymbol ω σ N-(gammaValue (fullRising N) τ P:ℂ)‖≤e)
    (hbridge : ∀ k≤N, ‖coeff (2*k) (fairSeries (areaCharacter ω) bridges)/(survival k:ℂ)-
      (gammaValue (halfRising k) τ B:ℂ)‖≤d)
    (hF : ∀ j≤N, |gammaValue (halfRising j) τ F|≤M) (hd : 0≤d) :
    ‖parityResidual ω (trialSeries (fun j => gammaValue (halfRising j) τ F)) σ N-
      (gammaValue (fullRising N) τ (P-betaProduct B F):ℂ)‖≤e+d*M := by
  let f := fun j => gammaValue (halfRising j) τ F
  let b := fun k => gammaValue (halfRising k) τ B
  have eq : complexAverage N (fun k => ((b k*f (N-k):ℝ):ℂ))=
      (gammaValue (fullRising N) τ (betaProduct B F):ℂ) := by
    rw [← gamma_polynomial_split]
    simp [complexAverage,average,b,f]
  have hb := norm_average_minus (N:=N) (profile ω (trialSeries f) σ N)
    (fun k => ((b k*f (N-k):ℝ):ℂ)) (v:=d*M) (by
      intro k hk
      rw [profile,trial_normalized _ _ _ hs,Complex.ofReal_mul,← sub_mul,norm_mul,
        Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul (hbridge k hk) (hF _ (Nat.sub_le ..)) (abs_nonneg _) hd)
  rw [eq] at hb
  rw [residual_split _ _ _ _ hs,map_sub,Complex.ofReal_sub,sub_sub_sub_comm]
  exact (norm_sub_le ..).trans (add_le_add hfree hb)

end CentralUnimodality.ReturnSplit
