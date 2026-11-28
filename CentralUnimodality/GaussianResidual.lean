module

public import CentralUnimodality.ReturnSplitResidual
public import CentralUnimodality.GaussianSymbols

/-! Compare the residual for a real trial profile directly with a finite
sum of Gaussians. Every input error is explicit in the size and frequency. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open PowerSeries Real

noncomputable def trialSeries (f : ℕ → ℝ) : PowerSeries ℂ :=
  mk fun i => ((survival (i/2)*f (i/2):ℝ):ℂ)

theorem trial_normalized (f : ℕ → ℝ) (j σ : ℕ) (hs : σ≤1) :
    coeff (2*j+σ) (trialSeries f)/(survival j:ℂ)=(f j:ℂ) := by
  have div : (2*j+σ)/2=j := by omega
  have hp : (survival j:ℂ)≠0 := by exact_mod_cast (survival_pos j).ne'
  rw [trialSeries,coeff_mk,div,Complex.ofReal_mul]
  field_simp

private theorem fourthSum_mono : Monotone fourthSum := by
  apply monotone_nat_of_le_succ
  intro i
  unfold fourthSum
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (by positivity)

noncomputable def gaussianResidual (ω : ℝ) (f : ℕ → ℝ) (σ N : ℕ) : ℝ :=
  exp (-freeExponent ω (2*N+σ)) -
    average N (fun k => exp (-bridgeExponent ω k)*f (N-k))

/-- The true complex residual is enclosed by quadrature on the discrete
split law, including the finite-size terms in each Gaussian variance. -/
theorem gaussian_residual_error {ω M : ℝ} (f : ℕ → ℝ) {N σ : ℕ}
    (hs : σ≤1) (ha : |ω| * (2*N+σ:ℕ)≤1)
    (hf : ∀ j≤N, |f j|≤M) :
    ‖parityResidual ω (trialSeries f) σ N-(gaussianResidual ω f σ N:ℂ)‖ ≤
      3/4*ω^4*fourthSum (2*N+σ) + 8/5*ω^4*fourthSum N*M := by
  let G := fun k => exp (-bridgeExponent ω k)*f (N-k)
  have mean : complexAverage N (fun k => (G k:ℂ))=(average N G:ℂ) := by
    simp [complexAverage,average]
  have approx : ‖complexAverage N (profile ω (trialSeries f) σ N)-(average N G:ℂ)‖ ≤
      8/5*ω^4*fourthSum N*M := by
    rw [← mean]
    apply norm_average_minus
    intro k hk
    have hkn : (2*k:ℝ)≤(2*N+σ:ℕ) := by exact_mod_cast (by omega : 2*k≤2*N+σ)
    have angle := (mul_le_mul_of_nonneg_left hkn (abs_nonneg ω)).trans ha
    rw [profile,trial_normalized f _ σ hs]
    simp only [G,Complex.ofReal_mul,← sub_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have err := (bridge_gaussian angle).trans (mul_le_mul_of_nonneg_left
      (fourthSum_mono hk) (by positivity : 0≤8/5*ω^4))
    exact mul_le_mul err (hf _ (Nat.sub_le ..)) (abs_nonneg _) (by
      unfold fourthSum; positivity)
  have free := free_gaussian ha
  rw [residual_split _ _ _ _ hs,gaussianResidual,Complex.ofReal_sub,sub_sub_sub_comm]
  exact (norm_sub_le ..).trans (add_le_add free approx)

end CentralUnimodality.ReturnSplit
