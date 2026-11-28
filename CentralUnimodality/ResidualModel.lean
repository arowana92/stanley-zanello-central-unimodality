module

public import CentralUnimodality.GammaPolynomialSplit

/-! A smooth residual model and a uniformly small discretization error
enter the inverse last-return estimate with different constants. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries

theorem inverseAt_dist (ω : ℝ) (N : ℕ) (E G : ℕ → ℂ) {v : ℝ}
    (hv : ∀ j≤N, ‖E j-G j‖≤v) :
    ‖inverseAt ω N E-inverseAt ω N G‖≤(2-survival N)*v := by
  have hv₀ := (norm_nonneg _).trans (hv N le_rfl)
  have eq : inverseAt ω N E-inverseAt ω N G = E N-G N-
      ∑ j ∈ Finset.range (N+1), returnSymbol ω j*(E (N-j)-G (N-j)) := by
    simp only [inverseAt,mul_sub,Finset.sum_sub_distrib]
    abel
  rw [eq]
  apply (norm_sub_le ..).trans
  have hs : ‖∑ j ∈ Finset.range (N+1), returnSymbol ω j*(E (N-j)-G (N-j))‖≤
      (1-survival N)*v := by
    apply (norm_sum_le ..).trans
    rw [← returnMass_sum,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul]
    exact mul_le_mul (norm_returnSymbol_le ..) (hv _ (Nat.sub_le ..)) (norm_nonneg _) (by
      unfold returnMass; positivity)
  linarith only [hv N le_rfl,hs]

/-- At the natural frequency scale, the smooth model costs a bounded
factor and the uniformly bounded remainder costs at most four square
roots of the half-length after conditioning on survival. -/
theorem amplitude_of_residual_model {n δ : ℕ} (hδ : δ≤1) (hN : 0<n+δ)
    (θ : ℝ) (V : PowerSeries ℂ) (G : ℕ → ℂ) {ξ e b v : ℝ}
    (hfreq : |θ| * (n+δ:ℕ)*Real.sqrt (n+δ:ℕ) ≤ ξ)
    (hend : ‖G (n+δ)‖≤e)
    (hvar : ∀ j≤n+δ, ‖G (n+δ)-G (n+δ-j)‖≤j*(b/(n+δ:ℕ)))
    (hrem : ∀ j≤n+δ, ‖parityResidual (θ/2) V (1-δ) j-G j‖≤v) :
    |signedAmplitude n δ θ-residualAmplitude (2*n+δ) V| ≤
      (1+ξ/2)*e+b+4*Real.sqrt (n+δ:ℕ)*v := by
  let N := n+δ
  let r := survival N
  have hr : 0<r := survival_pos _
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hv : 0≤v := (norm_nonneg _).trans (hrem N le_rfl)
  have he : 0≤e := (norm_nonneg _).trans hend
  have hc : 0≤r+N*(|θ/2|/2) := by positivity
  have hlen : 2*n+δ+1=2*N+(1-δ) := by dsimp [N]; omega
  have hhalf : (2*n+δ+1)/2=N := by dsimp [N]; omega
  have err := inverseAt_dist (θ/2) N _ G hrem
  have model := inverse_smooth_bound (θ/2) N G hvar
  have hmodel : ‖inverseAt (θ/2) N G‖ ≤ (r+N*(|θ/2|/2))*e+(N*r)*(b/N) :=
    model.trans (add_le_add (mul_le_mul_of_nonneg_left hend hc) le_rfl)
  have combined := (norm_add_le _ _).trans (add_le_add err hmodel)
  rw [sub_add_cancel] at combined
  have hscale : (N:ℝ)*(|θ/2|/2)/r ≤ ξ/2 := by
    have hinv := mul_le_mul_of_nonneg_left (survival_inv_le hN)
      (show 0≤(N:ℝ)*(|θ|/4) by positivity)
    rw [abs_div,abs_of_pos (show (0:ℝ)<2 by norm_num),div_eq_mul_inv]
    change |θ| * (N:ℝ)*Real.sqrt N≤ξ at hfreq
    dsimp only [r,N] at *
    linarith only [hinv,hfreq]
  have hvscale : (2-r)*v/r ≤ 4*Real.sqrt N*v := calc
    _ ≤ 2*v/r := div_le_div_of_nonneg_right (by nlinarith only [mul_nonneg hr.le hv]) hr.le
    _ = 2*v*r⁻¹ := div_eq_mul_inv ..
    _ ≤ 2*v*(2*Real.sqrt N) := mul_le_mul_of_nonneg_left (survival_inv_le hN) (by positivity)
    _ = _ := by ring
  rw [signedAmplitude,residualAmplitude,← sub_div,abs_div,hhalf,abs_of_pos hr,hlen,← Complex.sub_re]
  apply (div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) hr.le).trans
  rw [← map_sub,strict_error_eq_inverseAt _ _ _ _ (by omega)]
  apply (div_le_div_of_nonneg_right combined hr.le).trans
  change ((2-r)*v+((r+N*(|θ/2|/2))*e+(N*r)*(b/N)))/r ≤ _
  have id : ((2-r)*v+((r+N*(|θ/2|/2))*e+(N*r)*(b/N)))/r =
      (1+N*(|θ/2|/2)/r)*e+b+(2-r)*v/r := by field_simp [hr.ne',hn.ne']; ring
  rw [id]
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right (add_le_add le_rfl hscale) he) le_rfl)
    hvscale

end CentralUnimodality
