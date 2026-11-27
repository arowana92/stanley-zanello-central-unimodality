module

public import CentralUnimodality.CheckResidual
public import CentralUnimodality.HalfLengthResidual

/-! The exported arrays give a conditional amplitude enclosure once the
free and bridge input errors have been bounded. The large integer
congruences account for the complete finite convolutions. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries Residual

theorem checked_half_amplitude {n δ : ℕ} (hδ : δ ≤ 1) (θ : ℝ) {s : ℤ} (hs : 0 < s) (B : ℕ → ℤ)
    (F V E : ℕ → List ℤ) (R : List ℤ) (v e : ℕ) (u p : ℝ)
    (hc : ∀ σ ≤ 1, Residual.check (B σ) s (n+δ+1) (F σ) R (V σ) (E σ) = true)
    (hv : ∀ σ ≤ 1, magnitude (V σ) ≤ v) (he : ∀ σ ≤ 1, magnitude (E σ) ≤ e)
    (hF : ∀ σ ≤ 1, ∀ i ≤ n+δ, ‖coeff i (halfSeries σ (fairSeries (areaCharacter (θ/2)) words) -
      scaledSeries s (rowPolynomial (F σ)))‖ ≤ u)
    (hR : ∀ i ≤ n+δ, ‖coeff i (halfSeries 0 (fairSeries (areaCharacter (θ/2)) bridges) -
      scaledSeries s (rowPolynomial R))‖ ≤ p) :
    |signedAmplitude n δ θ -
      (coeff (n+δ) (scaledSeries s (rowPolynomial (V (1-δ))))).re/survival (n+δ)| ≤
      2*(u+(e:ℝ)/(s:ℝ)^2+((n+δ+1:ℕ):ℝ)*p*((v:ℝ)/s))/survival (n+δ) := by
  apply half_length_amplitude n δ hδ θ (fun σ => scaledSeries s (rowPolynomial (V σ)))
  intro σ hσ i hi
  apply dyadic_residual_bound hs (rowPolynomial (F σ)) (rowPolynomial R) (rowPolynomial (V σ))
    (rowPolynomial (E σ)) _ _ (check_sound (hc σ hσ)) _ (fun k hk => hF σ hσ k (by omega))
    (fun k hk => hR k (by omega)) _ i (by omega)
  · intro k _
    have h := (row_bound (E σ) k).trans (by exact_mod_cast he σ hσ : (magnitude (E σ):ℤ) ≤ e)
    exact_mod_cast h
  · intro k _
    rw [scaledSeries,coeff_mk,norm_div]
    have h := (row_bound (V σ) k).trans (by exact_mod_cast hv σ hσ : (magnitude (V σ):ℤ) ≤ v)
    have hnorm (a : ℤ) : ‖(a:ℂ)‖ = (|a|:ℝ) := by simp
    rw [hnorm,hnorm,abs_of_pos (by exact_mod_cast hs : (0:ℝ) < s)]
    exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by exact_mod_cast hs.le)

end CentralUnimodality
