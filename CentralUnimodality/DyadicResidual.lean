module

public import CentralUnimodality.PackedResidual

/-! Transfer a checked integer convolution to a true complex power-series
residual, allowing enclosures for the free and bridge inputs. -/
@[expose] public section

namespace CentralUnimodality

noncomputable def scaledSeries (s : ℤ) (P : Polynomial ℤ) : PowerSeries ℂ :=
  PowerSeries.mk fun i => (P.coeff i:ℂ)/(s:ℂ)

private theorem scaled_coeff (s : ℤ) (P : Polynomial ℤ) (i : ℕ) :
    PowerSeries.coeff i (scaledSeries s P) = (P.coeff i:ℂ)/(s:ℂ) := PowerSeries.coeff_mk ..

private theorem scaled_product (s : ℤ) (R V : Polynomial ℤ) (i : ℕ) :
    PowerSeries.coeff i (scaledSeries s R*scaledSeries s V) = ((R*V).coeff i:ℂ)/(s:ℂ)^2 := by
  rw [PowerSeries.coeff_mul,Polynomial.coeff_mul]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  rw [scaled_coeff,scaled_coeff]
  ring

theorem scaled_residual {s : ℤ} (hs : 0 < s) {F R V E : Polynomial ℤ} {i : ℕ}
    (hc : s*F.coeff i-(R*V).coeff i = E.coeff i) :
    ‖PowerSeries.coeff i (scaledSeries s F-scaledSeries s R*scaledSeries s V)‖ =
      (|E.coeff i|:ℝ)/(s:ℝ)^2 := by
  have hs' : (s:ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have he : (s:ℂ)*(F.coeff i:ℂ)-((R*V).coeff i:ℂ) = E.coeff i := by exact_mod_cast hc
  rw [map_sub,scaled_coeff,scaled_product]
  rw [show (F.coeff i:ℂ)/s-((R*V).coeff i:ℂ)/(s:ℂ)^2 =
    ((s:ℂ)*(F.coeff i:ℂ)-((R*V).coeff i:ℂ))/(s:ℂ)^2 by field_simp]
  rw [he,norm_div,norm_pow]
  simp

private theorem coeff_product_norm {L i : ℕ} (hi : i < L) (R V : PowerSeries ℂ)
    {p v : ℝ} (hp : ∀ k < L, ‖PowerSeries.coeff k R‖ ≤ p) (hv : ∀ k < L, ‖PowerSeries.coeff k V‖ ≤ v) :
    ‖PowerSeries.coeff i (R*V)‖ ≤ (L:ℝ)*p*v := by
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply (norm_sum_le ..).trans
  have h := Finset.sum_le_sum (s := Finset.range (i+1)) (fun j hj =>
    show ‖PowerSeries.coeff j R*PowerSeries.coeff (i-j) V‖ ≤ p*v by
      rw [norm_mul]
      exact mul_le_mul (hp j (by have := Finset.mem_range.mp hj; omega)) (hv _ (by omega))
        (norm_nonneg _) ((norm_nonneg _).trans (hp i hi)))
  apply h.trans
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  rw [mul_assoc (L:ℝ)]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi : (i:ℝ)+1 ≤ L)
    (mul_nonneg ((norm_nonneg _).trans (hp i hi)) ((norm_nonneg _).trans (hv i hi)))

/-- With certified input errors u and p, an integer residual of magnitude
at most e gives the analytic bound below for every coefficient through
L-1. The power series V is an arbitrary proposed dyadic approximation. -/
theorem dyadic_residual_bound {s : ℤ} (hs : 0 < s) {L : ℕ} (F R V E : Polynomial ℤ)
    (free bridge : PowerSeries ℂ) {u p v e : ℝ}
    (hc : ∀ i < L, s*F.coeff i-(R*V).coeff i = E.coeff i)
    (herr : ∀ i < L, (|E.coeff i|:ℝ) ≤ e)
    (hF : ∀ i < L, ‖PowerSeries.coeff i (free-scaledSeries s F)‖ ≤ u)
    (hR : ∀ i < L, ‖PowerSeries.coeff i (bridge-scaledSeries s R)‖ ≤ p)
    (hV : ∀ i < L, ‖PowerSeries.coeff i (scaledSeries s V)‖ ≤ v) :
    ∀ i < L, ‖PowerSeries.coeff i (free-bridge*scaledSeries s V)‖ ≤
      u+e/(s:ℝ)^2+(L:ℝ)*p*v := by
  intro i hi
  have he : free-bridge*scaledSeries s V = ((free-scaledSeries s F) +
      (scaledSeries s F-scaledSeries s R*scaledSeries s V))-(bridge-scaledSeries s R)*scaledSeries s V := by ring
  rw [he,map_sub,map_add]
  apply (norm_sub_le ..).trans
  apply add_le_add _ (coeff_product_norm hi _ _ hR hV)
  apply (norm_add_le ..).trans
  apply add_le_add (hF i hi)
  rw [scaled_residual hs (hc i hi)]
  exact div_le_div_of_nonneg_right (herr i hi) (sq_nonneg _)

end CentralUnimodality
