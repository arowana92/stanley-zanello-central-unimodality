module

public import CentralUnimodality.RankLossBins

/-! Scale the three signed event costs in a common surviving-prefix
probability. The shift on a neighboring lattice site costs 2zσ. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

noncomputable def restoredCost (r : Fin 3) (u : ℝ) (a : Fin 3 → ℝ) : ℝ :=
  if r=0 then a 0 else if r=1 then (1001/1000)*a 1+(1001/1000)*u*a 0
  else a 2+2*(1001/1000)*u*a 1

/-- Express a saddle's natural-rank triple as signed integer differences. -/
theorem signed_of_neighbors (A : ℤ → ℝ) (F : ℕ → ℝ) (hF : ∀ k : ℕ, A k=F k) (j : ℕ)
    (a : Fin 3 → ℝ) (u : ℝ)
    (H : F (j+1) ≤ a 0 ∧ F (j+2)-F (j+1) ≤ 1001/1000*a 1+1001/1000*u*a 0 ∧
      -(F j-2*F (j+1)+F (j+2)) ≤ a 2+2*(1001/1000)*u*a 1) (r : Fin 3) :
    signedRank r (j+1:ℕ) A ≤ restoredCost r u a := by
  fin_cases r
  · change A (j+1:ℕ) ≤ a 0; rw [hF]; exact H.1
  · change A ((j+1:ℕ)+1)-A (j+1:ℕ) ≤ _
    rw [show ((j+1:ℕ):ℤ)+1=(j+2:ℕ) by omega,hF,hF]; exact H.2.1
  · change -(A ((j+1:ℕ)-1)+A ((j+1:ℕ)+1)-2*A (j+1:ℕ)) ≤ _
    rw [show ((j+1:ℕ):ℤ)-1=j by omega,show ((j+1:ℕ):ℤ)+1=(j+2:ℕ) by omega,hF,hF,hF]
    change _ ≤ a 2+2*(1001/1000)*u*a 1
    linarith only [H.2.2]

/-- A common multiplicative event bound can be pulled out of all three
orders after multiplying the site bounds by σ, σ² and σ³. -/
theorem scale_restored_cost {σ P u du prob : ℝ} (hσ : 0 ≤ σ)
    (hu : 0 ≤ u) (hdu : σ*u ≤ du) (hp : 0 ≤ prob) (U A : Fin 3 → ℝ) (hA : ∀ r, 0 ≤ A r)
    (H : ∀ r : Fin 3, σ^(r.val+1)/P*U r ≤ prob*A r) (r : Fin 3) :
    σ^(r.val+1)/P*restoredCost r u U ≤ prob*restoredCost r du A := by
  have H₀ : σ/P*U 0 ≤ prob*A 0 := by simpa using H 0
  have H₁ : σ^2/P*U 1 ≤ prob*A 1 := H 1
  have H₂ : σ^3/P*U 2 ≤ prob*A 2 := H 2
  have extra {x y : ℝ} (hx : x ≤ prob*y) (hy : 0 ≤ y) :
      σ*u*x ≤ du*(prob*y) :=
    (mul_le_mul_of_nonneg_left hx (mul_nonneg hσ hu)).trans (mul_le_mul_of_nonneg_right hdu (mul_nonneg hp hy))
  fin_cases r
  · simpa [restoredCost] using H₀
  · change σ^2/P*((1001/1000)*U 1+(1001/1000)*u*U 0) ≤ prob*((1001/1000)*A 1+(1001/1000)*du*A 0)
    have hh := extra H₀ (hA 0)
    simp only [div_eq_mul_inv] at H₁ hh ⊢
    linear_combination (1001/1000)*H₁ + (1001/1000)*hh
  · change σ^3/P*(U 2+2*(1001/1000)*u*U 1) ≤ prob*(A 2+2*(1001/1000)*du*A 1)
    have hh := extra H₁ (hA 1)
    simp only [div_eq_mul_inv] at H₂ hh ⊢
    linear_combination H₂ + (2*(1001/1000))*hh

end CentralUnimodality.MarkedExcursion
