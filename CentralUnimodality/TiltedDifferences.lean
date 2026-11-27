module

public import CentralUnimodality.HitTiltCost
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Signed errors on adjacent ranks under an auxiliary tilt. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

theorem rankEvent_nonneg (c : ℝ) (m j : ℕ) (A : Finset (List Bool)) :
    0 ≤ rankEvent c m j A := Finset.sum_nonneg (fun _ _ => (signMass_pos ..).le)

private theorem exp_small_step {u : ℝ} (hu : 0 ≤ u) (hsmall : u ≤ 1/8192) :
    exp u ≤ 1001/1000 ∧ exp u-1 ≤ (1001/1000)*u := by
  have h : (1-u)*exp u ≤ 1 := by
    have he := mul_le_mul_of_nonneg_right (add_one_le_exp (-u)) (exp_pos u).le
    rw [← exp_add,neg_add_cancel,exp_zero] at he
    linarith only [he]
  have h₁ : exp u ≤ 1001/1000 := by
    apply (le_of_mul_le_mul_left _ (show 0 < 1-u by linarith))
    linarith
  exact ⟨h₁,by linarith only [h,mul_le_mul_of_nonneg_right h₁ hu]⟩

/-- At any neighboring rank, recenter the change of measure at a common j. -/
theorem change_at_neighbor (c z : ℝ) {m : ℕ} (j k : ℕ) (A : Finset (List Bool))
    (hA : A ⊆ words m) :
    rankEvent c m k A = exp (2*z*((k:ℝ)-j)) *
      (rankChange c z j m * rankEvent (c+z) m k A) := by
  rw [change_rank_tilt c (c+z) k A hA,rankChange,show c+z-c=z by ring]
  have he : exp (2*z*k) = exp (2*z*((k:ℝ)-j))*exp (2*z*j) := by rw [← exp_add]; congr 1; ring
  rw [he]; ring

/-- The two signed finite-difference errors in (5), for the same fixed
event at three adjacent ranks. A common positive normalization may be
applied to all three masses. -/
theorem change_difference_bounds (c : ℝ) {z : ℝ} (hz : 0 ≤ z) (hsmall : 2*z ≤ 1/8192)
    {m : ℕ} (j : ℕ) (A : Finset (List Bool)) (hA : A ⊆ words m) :
    let F := fun k => rankEvent c m k A
    let X := fun k => rankChange c z (j+1:ℕ) m * rankEvent (c+z) m k A
    let B := (1001/1000:ℝ)
    F (j+2)-F (j+1) ≤ B*|X (j+2)-X (j+1)| + B*(2*z)*X (j+1) ∧
    -(F j-2*F (j+1)+F (j+2)) ≤ -(X j-2*X (j+1)+X (j+2)) +
      B*(2*z)*(|X (j+2)-X (j+1)|+|X (j+1)-X j|) := by
  let X := fun k => rankChange c z (j+1:ℕ) m * rankEvent (c+z) m k A
  let u := 2*z
  let B := (1001/1000:ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hX (k) : 0 ≤ X k := mul_nonneg (rankChange_pos ..).le (rankEvent_nonneg ..)
  have hmid : rankEvent c m (j+1) A = X (j+1) := by
    simpa only [sub_self,mul_zero,exp_zero,one_mul] using change_at_neighbor c z (j+1) (j+1) A hA
  have hlo : rankEvent c m j A = exp (-u)*X j := by
    rw [change_at_neighbor c z (j+1) j A hA]
    congr 2; dsimp [u]; push_cast; ring
  have hhi : rankEvent c m (j+2) A = exp u*X (j+2) := by
    rw [change_at_neighbor c z (j+1) (j+2) A hA]
    congr 2; dsimp [u]; push_cast; ring
  dsimp only
  change _ ≤ B*|X (j+2)-X (j+1)|+B*u*X (j+1) ∧ _ ≤ -(X j-2*X (j+1)+X (j+2))+_
  rw [hmid,hlo,hhi]
  obtain ⟨hB,hBu⟩ := exp_small_step hu hsmall
  change exp u ≤ B at hB
  change exp u-1 ≤ B*u at hBu
  constructor
  · have hdiff := mul_le_mul (le_abs_self (X (j+2)-X (j+1))) hB (exp_pos u).le (abs_nonneg _)
    linarith only [hdiff,mul_le_mul_of_nonneg_right hBu (hX (j+1))]
  · let V := |X (j+2)-X (j+1)|+|X (j+1)-X j|
    have hd : X j-X (j+2) ≤ V := by
      dsimp only [V]
      linarith only [neg_abs_le (X (j+2)-X (j+1)),neg_abs_le (X (j+1)-X j)]
    have hs : sinh u ≤ B*u := by linarith only [cosh_add_sinh (x:=u),one_le_cosh u,hBu]
    have hcross := mul_le_mul hd hs (sinh_nonneg_iff.mpr hu) (show 0 ≤ V from add_nonneg (abs_nonneg _) (abs_nonneg _))
    have hsum := mul_nonneg (sub_nonneg.mpr (one_le_cosh u)) (add_nonneg (hX j) (hX (j+2)))
    rw [← cosh_add_sinh (x:=u),← cosh_add_sinh (x:=-u),cosh_neg,sinh_neg]
    dsimp only [V,B,u,X] at hcross hsum ⊢
    linarith only [hcross,hsum]

/-- Strict negative second difference under a common tilt gives strict
log-concavity of the original integer rank counts at that site. -/
theorem rank_curvature_of_tilt (c : ℝ) (m j : ℕ)
    (h : rankEvent c m j (ballots m) + rankEvent c m (j+2) (ballots m) <
      2*rankEvent c m (j+1) (ballots m)) :
    rankCount m j * rankCount m (j+2) < (rankCount m (j+1))^2 := by
  let F := fun k => rankEvent c m k (ballots m)
  have hF (k) : 0 ≤ F k := rankEvent_nonneg ..
  have H : F j + F (j+2) < 2*F (j+1) := h
  have H' := (sq_lt_sq₀ (add_nonneg (hF j) (hF (j+2))) (mul_nonneg (by norm_num) (hF (j+1)))).mpr H
  have hprod : F j * F (j+2) < F (j+1)^2 := by nlinarith only [H',sq_nonneg (F j - F (j+2))]
  let Z := rankNormalizer c m
  have hscaled := mul_lt_mul_of_pos_left hprod (sq_pos_of_pos (rankNormalizer_pos c m))
  have group₁ : Z^2*(F j*F (j+2)) = (F j*Z)*(F (j+2)*Z) := by ring
  have group₂ : Z^2*F (j+1)^2 = (F (j+1)*Z)^2 := by ring
  rw [group₁,group₂] at hscaled
  dsimp only [Z,F] at hscaled
  rw [ballot_rank_mass,ballot_rank_mass,ballot_rank_mass,mul_pow,mul_mul_mul_comm] at hscaled
  have he : exp (-2*c*j)*exp (-2*c*(j+2:ℕ)) = exp (-2*c*(j+1:ℕ))^2 := by
    rw [← exp_add, sq,← exp_add]; congr 1; push_cast; ring
  rw [he] at hscaled
  exact_mod_cast (lt_of_mul_lt_mul_right hscaled (sq_nonneg _))

end CentralUnimodality.MarkedExcursion
