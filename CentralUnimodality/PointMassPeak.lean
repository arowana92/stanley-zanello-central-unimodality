module

public import CentralUnimodality.FirstHitCount
public import CentralUnimodality.RankArcBounds

/-! At fixed positive endpoint a, the free-walk point probability over
compatible lengths is largest at time a². This reduces the uniform bound
on a times that probability to one binomial coefficient per endpoint. -/
@[expose] public section

namespace CentralUnimodality

noncomputable def pointMass (a d : ℕ) : ℝ :=
  ((a+2*d).choose d:ℝ)/(2:ℝ)^(a+2*d)

theorem pointMass_pos (a d : ℕ) : 0 < pointMass a d :=
  div_pos (by exact_mod_cast Nat.choose_pos (by omega : d ≤ a+2*d)) (by positivity)

private theorem choose_time_step (a d : ℕ) :
    (a+2*d+2).choose (d+1)*(a+d+1)*(d+1) =
      (a+2*d+2)*(a+2*d+1)*(a+2*d).choose d := by
  let j := a+2*d
  have h₁ := Nat.add_one_mul_choose_eq j d
  have h₂ := Nat.add_one_mul_choose_eq (j+1) (a+d)
  rw [Nat.choose_symm_of_eq_add (by dsimp [j]; omega : j+1 = (a+d)+(d+1)),
    Nat.choose_symm_of_eq_add (by dsimp [j]; omega : j+1+1 = (a+d+1)+(d+1))] at h₂
  change (j+1+1).choose (d+1)*(a+d+1)*(d+1) = (j+1+1)*(j+1)*j.choose d
  rw [← h₂, mul_assoc,← h₁, ← mul_assoc]

private theorem pointMass_step (a d : ℕ) :
    pointMass a (d+1)*(4*((a:ℝ)+d+1)*(d+1)) =
      pointMass a d*((a+2*(d:ℝ)+2)*(a+2*(d:ℝ)+1)) := by
  have he : (((a+2*d+2).choose (d+1)):ℝ)*((a:ℝ)+d+1)*(d+1) =
      ((a:ℝ)+2*d+2)*(a+2*d+1)*((a+2*d).choose d) := by exact_mod_cast choose_time_step a d
  rw [pointMass,pointMass,show a+2*(d+1) = (a+2*d)+2 by omega,pow_add]
  field_simp
  linarith only [he]

private theorem mass_increase (a d : ℕ) (h : a+2*d+2 ≤ a^2) :
    pointMass a d ≤ pointMass a (d+1) := by
  have hs : (a:ℝ)+2*d+2 ≤ (a:ℝ)^2 := by exact_mod_cast h
  apply le_of_mul_le_mul_right (a := 4*((a:ℝ)+d+1)*(d+1)) _ (by positivity)
  rw [pointMass_step]
  apply mul_le_mul_of_nonneg_left _ (pointMass_pos ..).le
  nlinarith only [hs]

private theorem mass_decrease (a d : ℕ) (h : a^2 ≤ a+2*d+2) :
    pointMass a (d+1) ≤ pointMass a d := by
  have hs : (a:ℝ)^2 ≤ (a:ℝ)+2*d+2 := by exact_mod_cast h
  apply le_of_mul_le_mul_right (a := 4*((a:ℝ)+d+1)*(d+1)) _ (by positivity)
  rw [pointMass_step]
  apply mul_le_mul_of_nonneg_left _ (pointMass_pos ..).le
  nlinarith only [hs]

theorem peak_time (a : ℕ) : a+2*a.choose 2 = a^2 := by
  cases a with
  | zero => decide
  | succ a =>
    have h := Nat.choose_succ_right_eq (a+1) 1
    simp only [Nat.choose_one_right,Nat.add_sub_cancel] at h
    nlinarith only [h]

theorem pointMass_le_square (a d : ℕ) : pointMass a d ≤ pointMass a (a.choose 2) := by
  have he := peak_time a
  rcases le_total d (a.choose 2) with hd | hd
  · have aux (b : ℕ) (hb : d ≤ b) : b ≤ a.choose 2 → pointMass a d ≤ pointMass a b := by
      induction b, hb using Nat.le_induction with
      | base => simp
      | succ b _ ih =>
        intro h
        exact (ih (by omega)).trans (mass_increase a b (by omega))
    exact aux _ hd le_rfl
  · induction d, hd using Nat.le_induction with
    | base => rfl
    | succ d hd ih => exact (mass_decrease a d (by omega)).trans ih

end CentralUnimodality
