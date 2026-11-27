module

public import CentralUnimodality.BallotCut

/-! The Carlitz–Riordan recursion for the very same corank weight as the
staircase polynomials. Remove the last down-step, then cut at the last zero. -/
@[expose] public section

namespace CentralUnimodality

theorem ballot_snoc_iff (w : List Bool) (b : Bool) :
    BallotFrom 0 (w++[b]) ↔ BallotFrom 0 w ∧ 0 ≤ displacement w + step b := by
  simp only [ballot_iff_heights, heights_append, List.forall_mem_append]
  simp [heights]

theorem ballot_endpoint_nonneg {w : List Bool} (hw : BallotFrom 0 w) : 0 ≤ displacement w := by
  induction w using List.reverseRecOn with
  | nil => decide
  | append_singleton w b _ =>
    rw [displacement_snoc]
    exact ((ballot_snoc_iff w b).mp hw).2

private def finalDown (w : List Bool) := w++[true]

private theorem dycks_finalDown (n : ℕ) : dycks (n+1) =
    ((ballots (2*n+1)).filter (fun w => displacement w = 1)).image finalDown := by
  ext w
  rw [mem_dycks, Finset.mem_image]
  induction w using List.reverseRecOn with
  | nil => simp [finalDown]
  | append_singleton w b _ =>
    simp only [List.length_append, List.length_singleton, ballot_snoc_iff, displacement_snoc]
    constructor
    · rintro ⟨⟨hl,hb,hz⟩,hd⟩
      cases b with
      | false => have := ballot_endpoint_nonneg hb; simp [step] at hd; omega
      | true => exact ⟨w, Finset.mem_filter.mpr ⟨mem_ballots.mpr ⟨by omega,hb⟩,
          by simp [step] at hd; omega⟩, rfl⟩
    · rintro ⟨v,hv,he⟩
      obtain ⟨hv,hd⟩ := Finset.mem_filter.mp hv
      obtain ⟨hl,hb⟩ := mem_ballots.mp hv
      have he' : v++[true] = w++[b] := he
      have h₁ : v = w := by simpa using congrArg List.dropLast he'
      subst v
      have h₂ := (List.cons.inj ((List.append_right_inj w).mp he')).1
      subst b
      exact ⟨⟨by omega,hb,by simp [hd,step]⟩,by simp [hd,step]⟩

private theorem finalDown_corank {w : List Bool} (hw : BallotFrom 0 w) (hd : displacement w = 1)
    {n : ℕ} (hl : w.length = 2*n+1) : walkCorank (finalDown w) = walkCorank w := by
  have h := walkArea_eq_corank ((ballot_snoc_iff w true).mpr ⟨hw,by simp [hd,step]⟩)
  rw [walkArea_append, walkArea_eq_corank hw, hd, hl, List.length_append, List.length_singleton] at h
  have hs : walkArea [true] = -1 := rfl
  change walkCorank (w++[true]) = _
  simp only [hs, Nat.cast_one, mul_one] at h
  omega

private theorem dycks_as_ballots {R : Type*} [Semiring R] (q : R) (n : ℕ) :
    corankSum q (dycks (n+1)) = ∑ w ∈ ballots (2*n+1),
      if displacement w = 1 then q^(walkCorank w) else 0 := by
  have hi : Function.Injective finalDown := fun _ _ h => (List.append_left_inj [true]).mp h
  rw [dycks_finalDown, corankSum, Finset.sum_image hi.injOn, ← Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w hw
  obtain ⟨hw,hd⟩ := Finset.mem_filter.mp hw
  have ⟨hl,hb⟩ := mem_ballots.mp hw
  rw [finalDown_corank hb hd hl]

theorem dyck_convolution {R : Type*} [Semiring R] (q : R) (n : ℕ) :
    corankSum q (dycks (n+1)) = ∑ i ∈ Finset.range (n+1),
      corankSum q (dycks i) * (q^(n-i) * corankSum q (dycks (n-i))) := by
  rw [dycks_as_ballots, ballot_last_zero_sum, show (2*n+1)/2 = n by omega]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have huinj : Function.Injective (false :: · : List Bool → List Bool) := fun _ _ h => (List.cons.inj h).2
  rw [show 2*n+1-2*i = 2*(n-i)+1 by omega, strictBallots_succ, corankSum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u hu
  obtain ⟨⟨_,hb⟩,hz⟩ := mem_dycks.mp hu
  rw [Finset.sum_image huinj.injOn, corankSum, dycks, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  obtain ⟨hl,hw⟩ := mem_ballots.mp hw
  have he : displacement (false::w) = 1 + displacement w := rfl
  rw [displacement_append, hz, zero_add, he]
  by_cases hd : displacement w = 0
  · simp [hd, walkCorank_append hz hb (ballot_up hw), walkCorank_up hw, hl,
      show (2*(n-i)+1)/2 = n-i by omega, Nat.add_comm (walkCorank w) (n-i), pow_add]
  · simp [hd, show 1 + displacement w ≠ 1 by omega]

end CentralUnimodality
