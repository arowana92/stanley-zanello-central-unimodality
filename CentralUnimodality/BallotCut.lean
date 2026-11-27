module

public import CentralUnimodality.Corank
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Exact last-zero decompositions of the ballot corank polynomials. -/
@[expose] public section

namespace CentralUnimodality

private abbrev Cut := Σ _ : ℕ, List Bool × List Bool

private def cutPairs (m : ℕ) : Finset Cut :=
  (Finset.range (m/2+1)).sigma fun i => dycks i ×ˢ strictBallots (m-2*i)

private def splitBallot (w : List Bool) : Cut := ⟨(lastSplit w).1.length/2,lastSplit w⟩

private def joinBallot (p : Cut) := p.2.1 ++ p.2.2

private theorem mem_cutPairs {p : Cut} {m : ℕ} :
    p ∈ cutPairs m ↔ p.1 ≤ m/2 ∧ p.2.1 ∈ dycks p.1 ∧ p.2.2 ∈ strictBallots (m-2*p.1) := by
  simp [cutPairs, Nat.lt_succ_iff]

private theorem splitBallot_mem {w : List Bool} {m : ℕ} (hw : w ∈ ballots m) :
    splitBallot w ∈ cutPairs m := by
  obtain ⟨hl, hb⟩ := mem_ballots.mp hw
  obtain ⟨he, hz, hs⟩ := lastSplit_valid w
  have hsum := congrArg List.length he
  rw [List.length_append, hl] at hsum
  have hpair := (ballot_append_iff hz).mp (he ▸ hb)
  have heven := bridge_length hz
  apply mem_cutPairs.mpr
  dsimp only [splitBallot]
  exact ⟨by omega, mem_dycks.mpr ⟨⟨heven, hpair.1⟩,hz⟩,
    mem_strictBallots.mpr ⟨⟨by omega, hpair.2⟩,hs⟩⟩

private theorem joinBallot_mem {p : Cut} {m : ℕ} (hp : p ∈ cutPairs m) :
    joinBallot p ∈ ballots m := by
  obtain ⟨hi,hu,hv⟩ := mem_cutPairs.mp hp
  obtain ⟨⟨hl,hb⟩, hz⟩ := mem_dycks.mp hu
  obtain ⟨⟨hl',hb'⟩,_⟩ := mem_strictBallots.mp hv
  exact mem_ballots.mpr ⟨by simp only [joinBallot, List.length_append, hl, hl']; omega,
    (ballot_append_iff hz).mpr ⟨hb,hb'⟩⟩

theorem ballot_last_zero_sum {A : Type*} [AddCommMonoid A] (F : List Bool → A) (m : ℕ) :
    (∑ w ∈ ballots m, F w) = ∑ i ∈ Finset.range (m/2+1),
      ∑ u ∈ dycks i, ∑ v ∈ strictBallots (m-2*i), F (u++v) := by
  calc
    _ = ∑ p ∈ cutPairs m, F (joinBallot p) := by
      apply Finset.sum_bij' (fun w _ => splitBallot w) (fun p _ => joinBallot p)
      · exact fun _ => splitBallot_mem
      · exact fun _ => joinBallot_mem
      · exact fun w _ => (lastSplit_valid w).1
      · rintro ⟨i,u,v⟩ hp
        obtain ⟨_,hu,hv⟩ := mem_cutPairs.mp hp
        obtain ⟨⟨hl,_⟩,hz⟩ := mem_dycks.mp hu
        obtain ⟨_,hs⟩ := mem_strictBallots.mp hv
        change u.length = 2*i at hl
        simp [joinBallot, splitBallot, lastSplit_append hz hs, hl]
      · exact fun w _ => congrArg F (lastSplit_valid w).1.symm
    _ = _ := by simp only [cutPairs, Finset.sum_sigma, Finset.sum_product, joinBallot]

theorem ballot_last_zero {R : Type*} [Semiring R] (q : R) (m : ℕ) :
    corankSum q (ballots m) = ∑ i ∈ Finset.range (m/2+1),
      corankSum q (dycks i) * corankSum q (strictBallots (m-2*i)) := by
  rw [corankSum, ballot_last_zero_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [corankSum, corankSum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  obtain ⟨⟨_,hb⟩,hz⟩ := mem_dycks.mp hu
  rw [walkCorank_append hz hb (mem_strictBallots.mp hv).1.2, pow_add]

theorem strictBallots_succ (m : ℕ) :
    strictBallots (m+1) = (ballots m).image (false :: ·) := by
  ext w
  rw [mem_strictBallots, Finset.mem_image]
  cases w with
  | nil => simp
  | cons b w =>
    cases b with
    | false =>
      simp only [List.length_cons, Nat.add_right_cancel_iff, List.cons.injEq, true_and,
        exists_eq_right, mem_ballots, noReturn_up_iff]
      exact ⟨fun ⟨⟨hl,_⟩,hb⟩ => ⟨hl,hb⟩, fun ⟨hl,hb⟩ => ⟨⟨hl,ballot_up hb⟩,hb⟩⟩
    | true => simp [BallotFrom]

theorem strictBallots_weight_succ {R : Type*} [Semiring R] (q : R) (m : ℕ) :
    corankSum q (strictBallots (m+1)) = q^((m+1)/2) * corankSum q (ballots m) := by
  have hi : Function.Injective (false :: · : List Bool → List Bool) := fun _ _ h => (List.cons.inj h).2
  rw [strictBallots_succ, corankSum, Finset.sum_image hi.injOn, corankSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have ⟨hl,hb⟩ := mem_ballots.mp hw
  rw [walkCorank_up hb, hl, Nat.add_comm, pow_add]

theorem strictBallots_weight_zero {R : Type*} [Semiring R] (q : R) :
    corankSum q (strictBallots 0) = 1 := by
  have he : strictBallots 0 = {[]} := by decide
  simp [he, corankSum, walkCorank, staircaseDegree, wordParts]

theorem odd_ballot_convolution {R : Type*} [Semiring R] (q : R) (n : ℕ) :
    corankSum q (ballots (2*n+1)) = ∑ i ∈ Finset.range (n+1),
      corankSum q (dycks i) * (q^(n-i) * corankSum q (ballots (2*(n-i)))) := by
  rw [ballot_last_zero, show (2*n+1)/2 = n by omega]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [show 2*n+1-2*i = 2*(n-i)+1 by omega, strictBallots_weight_succ,
    show (2*(n-i)+1)/2 = n-i by omega]

theorem even_ballot_convolution {R : Type*} [Semiring R] (q : R) (n : ℕ) :
    corankSum q (ballots (2*(n+1))) = corankSum q (dycks (n+1)) +
      ∑ i ∈ Finset.range (n+1), corankSum q (dycks i) *
        (q^(n-i+1) * corankSum q (ballots (2*(n-i)+1))) := by
  rw [ballot_last_zero, show 2*(n+1)/2 = n+1 by omega, Finset.sum_range_succ, Nat.sub_self,
    strictBallots_weight_zero, mul_one, add_comm]
  apply congrArg (corankSum q (dycks (n+1)) + ·)
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [show 2*(n+1)-2*i = (2*(n-i)+1)+1 by omega, strictBallots_weight_succ,
    show (2*(n-i)+1+1)/2 = n-i+1 by omega]

end CentralUnimodality
