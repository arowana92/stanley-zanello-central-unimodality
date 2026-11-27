module

public import CentralUnimodality.SignedRanks

/-! Cut nonnegative walks at returns to zero and track the ordinary (unsigned)
corank. The weight of a nonnegative word is the staircase degree minus the
sum of the corresponding distinct parts. -/
@[expose] public section

namespace CentralUnimodality

def staircaseDegree (m : ℕ) : ℕ := (m/2)*((m+1)/2)

theorem staircaseDegree_parity (n δ : ℕ) (hδ : δ ≤ 1) :
    staircaseDegree (2*n+δ) = n*(n+δ) := by
  unfold staircaseDegree
  congr 1 <;> omega

def walkCorank (w : List Bool) : ℕ := staircaseDegree w.length - (wordParts w).sum

theorem displacement_length (w : List Bool) :
    displacement w + 2*((wordParts w).length : ℤ) = (w.length:ℤ) := by
  induction w with
  | nil => simp [displacement, wordParts]
  | cons b w ih =>
    change step b + displacement w + _ = _
    cases b <;> simp only [step, wordParts, List.length_append, List.length_nil,
      List.length_cons, Nat.cast_add, Nat.cast_one, Nat.cast_zero] <;> omega

theorem bridge_length {w : List Bool} (hw : displacement w = 0) :
    w.length = 2*(w.length/2) := by
  have := displacement_length w
  omega

instance (h : ℕ) (w : List Bool) : Decidable (BallotFrom h w) :=
  decidable_of_iff _ (ballot_iff_heights h w).symm

theorem ballot_append_iff {u v : List Bool} (hu : displacement u = 0) :
    BallotFrom 0 (u++v) ↔ BallotFrom 0 u ∧ BallotFrom 0 v := by
  simp only [ballot_iff_heights, heights_append, hu, add_zero, List.forall_mem_append]

theorem wordParts_sum_le_degree {w : List Bool} (hw : BallotFrom 0 w) :
    (wordParts w).sum ≤ staircaseDegree w.length := by
  let n := w.length/2
  let δ := w.length%2
  have hlo : δ ≤ 1 := by dsimp [δ]; omega
  have hlen : w.length = 2*n+δ := by dsimp [δ,n]; omega
  have hf := (ballot_iff_fits 0 w).mp hw
  simp only [Nat.add_zero, hlen] at hf
  have hb := sum_le_staircase_area hlo ((fits_iff_inside_reverse n δ hlo _).mp hf)
  simpa [hlen, staircaseDegree_parity n δ hlo] using hb

theorem walkArea_eq_corank {w : List Bool} (hw : BallotFrom 0 w) :
    walkArea w = 2*(walkCorank w:ℤ) + (((w.length+1)/2 : ℕ):ℤ) := by
  let n := w.length/2
  let δ := w.length%2
  have hlo : δ ≤ 1 := by dsimp [δ]; omega
  have hlen : w.length = 2*n+δ := by dsimp [δ,n]; omega
  have hhalf : (w.length+1)/2 = n+δ := by omega
  have ha := strict_up_area n δ hlo hlen
  rw [walkArea_cons, walkCorank, Nat.cast_sub (wordParts_sum_le_degree hw), hlen,
    staircaseDegree_parity n δ hlo] at *
  simp only [step, one_mul, Nat.cast_mul, Nat.cast_add] at *
  omega

theorem walkCorank_append {u v : List Bool} (hu : displacement u = 0)
    (hb : BallotFrom 0 u) (hc : BallotFrom 0 v) :
    walkCorank (u++v) = walkCorank u + walkCorank v := by
  have ha := walkArea_eq_corank ((ballot_append_iff hu).mpr ⟨hb,hc⟩)
  rw [walkArea_append, hu, zero_mul, add_zero, walkArea_eq_corank hb, walkArea_eq_corank hc,
    List.length_append] at ha
  have := bridge_length hu
  omega

theorem ballot_up {w : List Bool} (hw : BallotFrom 0 w) : BallotFrom 0 (false::w) := by
  have h := (ballot_iff_heights 0 w).mp hw
  apply (ballot_iff_heights 0 _).mpr
  have he := heights_translate 1 0 w
  simp only [add_zero] at he
  simp [heights, step, he]
  intro y hy
  have := h y hy
  omega

theorem walkCorank_up {w : List Bool} (hw : BallotFrom 0 w) :
    walkCorank (false::w) = walkCorank w + (w.length+1)/2 := by
  have h := walkArea_eq_corank (ballot_up hw)
  rw [walkArea_cons, walkArea_eq_corank hw, List.length_cons] at h
  simp only [step, one_mul] at h
  omega

def ballots (m : ℕ) := (words m).filter (BallotFrom 0)
def dycks (n : ℕ) := (ballots (2*n)).filter (fun w => displacement w = 0)
def strictBallots (m : ℕ) := (ballots m).filter NoReturn

theorem mem_ballots {w : List Bool} {m : ℕ} :
    w ∈ ballots m ↔ w.length = m ∧ BallotFrom 0 w := by simp [ballots, mem_words]

theorem mem_dycks {w : List Bool} {n : ℕ} :
    w ∈ dycks n ↔ (w.length = 2*n ∧ BallotFrom 0 w) ∧ displacement w = 0 := by
  simp [dycks, mem_ballots]

theorem mem_strictBallots {w : List Bool} {m : ℕ} :
    w ∈ strictBallots m ↔ (w.length = m ∧ BallotFrom 0 w) ∧ NoReturn w := by
  simp [strictBallots, mem_ballots]

/-- Area weights taken in an arbitrary semiring, in particular in the polynomial
ring with q the indeterminate. -/
def corankSum {R : Type*} [Semiring R] (q : R) (T : Finset (List Bool)) : R :=
  ∑ w ∈ T, q^(walkCorank w)

theorem ballot_rank_polynomial {R : Type*} [Semiring R] (q : R) (n δ : ℕ) (hδ : δ ≤ 1) :
    corankSum q (ballots (2*n+δ)) = ∑ j ∈ Finset.range (n*(n+δ)+1),
      rankCount (2*n+δ) j • q^(n*(n+δ)-j) := by
  rw [← sum_over_ranks (fun j => q^(n*(n+δ)-j)) n δ hδ]
  apply Finset.sum_bij' (fun w _ => wordParts w) (fun l _ => wordOfParts (2*n+δ) l)
  · intro w hw
    obtain ⟨hl,hb⟩ := mem_ballots.mp hw
    exact mem_allPartitions.mpr (by simpa [hl] using (ballot_iff_fits 0 w).mp hb)
  · intro l hl
    exact mem_ballots.mpr ((ballotEquiv _).symm ⟨l,mem_allPartitions.mp hl⟩).property
  · intro w hw
    rw [← (mem_ballots.mp hw).1, wordOfParts_wordParts]
  · intro l hl
    exact wordParts_wordOfParts (mem_allPartitions.mp hl)
  · intro w hw
    simp [walkCorank, (mem_ballots.mp hw).1, staircaseDegree_parity n δ hδ]

end CentralUnimodality
