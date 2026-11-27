module

public import CentralUnimodality.Packing

/-! Chronological ballot words. False denotes an up-step and true a down-step.
The labels of the steps decrease from the word length to one. -/
@[expose] public section

namespace CentralUnimodality

def BallotFrom : ℕ → List Bool → Prop
  | _, [] => True
  | h, false :: w => BallotFrom (h+1) w
  | h, true :: w => 0 < h ∧ BallotFrom (h-1) w

def wordParts : List Bool → List ℕ
  | [] => []
  | false :: w => wordParts w
  | true :: w => wordParts w ++ [w.length+1]

theorem mem_wordParts_bounds {a : ℕ} {w : List Bool} (ha : a ∈ wordParts w) :
    0 < a ∧ a ≤ w.length := by
  induction w with
  | nil => simp [wordParts] at ha
  | cons b w ih =>
    cases b with
    | false => obtain ⟨hp, hb⟩ := ih ha; exact ⟨hp, by simp; omega⟩
    | true =>
      simp only [wordParts, List.mem_append, List.mem_singleton] at ha
      rcases ha with ho | rfl
      · obtain ⟨hp, hb⟩ := ih ho; exact ⟨hp, by simp; omega⟩
      · simp

theorem wordParts_sorted (w : List Bool) : (wordParts w).Pairwise (· < ·) := by
  induction w with
  | nil => constructor
  | cons b w ih =>
    cases b with
    | false => exact ih
    | true =>
      apply List.pairwise_append.mpr
      exact ⟨ih, by simp, fun a ha b hb =>
        (List.mem_singleton.mp hb) ▸ Nat.lt_succ_of_le (mem_wordParts_bounds ha).2⟩

theorem wordParts_positive (w : List Bool) : PositiveParts (wordParts w) :=
  fun _ ha => (mem_wordParts_bounds ha).1

private theorem rowBounds_snoc (m a : ℕ) (l : List ℕ) :
    RowBounds m (l ++ [a]) ↔ a < m ∧ RowBounds (m-2) l := by
  induction l with
  | nil => simp [RowBounds]
  | cons x l ih =>
    simp only [List.cons_append, RowBounds, List.length_append, List.length_singleton, ih]
    rw [show x+2*(l.length+1) < m ↔ x+2*l.length < m-2 by omega]
    tauto

theorem ballot_iff_fits (h : ℕ) (w : List Bool) :
    BallotFrom h w ↔ Fits (w.length+h) (wordParts w) := by
  have core (w : List Bool) (h : ℕ) : BallotFrom h w ↔ RowBounds (w.length+h) (wordParts w) := by
    induction w generalizing h with
    | nil => simp [BallotFrom, wordParts, RowBounds]
    | cons b w ih =>
      cases b with
      | false =>
        simp only [BallotFrom, wordParts, List.length_cons, ih]
        rw [show w.length+1+h = w.length+(h+1) by omega]
      | true =>
        simp only [BallotFrom, wordParts, List.length_cons, rowBounds_snoc, ih]
        by_cases hh : h = 0
        · simp [hh]
        · rw [show w.length+1+h-2 = w.length+(h-1) by omega]
          simp [show 0 < h by omega]
  exact ⟨fun hb => ⟨wordParts_sorted w, wordParts_positive w, (core _ _).mp hb⟩,
    fun hf => (core _ _).mpr hf.2.2⟩

def wordOfParts : ℕ → List ℕ → List Bool
  | 0, _ => []
  | m+1, l => decide (m+1 ∈ l) :: wordOfParts m l

theorem wordOfParts_length (m : ℕ) (l : List ℕ) : (wordOfParts m l).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [wordOfParts, ih]

private theorem wordOfParts_congr {a b : List ℕ} (m : ℕ)
    (h : ∀ i ≤ m, i ∈ a ↔ i ∈ b) : wordOfParts m a = wordOfParts m b := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [wordOfParts, h (m+1) (Nat.le_refl _), List.cons.injEq, true_and]
    exact ih fun i hi => h i (by omega)

theorem wordOfParts_wordParts (w : List Bool) : wordOfParts w.length (wordParts w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have htop : w.length+1 ∉ wordParts w := by intro h; have := (mem_wordParts_bounds h).2; omega
    cases b with
    | false => simpa [wordOfParts, wordParts, htop] using ih
    | true =>
      have e : wordOfParts w.length (wordParts w ++ [w.length+1]) = wordOfParts w.length (wordParts w) := by
        apply wordOfParts_congr
        intro i hi
        simp [show i ≠ w.length+1 by omega]
      simp [wordParts, wordOfParts, e, ih]

private theorem mem_decode (m : ℕ) (l : List ℕ) (a : ℕ) :
    a ∈ wordParts (wordOfParts m l) ↔ (0 < a ∧ a ≤ m ∧ a ∈ l) := by
  induction m with
  | zero => simp [wordOfParts, wordParts]; omega
  | succ m ih =>
    by_cases h : m+1 ∈ l
    · simp [wordOfParts, h, wordParts, wordOfParts_length, ih]
      grind
    · simp [wordOfParts, h, wordParts, ih]
      grind

private theorem sorted_eq_of_membership {a b : List ℕ}
    (ha : a.Pairwise (· < ·)) (hb : b.Pairwise (· < ·)) (he : ∀ x, x ∈ a ↔ x ∈ b) : a = b := by
  have eqset : a.toFinset = b.toFinset := Finset.ext fun x => by simpa using he x
  rw [← (List.toFinset_sort (· ≤ ·) (ha.imp Nat.ne_of_lt)).mpr (ha.imp Nat.le_of_lt),
      ← (List.toFinset_sort (· ≤ ·) (hb.imp Nat.ne_of_lt)).mpr (hb.imp Nat.le_of_lt), eqset]

theorem wordParts_wordOfParts {m : ℕ} {l : List ℕ} (hf : Fits m l) :
    wordParts (wordOfParts m l) = l := by
  apply sorted_eq_of_membership (wordParts_sorted _) hf.1
  intro a
  rw [mem_decode]
  exact ⟨fun h => h.2.2, fun ha => ⟨hf.2.1 _ ha, Nat.le_of_lt (lt_of_mem_of_fits hf ha), ha⟩⟩

/-- Weight-preserving identification with chronological walks staying nonnegative. -/
def ballotEquiv (m : ℕ) :
    {w : List Bool // w.length = m ∧ BallotFrom 0 w} ≃ {l : List ℕ // Fits m l} where
  toFun w := ⟨wordParts w.val, by simpa [w.property.1] using (ballot_iff_fits 0 _).mp w.property.2⟩
  invFun l := ⟨wordOfParts m l.val, wordOfParts_length m l.val, (ballot_iff_fits _ _).mpr
    (by simpa [wordOfParts_length, wordParts_wordOfParts l.property] using l.property)⟩
  left_inv w := Subtype.ext (w.property.1 ▸ wordOfParts_wordParts w.val)
  right_inv l := Subtype.ext (wordParts_wordOfParts l.property)

end CentralUnimodality
