module

public import CentralUnimodality.DyckAreaWord

/-! A direct degree bound for the joint (area,dinv) enumerator. Label
each occurrence of a height by the number of later occurrences at that
height. The labels are distinct lattice points, and their second-coordinate
sum counts the equal-height inversions. -/
@[expose] public section

namespace CentralUnimodality

/-- Pairs i < j with heights equal or with the first one larger by one. -/
def diagonalInversions : List ℕ → ℕ
  | [] => 0
  | a::v => v.count a + (if a = 0 then 0 else v.count (a-1)) + diagonalInversions v

private def occurrencePoints : List ℕ → Finset (ℕ × ℕ)
  | [] => ∅
  | a::v => insert (a,v.count a) (occurrencePoints v)

private theorem occurrence_lt_count {v : List ℕ} {p : ℕ × ℕ} (hp : p ∈ occurrencePoints v) :
    p.2 < v.count p.1 := by
  induction v with
  | nil => simp [occurrencePoints] at hp
  | cons a v ih =>
    rw [occurrencePoints,Finset.mem_insert] at hp
    rcases hp with rfl|hp
    · simp
    · have h := ih hp
      simp only [List.count_cons]
      split <;> omega

private theorem occurrence_fresh (a : ℕ) (v : List ℕ) : (a,v.count a) ∉ occurrencePoints v :=
  fun h => (Nat.lt_irrefl _) (occurrence_lt_count h)

private theorem occurrence_count (v : List ℕ) : (occurrencePoints v).card = v.length := by
  induction v with
  | nil => simp [occurrencePoints]
  | cons a v ih => simp [occurrencePoints,Finset.card_insert_of_notMem (occurrence_fresh a v),ih]

private theorem occurrence_sum (v : List ℕ) :
    (∑ p ∈ occurrencePoints v, (p.1+p.2)) ≤ v.sum+diagonalInversions v := by
  induction v with
  | nil => simp [occurrencePoints,diagonalInversions]
  | cons a v ih =>
    rw [occurrencePoints,Finset.sum_insert (occurrence_fresh a v)]
    simp only [List.sum_cons,diagonalInversions]
    omega

theorem area_dinv_degree (v : List ℕ) :
    dyckLower v.length ≤ ((v.sum+diagonalInversions v:ℕ):ℝ) := by
  have h := degree_sum_lower (occurrencePoints v)
  rw [occurrence_count] at h
  exact h.trans (by exact_mod_cast occurrence_sum v)

def dyckTotalDegree (w : List Bool) := walkCorank w+diagonalInversions (upHeights 0 w)

/-- Every nonempty ordinary q,t-Catalan total-degree slice has degree at
least the threshold needed by the staircase induction. -/
theorem dyck_diagonal_cutoff {w : List Bool} {n : ℕ} (hw : w ∈ dycks n) :
    ⌈dyckLower n⌉₊ ≤ dyckTotalDegree w := by
  obtain ⟨hl,ha⟩ := dyck_up_heights hw
  apply Nat.ceil_le.mpr
  simpa only [hl,ha,dyckTotalDegree] using area_dinv_degree (upHeights 0 w)

end CentralUnimodality
