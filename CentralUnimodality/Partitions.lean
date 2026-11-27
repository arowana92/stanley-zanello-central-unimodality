module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image

/-! Strict partitions inside the central staircases, listed smallest part first.
For ballot length `m`, the i-th largest part (i starting at 1) is at most
`m - 2*i + 1`. A part with `r` larger parts therefore satisfies `a + 2*r < m`.
-/

@[expose] public section

namespace CentralUnimodality

def RowBounds (m : ℕ) : List ℕ → Prop
  | [] => True
  | a :: tail => a + 2 * tail.length < m ∧ RowBounds m tail

def PositiveParts (l : List ℕ) : Prop := ∀ a ∈ l, 0 < a

def Fits (m : ℕ) (l : List ℕ) : Prop :=
  l.Pairwise (· < ·) ∧ PositiveParts l ∧ RowBounds m l

theorem fits_nil (m : ℕ) : Fits m [] := by
  simp [Fits, PositiveParts, RowBounds]

theorem fits_cons {m a : ℕ} {l : List ℕ} :
    Fits m (a :: l) ↔ (∀ b ∈ l, a < b) ∧ 0 < a ∧ a + 2*l.length < m ∧ Fits m l := by
  simp only [Fits, List.pairwise_cons, PositiveParts, List.forall_mem_cons, RowBounds]
  tauto

theorem fits_length_le {m : ℕ} {l : List ℕ} (h : Fits m l) : 2*l.length ≤ m := by
  cases l with
  | nil => simp
  | cons a l =>
    obtain ⟨_, ha, hr, _⟩ := fits_cons.mp h
    simp only [List.length_cons]
    omega

def raiseParts (l : List ℕ) : List ℕ := l.map Nat.succ

def insertOne (l : List ℕ) : List ℕ := 1 :: raiseParts l

theorem raiseParts_injective : Function.Injective raiseParts := by
  intro l t h
  have := congrArg (List.map Nat.pred) h
  simpa [raiseParts, List.map_map, Function.comp_def] using this

theorem insertOne_injective : Function.Injective insertOne := by
  intro l t h
  exact raiseParts_injective (List.cons.inj h).2

theorem raiseParts_length (l : List ℕ) : (raiseParts l).length = l.length := by
  simp [raiseParts]

theorem raiseParts_sum (l : List ℕ) : (raiseParts l).sum = l.sum + l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change a+1 + (raiseParts l).sum = (a+l.sum) + (l.length+1)
    omega

private theorem fits_raiseParts {m : ℕ} {l : List ℕ} (hp : PositiveParts l) :
    Fits (m+1) (raiseParts l) ↔ Fits m l := by
  induction l with
  | nil => simp [Fits, raiseParts, RowBounds, PositiveParts]
  | cons a l ih =>
    have ht : PositiveParts l := fun b hb => hp b (List.mem_cons_of_mem _ hb)
    have ha : 0 < a := hp a (by simp)
    change Fits (m+1) (a.succ :: raiseParts l) ↔ Fits m (a :: l)
    simp only [fits_cons, ih ht, raiseParts_length]
    have hlt : (∀ b ∈ raiseParts l, a.succ < b) ↔ (∀ b ∈ l, a < b) := by
      simp [raiseParts]
    rw [hlt]
    have hbound : a.succ + 2*l.length < m+1 ↔ a + 2*l.length < m := by omega
    simp [hbound, ha]

private theorem fits_insertOne {m : ℕ} {l : List ℕ} (hp : PositiveParts l) :
    Fits (m+1) (insertOne l) ↔ 2*(l.length+1) ≤ m+1 ∧ Fits m l := by
  have hgt : ∀ b ∈ raiseParts l, 1 < b := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact Nat.succ_lt_succ (hp a ha)
  rw [insertOne, fits_cons, raiseParts_length, fits_raiseParts hp]
  have hbound : 1 + 2*l.length < m+1 ↔ 2*(l.length+1) ≤ m+1 := by omega
  exact ⟨fun h => ⟨hbound.mp h.2.2.1, h.2.2.2⟩,
    fun h => ⟨hgt, by decide, hbound.mpr h.1, h.2⟩⟩

private theorem unraise {l : List ℕ} (hp : ∀ a ∈ l, 1 < a) :
    ∃ t, PositiveParts t ∧ raiseParts t = l := by
  refine ⟨l.map Nat.pred, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have := hp b hb
    change 0 < b-1
    omega
  · simp only [raiseParts, List.map_map]
    calc
      _ = l.map id := List.map_congr_left fun a ha =>
        Nat.succ_pred_eq_of_pos (Nat.lt_trans Nat.zero_lt_one (hp a ha))
      _ = l := List.map_id l

/-- Distinct lists of exactly `d` positive parts. Each step raises the old parts
and optionally inserts a new smallest part of size one. -/
def partitions : ℕ → ℕ → Finset (List ℕ)
  | 0, 0 => {[]}
  | 0, _+1 => ∅
  | _+1, 0 => {[]}
  | m+1, d+1 =>
    (partitions m (d+1)).image raiseParts ∪
      (if 2*(d+1) ≤ m+1 then (partitions m d).image insertOne else ∅)

theorem mem_partitions {m d : ℕ} {l : List ℕ} :
    l ∈ partitions m d ↔ Fits m l ∧ l.length = d := by
  induction m generalizing d l with
  | zero =>
    cases d with
    | zero =>
      cases l <;> simp [partitions, fits_nil]
    | succ d =>
      simp only [partitions, Finset.notMem_empty, false_iff, not_and]
      intro hf
      have := fits_length_le hf
      omega
  | succ m ih =>
    cases d with
    | zero =>
      cases l <;> simp [partitions, fits_nil]
    | succ d =>
      rw [partitions, Finset.mem_union]
      constructor
      · rintro (hr | ho)
        · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
          obtain ⟨hf, hl⟩ := ih.mp ht
          exact ⟨(fits_raiseParts hf.2.1).mpr hf, (raiseParts_length t).trans hl⟩
        · split at ho
          next h =>
            obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ho
            obtain ⟨hf, hl⟩ := ih.mp ht
            exact ⟨(fits_insertOne hf.2.1).mpr ⟨hl ▸ h, hf⟩, by simp [insertOne, raiseParts_length, hl]⟩
          next => simp at ho
      · rintro ⟨hf, hl⟩
        cases l with
        | nil => simp at hl
        | cons a l =>
          obtain ⟨hgt, ha, _, htail⟩ := fits_cons.mp hf
          by_cases hex : a = 1
          · subst a
            obtain ⟨t, ht, rfl⟩ := unraise hgt
            have hd : t.length = d := by simpa [raiseParts_length] using hl
            have hex := (fits_insertOne ht).mp hf
            right
            rw [ite_eq_left (hd ▸ hex.1)]
            exact Finset.mem_image.mpr ⟨t, ih.mpr ⟨hex.2, hd⟩, rfl⟩
          · have hlo : ∀ b ∈ a :: l, 1 < b := by
              intro b hb
              rcases List.mem_cons.mp hb with rfl | hb
              · omega
              · have := hgt b hb; omega
            obtain ⟨t, ht, he⟩ := unraise hlo
            left
            exact Finset.mem_image.mpr ⟨t, ih.mpr
              ⟨(fits_raiseParts ht).mp (he ▸ hf), by rw [← raiseParts_length t, he, hl]⟩, he⟩

end CentralUnimodality
