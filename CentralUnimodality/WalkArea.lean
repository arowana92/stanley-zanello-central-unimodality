module

public import CentralUnimodality.Ballot
import Mathlib.Tactic.Ring

/-! The signed walk area equals twice corank plus an explicit shift on the
positive strict branch. All areas in this module are integer sums of heights. -/
@[expose] public section

namespace CentralUnimodality

def step : Bool → ℤ
  | false => 1
  | true => -1

def displacement (w : List Bool) : ℤ := (w.map step).sum

def heights (h : ℤ) : List Bool → List ℤ
  | [] => []
  | b :: w => (h+step b) :: heights (h+step b) w

def walkArea (w : List Bool) : ℤ := (heights 0 w).sum

theorem displacement_append (u v : List Bool) :
    displacement (u++v) = displacement u + displacement v := by
  simp [displacement]

theorem heights_length (h : ℤ) (w : List Bool) : (heights h w).length = w.length := by
  induction w generalizing h with
  | nil => rfl
  | cons b w ih => simp [heights, ih]

theorem heights_append (h : ℤ) (u v : List Bool) :
    heights h (u++v) = heights h u ++ heights (h+displacement u) v := by
  induction u generalizing h with
  | nil => simp [heights, displacement]
  | cons b u ih => simp [heights, ih, displacement, add_assoc]

theorem heights_translate (a h : ℤ) (w : List Bool) :
    heights (a+h) w = (heights h w).map (a+·) := by
  induction w generalizing h with
  | nil => rfl
  | cons b w ih => simp [heights, add_assoc, ih]

theorem sum_heights_translate (a h : ℤ) (w : List Bool) :
    (heights (a+h) w).sum = a*w.length + (heights h w).sum := by
  induction w generalizing h with
  | nil => simp [heights]
  | cons b w ih =>
    simp only [heights, List.sum_cons, add_assoc a h, ih, List.length_cons, Nat.cast_add,
      Nat.cast_one]
    ring

theorem sum_heights (h : ℤ) (w : List Bool) :
    (heights h w).sum = h*w.length + walkArea w := by
  simpa [walkArea] using sum_heights_translate h 0 w

theorem walkArea_cons (b : Bool) (w : List Bool) :
    walkArea (b :: w) = walkArea w + step b*(w.length+1) := by
  change (0+step b) + (heights (0+step b) w).sum = _
  rw [sum_heights, zero_add]
  ring

theorem walkArea_append (u v : List Bool) :
    walkArea (u++v) = walkArea u + walkArea v + displacement u*v.length := by
  change (heights 0 (u++v)).sum = _
  rw [heights_append, List.sum_append, zero_add, sum_heights (displacement u) v]
  change walkArea u + _ = _
  omega

theorem area_rank_identity (w : List Bool) :
    2*walkArea w + 4*((wordParts w).sum : ℤ) = (w.length : ℤ)*(w.length+1) := by
  induction w with
  | nil => simp [wordParts, walkArea, heights]
  | cons b w ih =>
    rw [walkArea_cons]
    cases b <;> simp only [step, wordParts, List.sum_append, List.sum_singleton, List.length_cons,
      Nat.cast_add, Nat.cast_one]
    all_goals
      calc
        _ = (2*walkArea w + 4*↑(wordParts w).sum) + 2*((w.length : ℤ)+1) := by ring
        _ = _ := by rw [ih]; ring

/-- On a strict walk starting up, this is twice the signed half-area of the
research proof. The equality is valid before restricting the suffix to ballot words. -/
theorem strict_up_area (n δ : ℕ) (hδ : δ ≤ 1) {w : List Bool} (hw : w.length = 2*n+δ) :
    walkArea (false :: w) =
      2*((n : ℤ)*(n+δ) - (wordParts w).sum) + (w.length+1) + (n+δ) := by
  have ha := area_rank_identity w
  rw [hw] at ha
  rw [walkArea_cons, hw]
  rcases (show δ = 0 ∨ δ = 1 by omega) with rfl | rfl <;>
    simp only [step, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
      add_zero, one_mul] at * <;>
    ring_nf at ha ⊢ <;> omega

theorem ballot_iff_heights (h : ℕ) (w : List Bool) :
    BallotFrom h w ↔ ∀ y ∈ heights h w, 0 ≤ y := by
  induction w generalizing h with
  | nil => simp [BallotFrom, heights]
  | cons b w ih =>
    cases b with
    | false => simp [BallotFrom, heights, step, ih, show (0 : ℤ) ≤ h+1 by omega]
    | true =>
      cases h with
      | zero => simp [BallotFrom, heights, step]
      | succ h => simp [BallotFrom, heights, step, ih]

def NoReturn (w : List Bool) : Prop := 0 ∉ heights 0 w

instance (w : List Bool) : Decidable (NoReturn w) := inferInstanceAs (Decidable (0 ∉ heights 0 w))

private theorem positive_of_avoids_zero (w : List Bool) (h : ℤ) (hp : 0 < h)
    (hz : 0 ∉ heights h w) : ∀ y ∈ heights h w, 0 < y := by
  induction w generalizing h with
  | nil => simp [heights]
  | cons b w ih =>
    simp only [heights, List.mem_cons, not_or] at hz
    have hs : 0 < h+step b := by cases b <;> simp only [step] at * <;> omega
    exact List.forall_mem_cons.mpr ⟨hs, ih _ hs hz.2⟩

theorem noReturn_up_iff (w : List Bool) : NoReturn (false::w) ↔ BallotFrom 0 w := by
  have ht : heights 1 w = (heights 0 w).map (1+·) := by simpa using heights_translate 1 0 w
  rw [ballot_iff_heights]
  constructor
  · intro hz
    have ha : 0 ∉ heights 1 w := by simpa [NoReturn, heights, step] using hz
    intro y hy
    have hp := positive_of_avoids_zero w 1 (by decide) ha (1+y) (ht ▸ List.mem_map_of_mem hy)
    omega
  · intro hp
    simp only [NoReturn, heights, step, zero_add, List.mem_cons, zero_ne_one, false_or, ht]
    intro hz
    obtain ⟨y, hy, he⟩ := List.mem_map.mp hz
    have := hp _ hy
    omega

end CentralUnimodality
