module

public import CentralUnimodality.PackedRows

/-! A Boolean test for weak unimodality with a proof about the literal ranks.
The input integer has one coefficient per base-2^bits digit, in rank order. -/
@[expose] public section

namespace CentralUnimodality

def fallingDigits (bits : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | d+1, v =>
    let w := v >>> bits
    decide (w % 2^bits ≤ v % 2^bits) && fallingDigits bits d w

def unimodalDigits (bits : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | d+1, v =>
    let w := v >>> bits
    if v % 2^bits ≤ w % 2^bits then unimodalDigits bits d w
    else fallingDigits bits d w

theorem digit_succ (b v j : ℕ) :
    digit b v (j+1) = digit b (v >>> b) j := by
  simp [digit, Nat.mul_add, Nat.shiftRight_add, Nat.add_comm]

theorem digit_zero (b v : ℕ) : digit b v 0 = v % 2^b := by simp [digit]

theorem fallingDigits_sound (b d v : ℕ) (h : fallingDigits b d v = true) :
    ∀ j < d, digit b v (j+1) ≤ digit b v j := by
  induction d generalizing v with
  | zero => omega
  | succ d ih =>
    simp only [fallingDigits, Bool.and_eq_true, decide_eq_true_eq] at h
    intro j hj
    cases j with
    | zero => simpa only [digit_succ, digit_zero] using h.1
    | succ j => rw [digit_succ b v (j+1), digit_succ b v j]; exact ih _ h.2 _ (by omega)

theorem unimodalDigits_sound (b d v : ℕ) (h : unimodalDigits b d v = true) :
    UnimodalOn (digit b v) 0 d := by
  induction d generalizing v with
  | zero => exact ⟨0, by omega, by omega, by omega, by omega⟩
  | succ d ih =>
    simp only [unimodalDigits] at h
    split at h
    next hfirst =>
      obtain ⟨p, _, hp, up, down⟩ := ih _ h
      refine ⟨p+1, by omega, by omega, ?_, ?_⟩
      · intro j _ hj
        cases j with
        | zero => simpa only [digit_succ, digit_zero] using hfirst
        | succ j =>
          rw [digit_succ b v j, digit_succ b v (j+1)]
          exact up j (by omega) (by omega)
      · intro j hj hd
        cases j with
        | zero => omega
        | succ j =>
          rw [digit_succ b v (j+1), digit_succ b v j]
          exact down j (by omega) (by omega)
    next hfirst =>
      refine ⟨0, by omega, by omega, by omega, ?_⟩
      intro j _ hd
      cases j with
      | zero => simpa only [digit_succ, digit_zero] using Nat.le_of_not_ge hfirst
      | succ j =>
        rw [digit_succ b v (j+1), digit_succ b v j]
        exact fallingDigits_sound _ _ _ h j (by omega)

def checkRow (b m d : ℕ) : Bool := unimodalDigits b d (packedRow b m)

theorem checkRow_sound {b m d : ℕ} (hm : m < b) (hc : checkRow b m d = true) :
    UnimodalOn (rankCount m) 0 d := by
  have he : digit b (packedRow b m) = rankCount m := funext fun j => packedRow_digit b m j hm
  exact he ▸ unimodalDigits_sound _ _ _ hc

end CentralUnimodality
