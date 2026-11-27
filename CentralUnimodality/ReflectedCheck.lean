module

public import CentralUnimodality.BaseCases
public import CentralUnimodality.MomentTest
public import Mathlib.Data.Nat.Sqrt

/-! Integer certificate for the small-size reflected comparisons. The squared
threshold is the exact rational 131/250 times (2N)^(3/2), with no rounding. -/
@[expose] public section

namespace CentralUnimodality

def reflectedLimit (m : ℕ) : ℕ :=
  (131^2*(2*((m+1)/2))^3).sqrt/250 - (m+1+(m+1)/2)

theorem le_reflectedLimit {m i j : ℕ}
    (h : (250*(i+j+(m+1+(m+1)/2)))^2 ≤ 131^2*(2*((m+1)/2))^3) :
    i+j ≤ reflectedLimit m := by
  have h₁ := Nat.le_sqrt'.mpr h
  unfold reflectedLimit
  omega

def reflectedCheck (m : ℕ) : Bool :=
  let d := m*m/4
  let l := reflectedLimit m
  let v := packedRow 192 m
  (if m < 128 then true else unimodalDigits 192 d v) &&
    (decide (l ≤ d) && (List.range (l/2+1)).all (fun i =>
      decide (digit 192 v (d-i) ≤ digit 192 v (d-(l-i)))))

theorem reflectedCheck_sound {m : ℕ} (hm : m < 192) (hc : reflectedCheck m = true) :
    UnimodalOn (rankCount m) 0 (m*m/4) ∧
    ∀ i j : ℕ, i < j → i+j ≤ reflectedLimit m →
      rankCount m (m*m/4-i) ≤ rankCount m (m*m/4-j) := by
  simp only [reflectedCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨hrow,hlim,hpairs⟩ := hc
  have hu : UnimodalOn (rankCount m) 0 (m*m/4) := by
    by_cases hsmall : m < 128
    · exact base_word hsmall
    · exact checkRow_sound hm (by simpa only [checkRow, ite_eq_right hsmall] using hrow)
  refine ⟨hu, ?_⟩
  intro i j hij hcut
  have he := hpairs i (List.mem_range.mpr (by omega))
  simp only [packedRow_digit _ _ _ hm] at he
  have hbt := hu.reverse.between (Nat.le_of_lt hij) (by omega : j ≤ reflectedLimit m-i)
    (by omega : reflectedLimit m-i ≤ m*m/4)
  simpa only [min_eq_left he] using hbt

end CentralUnimodality
