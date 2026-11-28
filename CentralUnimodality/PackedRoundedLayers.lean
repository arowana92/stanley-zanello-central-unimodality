module

public import CentralUnimodality.PackedDigitArithmetic
public import CentralUnimodality.RoundedDeficit
import Mathlib.Tactic.Positivity

/-! Evaluate all rounded deficits below a chosen cutoff in parallel. Each
digit represents one endpoint count. A spare high bit isolates the rounding
of neighboring counts when an entire packed integer is divided by two. -/
@[expose] public section

namespace CentralUnimodality.EndpointDeficit

theorem rounded_le (u m d : ℕ) (i : ℤ) : rounded u m d i ≤ u := by
  induction m generalizing d i with
  | zero => simp only [rounded]; split <;> omega
  | succ m ih =>
    cases d with
    | zero => exact (Nat.div_le_self ..).trans (ih 0 i)
    | succ d =>
      rw [rounded]
      split
      next =>
        have := ih (d+1) i
        have := ih d (i-(m+1-2*(d+1):ℕ))
        omega
      next => omega

theorem rounded_zero_of_count {u m d : ℕ} {i : ℤ} (h : count m d i=0) :
    rounded u m d i=0 := by
  have H := (rounded_encloses u m d i).1
  rw [h,Nat.mul_zero] at H
  have hzero := Nat.mul_eq_zero.mp (Nat.eq_zero_of_le_zero H)
  have hp := Nat.two_pow_pos m
  omega

def halfLayers (w n mask u : ℕ) : ℕ → List ℕ
  | 0 => [if n=0 then 0 else u]
  | m+1 =>
    let row := halfLayers w n mask u m
    (List.range ((m+1)/2+1)).map fun
      | 0 => (entry row 0 >>> 1) &&& mask
      | d+1 =>
        let h := m+1-2*(d+1)
        ((entry row (d+1) + (entry row d <<< ((w+1)*h))) >>> 1) &&& mask

def roundedLayers (w n u m : ℕ) : List ℕ :=
  halfLayers w n (repeatDigit (w+1) n (2^w-1)) u m

private theorem digit_single {w v : ℕ} (hv : v<2^w) (i : ℕ) :
    digit w v i = if i=0 then v else 0 := by
  cases i with
  | zero => simp [digit_zero,Nat.mod_eq_of_lt hv]
  | succ i => rw [digit_succ,Nat.shiftRight_eq_div_pow,Nat.div_eq_of_lt hv]; simp [digit]

private theorem entry_mapped (f : ℕ → ℕ) (n d : ℕ) :
    entry ((List.range n).map f) d = if d<n then f d else 0 := by
  by_cases h : d<n <;> simp [entry,h]

/-- Digit `i` in entry `d` computes the rounded count. Digits outside the
stored interval and impossible endpoints are zero. -/
theorem roundedLayers_digit {w u : ℕ} (hu : u<2^w) (n m d i : ℕ) :
    digit (w+1) (entry (roundedLayers w n u m) d) i =
      if i<n then rounded u m d i else 0 := by
  have hu' : u<2^(w+1) := by rw [pow_succ]; omega
  unfold roundedLayers
  induction m generalizing d i with
  | zero =>
    cases d with
    | zero =>
      by_cases hn : n=0
      · simp [hn,halfLayers,entry,digit]
      · by_cases hi : i=0 <;> simp [halfLayers,entry,hn,digit_single hu',hi,rounded]
    | succ d => simp [halfLayers,entry,digit,rounded]
  | succ m ih =>
    let M := repeatDigit (w+1) n (2^w-1)
    let row := halfLayers w n M u m
    have prev (d i : ℕ) : digit (w+1) (entry row d) i =
        if i<n then rounded u m d i else 0 := ih _ _
    rw [halfLayers,entry_mapped]
    by_cases hd : d<(m+1)/2+1
    · rw [ite_eq_left hd]
      cases d with
      | zero => rw [digit_half_mask,prev]; split <;> simp_all [rounded]
      | succ d =>
        have legal : 2*(d+1)≤m+1 := by omega
        let h := m+1-2*(d+1)
        let x := entry row (d+1)
        let y := entry row d <<< ((w+1)*h)
        change digit (w+1) (((x+y) >>> 1) &&& M) i = _
        rw [digit_half_mask]
        split
        next hi =>
          have small (a k : ℕ) : digit (w+1) (entry row a) k ≤ u := by
            rw [prev]; split <;> first | apply rounded_le | omega
          have add (j : ℕ) (_ : j≤i) : digit (w+1) x j + digit (w+1) y j < 2^(w+1) := by
            have H := small (d+1) j
            have K := small d (j-h)
            dsimp only [x,y]
            rw [digit_left,pow_succ]
            split <;> omega
          rw [digit_add add]
          dsimp only [x,y]
          rw [digit_left,prev,ite_eq_left hi,rounded,ite_eq_left (show 2*(d+1)≤m+1 ∧ (0:ℤ)≤i from ⟨legal,by positivity⟩)]
          by_cases hk : h≤i
          · rw [ite_eq_left hk,prev,ite_eq_left (by omega : i-h<n),Int.natCast_sub hk]
          · rw [ite_eq_right hk,rounded_zero_of_count (u:=u) (m:=m) (d:=d) (i:=(i:ℤ)-h) (count_negative (by omega))]
        next _ => rfl
    · rw [ite_eq_right hd,rounded_zero_of_count (count_illegal (by omega : m+1<2*d) i)]
      simp [digit]

end CentralUnimodality.EndpointDeficit
