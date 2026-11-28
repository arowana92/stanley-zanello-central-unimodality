module

public import CentralUnimodality.Statement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Reverse each fixed-length rank row about its own maximal rank
`d*(m-d)`. In these coordinates the two predecessors have shifts zero
and the new ballot height. Truncation to an initial interval is exact. -/
@[expose] public section

namespace CentralUnimodality.EndpointDeficit

def signedCount (m d : ℕ) (j : ℤ) : ℕ :=
  if 0 ≤ j then rankCountLength m d j.toNat else 0

private theorem signed_step (m d : ℕ) (z : ℤ) (hd : 2*(d+1) ≤ m+1) :
    signedCount (m+1) (d+1) (z+(d+1:ℕ)) = signedCount m (d+1) z + signedCount m d z := by
  by_cases hz : 0 ≤ z
  · have hpre : z.toNat+(d+1) = (z+(d+1:ℕ)).toNat := by omega
    simp only [signedCount, ite_eq_left hz, ite_eq_left (show 0≤z+(d+1:ℕ) by omega), ← hpre]
    exact rankCountLength_step m d z.toNat hd
  · simp only [signedCount, ite_eq_right hz, add_zero]
    split
    · apply rankCountLength_zero_of_rank; omega
    · rfl

/-- Count at deficit `i` from the maximal size at a prescribed number of parts. -/
def count (m d : ℕ) (i : ℤ) : ℕ :=
  signedCount m d ((m:ℤ)*d-(d:ℤ)^2-i)

theorem count_negative {m d : ℕ} {i : ℤ} (hi : i<0) : count m d i = 0 := by
  unfold count signedCount
  split
  next h =>
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro l hl
    obtain ⟨hl, hs⟩ := Finset.mem_filter.mp hl
    obtain ⟨hf, hlen⟩ := mem_partitions.mp hl
    have hb := sum_bound_length hf
    rw [hlen] at hb
    have hb' : (l.sum:ℤ)+(d:ℤ)*d ≤ (m:ℤ)*d := by exact_mod_cast hb
    have hs' := congrArg (fun a : ℕ => (a:ℤ)) hs
    change (l.sum:ℤ) = (((m:ℤ)*d-(d:ℤ)^2-i).toNat:ℤ) at hs'
    rw [Int.toNat_of_nonneg h] at hs'
    nlinarith
  next => rfl

theorem count_zero_parts (m : ℕ) (i : ℤ) : count m 0 i = if i=0 then 1 else 0 := by
  simp only [count, Nat.cast_zero, mul_zero, zero_pow (by decide : 2≠0), sub_zero, zero_sub,
    signedCount, rankCountLength_zero_parts]
  split <;> split <;> simp_all <;> omega

theorem count_illegal {m d : ℕ} (hd : m<2*d) (i : ℤ) : count m d i = 0 := by
  simp [count, signedCount, rankCountLength_zero_of_length hd]

theorem count_step (m d : ℕ) (i : ℤ) (hd : 2*(d+1) ≤ m+1) :
    count (m+1) (d+1) i = count m (d+1) i + count m d (i-(m+1-2*(d+1):ℕ)) := by
  unfold count
  rw [Nat.cast_sub hd]
  push_cast
  have H := signed_step m d ((m:ℤ)*(d+1)-((d:ℤ)+1)^2-i) hd
  push_cast at H
  convert H using 2 <;> congr 1 <;> ring

/-- The full rank is the sum of the endpoint rows at their corresponding deficits. -/
theorem rank_eq_sum (m j : ℕ) :
    rankCount m j = ∑ d ∈ Finset.range (m/2+1), count m d ((m:ℤ)*d-(d:ℤ)^2-j) := by
  unfold rankCount
  apply Finset.sum_congr rfl
  intro d _
  rw [count, show (m:ℤ)*d-(d:ℤ)^2-((m:ℤ)*d-(d:ℤ)^2-j)=j by ring]
  simp [signedCount]

end CentralUnimodality.EndpointDeficit
