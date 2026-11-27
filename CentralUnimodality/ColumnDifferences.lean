module

public import CentralUnimodality.MomentExtraction

/-! Sensitivity of a moment column to its last, previously unknown entry.
All lower entries agree. Only the two boundary terms of a product can change. -/
@[expose] public section

namespace CentralUnimodality.Laurent

open PowerSeries

theorem sumRange_congr {f g : ℕ → Laurent} {n : ℕ} (h : ∀ i < n, f i = g i) :
    sumRange f n = sumRange g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumRange, sumRange, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem convolution_congr {A B D E : ℕ → Laurent} {r : ℕ}
    (hA : ∀ i ≤ r, A i = D i) (hB : ∀ i ≤ r, B i = E i) :
    convolution A B r = convolution D E r := by
  apply sumRange_congr
  intro i hi
  rw [hA i (by omega), hB (r-i) (by omega)]

theorem shifted_congr (b : MomentBase) (d : ℕ) {A B : ℕ → Laurent} {r : ℕ}
    (h : ∀ i ≤ r, A i = B i) : shifted b d A r = shifted b d B r := by
  apply sumRange_congr
  intro i _
  rw [h (r-i) (by omega)]

theorem exponential_congr {A B : ℕ → Laurent} {r : ℕ} (h : ∀ i ≤ r, A i = B i) :
    exponential A r = exponential B r := by
  apply sumRange_congr
  intro i _
  rw [h (r-i) (by omega)]

theorem eval_convolution_difference {A B D E : ℕ → Laurent} {r : ℕ} (hr : 0 < r)
    (hA : ∀ i < r, A i = D i) (hB : ∀ i < r, B i = E i) :
    eval (convolution A B r) - eval (convolution D E r) =
      (eval (A r)-eval (D r))*eval (E 0) + eval (D 0)*(eval (B r)-eval (E r)) := by
  simp only [convolution, eval_sumRange, eval_mul, ← Finset.sum_sub_distrib]
  cases r with
  | zero => omega
  | succ n =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [Nat.sub_self, Nat.sub_zero, hA 0 (by omega), hB 0 (by omega)]
    have hz : (∑ i ∈ Finset.range n, (eval (A (i+1))*eval (B (n+1-(i+1))) -
        eval (D (i+1))*eval (E (n+1-(i+1))))) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have := Finset.mem_range.mp hi
      rw [hA _ (by omega), hB _ (by omega), sub_self]
    rw [hz]
    ring

theorem eval_shifted_difference (b : MomentBase) (d : ℕ) {A B : ℕ → Laurent} {r : ℕ}
    (h : ∀ i < r, A i = B i) :
    eval (shifted b d A r) - eval (shifted b d B r) = eval (A r)-eval (B r) := by
  simp only [shifted, eval_sumRange]
  rw [← Finset.sum_sub_distrib, Finset.sum_range_succ']
  have hz : (∑ i ∈ Finset.range r, (eval (b.divided d (A (r-(i+1))) (i+1)) -
      eval (b.divided d (B (r-(i+1))) (i+1)))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have := Finset.mem_range.mp hi
    rw [h _ (by omega), sub_self]
  rw [hz,zero_add,Nat.sub_zero,MomentBase.divided,MomentBase.divided]

theorem eval_exponential_difference {A B : ℕ → Laurent} {r : ℕ} (h : ∀ i < r, A i = B i) :
    eval (exponential A r) - eval (exponential B r) = eval (A r)-eval (B r) := by
  simp only [exponential, eval_sumRange]
  rw [← Finset.sum_sub_distrib, Finset.sum_range_succ']
  have hz : (∑ i ∈ Finset.range r, (eval (scaleShift (1/((i+1).factorial:ℚ)) 0 (A (r-(i+1)))) -
      eval (scaleShift (1/((i+1).factorial:ℚ)) 0 (B (r-(i+1)))))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have := Finset.mem_range.mp hi
    rw [h _ (by omega),sub_self]
  rw [hz]
  simp [eval_scaleShift,rootPower_zero]

end CentralUnimodality.Laurent
