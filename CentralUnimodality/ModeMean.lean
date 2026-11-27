module

public import CentralUnimodality.Unimodality
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! A nonnegative row increasing through p has mean at least p/2.
Pair the entries i and p−i in the initial interval. -/
@[expose] public section

namespace CentralUnimodality

theorem prefix_mean_bound (f : ℕ → ℕ) {p D : ℕ} (hp : p ≤ D)
    (hu : ∀ k < p, f k ≤ f (k+1)) :
    p * (∑ i ∈ Finset.range (D+1), f i) ≤ 2*(∑ i ∈ Finset.range (D+1), i*f i) := by
  have mono {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p) : f i ≤ f j := by
    induction j,hij using Nat.le_induction with
    | base => rfl
    | succ j _ ih => exact (ih (by omega)).trans (hu _ (by omega))
  have pair {a b : ℕ} (hs : a+b=p) : p*f a + p*f b ≤ 2*(a*f a)+2*(b*f b) := by
    rcases le_total a b with hab|hba
    · have hf := mono hab (by omega)
      obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hab
      obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le hf
      rw [← hs,he,hd]
      nlinarith only [Nat.zero_le (d*e)]
    · have hf := mono hba (by omega)
      obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hba
      obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le hf
      rw [← hs,he,hd]
      nlinarith only [Nat.zero_le (d*e)]
  have refl (g : ℕ → ℕ) : (∑ i ∈ Finset.range (p+1), g (p-i)) = ∑ i ∈ Finset.range (p+1), g i := by
    simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect g (p+1)
  have hs := Finset.sum_le_sum (s := Finset.range (p+1)) (fun i hi =>
    pair (a := i) (b := p-i) (by have := Finset.mem_range.mp hi; omega))
  simp only [Finset.sum_add_distrib] at hs
  rw [refl (fun i => p*f i),refl (fun i => 2*(i*f i)),← Finset.mul_sum,← Finset.mul_sum] at hs
  induction D,hp using Nat.le_induction with
  | base => omega
  | succ d hd ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ (fun i => i*f i) (d+1),mul_add,mul_add]
    apply add_le_add ih
    rw [← mul_assoc]
    exact Nat.mul_le_mul_right _ (by omega)

end CentralUnimodality
