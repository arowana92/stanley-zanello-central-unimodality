module

public import CentralUnimodality.ReturnSplitMoments
import Mathlib.Tactic.FieldSimp

/-! Exact evaluation of the discrete last-return convolution on rising
factorials. These are the moments used to average a polynomial at gamma
times of shapes j+1/2 and j+1. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit

noncomputable def fullRising (k a : ℕ) : ℝ := (k+1).ascFactorial a

noncomputable def halfRising (k a : ℕ) : ℝ :=
  fullRising k a*survival (k+a)/survival k

noncomputable def betaWeight (a b : ℕ) : ℝ :=
  a.factorial*b.factorial*survival a*survival b/(a+b).factorial

theorem fullRising_choose (k a : ℕ) : fullRising k a=a.factorial*((k+a).choose a:ℝ) := by
  unfold fullRising
  exact_mod_cast Nat.ascFactorial_eq_factorial_mul_choose k a

@[simp] theorem fullRising_zero (k : ℕ) : fullRising k 0=1 := by simp [fullRising]

@[simp] theorem halfRising_zero (k : ℕ) : halfRising k 0=1 := by simp [halfRising,(survival_pos k).ne']

theorem fullRising_succ (k a : ℕ) : fullRising k (a+1)=(k+1+a:ℝ)*fullRising k a := by
  simp [fullRising,Nat.ascFactorial_succ]

theorem halfRising_succ (k a : ℕ) : halfRising k (a+1)=(k+1/2+a:ℝ)*halfRising k a := by
  rw [halfRising,fullRising_succ,Nat.add_succ,survival_succ,halfRising,Nat.cast_add]
  field_simp
  ring

private theorem shift_support (N a b : ℕ) (f : ℕ → ℝ)
    (before : ∀ k<a, f k=0) (after : ∀ k, a+N<k → k≤N+a+b → f k=0) :
    (∑ k ∈ Finset.range (N+a+b+1), f k)=∑ k ∈ Finset.range (N+1), f (a+k) := by
  rw [show N+a+b+1=a+(N+1+b) by omega,Finset.sum_range_add,
    Finset.sum_eq_zero (fun k hk => before k (Finset.mem_range.mp hk)),zero_add,Finset.sum_range_add]
  have hz : (∑ k ∈ Finset.range b, f (a+(N+1+k)))=0 :=
    Finset.sum_eq_zero (fun k hk => after _ (by omega) (by have := Finset.mem_range.mp hk; omega))
  rw [hz,add_zero]

/-- Averaging the product of two half-shape moments gives the full-shape
moment times the arcsine beta coefficient, also at zero time. -/
theorem rising_split (N a b : ℕ) :
    average N (fun k => halfRising k a*halfRising (N-k) b)=
      betaWeight a b*fullRising N (a+b) := by
  let L := N+a+b
  let f := fun k => weight L k*((k.choose a:ℝ)*((L-k).choose b:ℝ))
  have H := mixed_binomial_moment L a b
  change (∑ k ∈ Finset.range (L+1), f k)=_ at H
  have before (k : ℕ) (hk : k<a) : f k=0 := by simp [f,Nat.choose_eq_zero_of_lt hk]
  have after (k : ℕ) (hk : a+N<k) (hl : k≤N+a+b) : f k=0 := by
    have Hk : L-k<b := by dsimp [L]; omega
    simp [f,Nat.choose_eq_zero_of_lt Hk]
  have shortened := shift_support N a b f before after
  rw [shortened] at H
  calc
    _ = (a.factorial:ℝ)*b.factorial*∑ k ∈ Finset.range (N+1), f (a+k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hl : L-(k+a)=(N-k)+b := by dsimp [L]; omega
      simp only [f,weight,halfRising,fullRising_choose,hl,Nat.add_comm a k]
      field_simp [(survival_pos k).ne',(survival_pos (N-k)).ne']
    _ = _ := by
      rw [H,betaWeight,fullRising_choose,show N+(a+b)=L by dsimp [L]; omega]
      field_simp

end CentralUnimodality.ReturnSplit
