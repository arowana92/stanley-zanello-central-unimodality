module

public import CentralUnimodality.SurvivalBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The zero-frequency last-return split has weights r_k r_(N-k), where
r_k is the normalized middle binomial coefficient. Deleting one uniformly
chosen position gives its law at the preceding half-length. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit

noncomputable def weight (N k : ℕ) : ℝ := survival k*survival (N-k)
noncomputable def average (N : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N+1), weight N k * f k

theorem weight_pos (N k : ℕ) : 0 < weight N k := mul_pos (survival_pos _) (survival_pos _)

private theorem half_step (k : ℕ) :
    ((k:ℝ)+1)*survival (k+1) = (k+1/2)*survival k := by
  rw [survival_succ]
  field_simp

theorem adjacent_weights {N k : ℕ} (hk : k≤N) :
    ((N:ℝ)+1-k)*weight (N+1) k + (k+1:ℕ)*weight (N+1) (k+1) =
      (N+1:ℕ)*weight N k := by
  have h₁ := half_step (N-k)
  have h₂ := half_step k
  rw [Nat.cast_sub hk] at h₁
  simp only [weight,show N+1-k=(N-k)+1 by omega,show N+1-(k+1)=N-k by omega,Nat.cast_succ]
  linear_combination survival k*h₁ + survival (N-k)*h₂

/-- The value at index k after deletion comes from indices k and k+1. -/
theorem deletion (N : ℕ) (f : ℕ → ℝ) :
    ((N:ℝ)+1)*average N f =
      average (N+1) (fun k => ((N:ℝ)+1-k)*f k+(k:ℝ)*f (k-1)) := by
  let A := fun k : ℕ => weight (N+1) k * (((N:ℝ)+1-k)*f k)
  let B := fun k : ℕ => weight (N+1) k * ((k:ℝ)*f (k-1))
  have zeroA : A (N+1)=0 := by simp [A]
  have zeroB : B 0=0 := by simp [B]
  rw [average,average,Finset.mul_sum]
  simp only [mul_add,Finset.sum_add_distrib]
  change _ = (∑ k ∈ Finset.range (N+1+1), A k) + ∑ k ∈ Finset.range (N+1+1), B k
  rw [Finset.sum_range_succ A,Finset.sum_range_succ' B,zeroA,zeroB,add_zero,add_zero,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have h := adjacent_weights (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  dsimp only [A,B]
  rw [Nat.add_sub_cancel]
  push_cast at h ⊢
  linear_combination -(f k)*h

theorem average_const (N : ℕ) (c : ℝ) : average N (fun _ => c)=c := by
  induction N with
  | zero => simp [average,weight,survival]
  | succ N ih =>
    have H := deletion N (fun _ => c)
    rw [ih] at H
    have f (k : ℕ) : ((N:ℝ)+1-k)*c+(k:ℝ)*c=((N:ℝ)+1)*c := by ring
    simp only [f] at H
    unfold average at H ⊢
    have hn : (N:ℝ)+1 ≠ 0 := by positivity
    apply mul_left_cancel₀ hn
    rw [Finset.mul_sum]
    simpa only [mul_left_comm] using H.symm

end CentralUnimodality.ReturnSplit
