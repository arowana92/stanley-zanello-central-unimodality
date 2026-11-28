module

public import CentralUnimodality.ReturnCharacterMoment
import Mathlib.Tactic.Linarith

/-! Cancellation in the inverse renewal convolution. A residual nearly
constant across return times can be bounded at the natural survival scale,
including at arbitrarily large half-lengths. -/
@[expose] public section

namespace CentralUnimodality
open PowerSeries

noncomputable def returnSymbol (ω : ℝ) (j : ℕ) : ℂ :=
  coeff (2*j) (fairSeries (areaCharacter ω) firstReturns)

theorem norm_returnSymbol_le (ω : ℝ) (j : ℕ) : ‖returnSymbol ω j‖≤returnMass j :=
  norm_coeff_fairSeries _ (fun a => (norm_areaCharacter ω a).le) _ _

theorem returnSymbol_sum_dist (ω : ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range (N+1), ‖(returnMass j:ℂ)-returnSymbol ω j‖ ≤ N*(|ω|/2) := by
  induction N with
  | zero =>
    have zeroSymbol : returnSymbol ω 0=0 := norm_le_zero_iff.mp (returnMass_zero ▸ norm_returnSymbol_le ω 0)
    simp [zeroSymbol]
  | succ N ih =>
    rw [Finset.sum_range_succ,Nat.cast_succ,add_mul,one_mul]
    exact add_le_add ih (by rw [norm_sub_rev]; exact returnCharacter_dist ω N)

theorem returnSymbol_remainder (ω : ℝ) (N : ℕ) :
    ‖1-∑ j ∈ Finset.range (N+1), returnSymbol ω j‖ ≤ survival N+N*(|ω|/2) := by
  have mass : (∑ j ∈ Finset.range (N+1), (returnMass j:ℂ))=1-(survival N:ℂ) := by
    exact_mod_cast returnMass_sum N
  have eqn : 1-∑ j ∈ Finset.range (N+1), returnSymbol ω j =
      (survival N:ℂ) + ∑ j ∈ Finset.range (N+1), ((returnMass j:ℂ)-returnSymbol ω j) := by
    rw [Finset.sum_sub_distrib,mass]; ring
  rw [eqn]
  have h := (norm_sum_le _ _).trans (returnSymbol_sum_dist ω N)
  exact (norm_add_le ..).trans (add_le_add (by simp [abs_of_pos (survival_pos N)]) h)

theorem inverse_smooth_bound (ω : ℝ) (N : ℕ) (E : ℕ → ℂ) {L : ℝ}
    (hd : ∀ j≤N, ‖E N-E (N-j)‖≤j*L) :
    ‖E N-∑ j ∈ Finset.range (N+1), returnSymbol ω j * E (N-j)‖ ≤
      (survival N+N*(|ω|/2))*‖E N‖ + (N*survival N)*L := by
  let S := Finset.range (N+1)
  have id : E N-∑ j ∈ S, returnSymbol ω j*E (N-j) =
      (1-∑ j ∈ S, returnSymbol ω j)*E N +
        ∑ j ∈ S, returnSymbol ω j*(E N-E (N-j)) := by
    simp only [sub_mul,one_mul,Finset.sum_mul,mul_sub,Finset.sum_sub_distrib]
    ring
  have varBound : ‖∑ j ∈ S, returnSymbol ω j*(E N-E (N-j))‖≤(N*survival N)*L := by
    calc
      _ ≤ ∑ j ∈ S, ‖returnSymbol ω j*(E N-E (N-j))‖ := norm_sum_le ..
      _ ≤ ∑ j ∈ S, ((j:ℝ)*returnMass j)*L := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul]
        have h := mul_le_mul (norm_returnSymbol_le ω j) (hd j (by
          have := Finset.mem_range.mp hj; omega)) (norm_nonneg _) (by unfold returnMass; positivity)
        simpa only [mul_left_comm,mul_assoc] using h
      _ = _ := by rw [← Finset.sum_mul,returnMass_time_sum]
  change ‖E N-∑ j ∈ S, returnSymbol ω j*E (N-j)‖≤_
  rw [id]
  apply (norm_add_le ..).trans
  rw [norm_mul]
  exact add_le_add (mul_le_mul_of_nonneg_right (returnSymbol_remainder ω N) (norm_nonneg _)) varBound

end CentralUnimodality
