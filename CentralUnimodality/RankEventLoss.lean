module

public import CentralUnimodality.TiltedDifferences
public import CentralUnimodality.LatticeDifference

/-! Restore the label tilt simultaneously at a saddle and its two neighbours
for any finite rank event with bounds on its first two finite differences. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

theorem small_rank_shift {m : ℕ} (hm : 4096 ≤ m) {z Δ : ℝ} (hz : 0 ≤ z)
    (hΔ : Δ=2*z*((m:ℝ)*√m)) (hshift : Δ ≤ 32) : 2*z ≤ 1/8192 := by
  have hm' : (4096:ℝ) ≤ m := by exact_mod_cast hm
  have hr : (64:ℝ) ≤ √m := (le_sqrt (by norm_num) (Nat.cast_nonneg _)).mpr (by linarith only [hm'])
  have hσ : (262144:ℝ) ≤ m*√m := by nlinarith only [mul_le_mul hm' hr (by norm_num) (Nat.cast_nonneg (α:=ℝ) m)]
  nlinarith only [hΔ,hshift,mul_le_mul_of_nonneg_left hσ hz]

theorem rank_event_loss {c z : ℝ} (hz : 0 ≤ z) (hstep : 2*z ≤ 1/8192) {m j : ℕ}
    (hj : meanRank c m=(j+1:ℕ)) (A : Finset (List Bool)) (hA : A ⊆ words m) (W : ℤ → ℝ)
    (U : Fin 3 → ℝ) (hW : ∀ k : ℕ, W (k:ℤ)=rankChange c z (meanRank c m) m*rankEvent (c+z) m k A)
    (bound : ∀ r k, |rankDifference r k W| ≤ U r) :
    let F := fun k => rankEvent c m k A
    F (j+1) ≤ U 0 ∧
      F (j+2)-F (j+1) ≤ 1001/1000*U 1+1001/1000*(2*z)*U 0 ∧
      -(F j-2*F (j+1)+F (j+2)) ≤ U 2+2*(1001/1000)*(2*z)*U 1 := by
  let R := rankChange c z (meanRank c m) m
  let X (k : ℕ) := R*rankEvent (c+z) m k A
  have hX (k : ℕ) : W (k:ℤ)=X k := hW k
  have H₀ : X (j+1) ≤ U 0 := by
    rw [← hX]; exact (le_abs_self _).trans (bound 0 _)
  have H₁ (k : ℕ) : |X (k+1)-X k| ≤ U 1 := by
    simp only [← hX,Nat.cast_add,Nat.cast_one]; exact bound 1 k
  have H₂ : -(X j-2*X (j+1)+X (j+2)) ≤ U 2 := by
    have H := bound 2 ((j:ℤ)+1)
    change |W ((j:ℤ)+1-1)+W ((j:ℤ)+1+1)-2*W ((j:ℤ)+1)| ≤ _ at H
    rw [add_sub_cancel_right,show (j:ℤ)+1+1=(j+2:ℕ) by push_cast; ring,
      show (j:ℤ)+1=(j+1:ℕ) by push_cast; rfl,hX,hX,hX] at H
    linarith only [(neg_le_abs _).trans H]
  have cost := change_difference_bounds (m := m) c hz hstep j A hA
  have Xeq (k : ℕ) : rankChange c z (j+1:ℕ) m*rankEvent (c+z) m k A=X k := by dsimp [X,R]; rw [hj]
  dsimp only at cost ⊢
  simp only [Xeq] at cost
  have hmid : rankEvent c m (j+1) A=X (j+1) := by
    simpa only [sub_self,mul_zero,exp_zero,one_mul,Xeq] using change_at_neighbor c z (j+1) (j+1) A hA
  refine ⟨hmid.le.trans H₀,?_,?_⟩
  · exact cost.1.trans (add_le_add (mul_le_mul_of_nonneg_left (H₁ (j+1)) (by norm_num))
      (mul_le_mul_of_nonneg_left H₀ (by positivity)))
  · have h := mul_le_mul_of_nonneg_left (add_le_add (H₁ (j+1)) (H₁ j)) (by positivity : 0 ≤ (1001/1000)*(2*z))
    exact cost.2.trans ((add_le_add H₂ h).trans_eq (by ring))

end CentralUnimodality.MarkedExcursion
