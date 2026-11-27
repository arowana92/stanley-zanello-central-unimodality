module

public import CentralUnimodality.ColumnDifferences
import Mathlib.Tactic.LinearCombination

/-! Isolate the undetermined highest moment in the two area recurrences.
In both equations the factor left to invert is the Catalan square root. -/
@[expose] public section

namespace CentralUnimodality.Laurent

open PowerSeries

theorem dyckRhs_congr {A B : ℕ → Laurent} {r : ℕ} (ha : ∀ i ≤ r, A i = B i) :
    dyckRhs A r = dyckRhs B r := by
  unfold dyckRhs
  rw [convolution_congr ha (fun i hi => shifted_congr .dyck 1 (r := i) (fun t ht => ha t (by omega)))]

theorem ballotRhs_congr {A B D E : ℕ → Laurent} {r : ℕ}
    (ha : ∀ i ≤ r, A i = D i) (hb : ∀ i ≤ r, B i = E i) : ballotRhs A B r = ballotRhs D E r := by
  unfold ballotRhs
  rw [ha r le_rfl]
  congr 1
  apply exponential_congr
  intro i hi
  apply convolution_congr
  · intro j hj
    simp only [stripped, ha j (by omega)]
  · intro j hj
    exact shifted_congr .ballot 2 (r := j) (fun t ht => hb t (by omega))

theorem eval_shifted_zero (b : MomentBase) (d : ℕ) (D : ℕ → Laurent) :
    eval (shifted b d D 0) = eval (D 0) := by
  simp [shifted,eval_sumRange,MomentBase.divided]

theorem alpha_add_beta : eval alpha + eval beta = 1 := by
  simp only [alpha,beta,eval,rootPower_zero,rootPower_one,mul_one,add_zero,neg_div,map_neg]
  have h : C ((1:ℚ)/2)*2 = (1:PowerSeries ℚ) := by
    rw [← map_ofNat (C (R := ℚ)) 2, ← map_mul]; norm_num
  linear_combination h

theorem beta_pivot : 1 - 2*eval beta = catalanRoot := by rw [beta_identity, catalanRoot]; ring

theorem dyckRhs_difference {A B : ℕ → Laurent} {r : ℕ} (hr : 0 < r)
    (ha : ∀ i < r, A i = B i) (h₀ : eval (B 0) = 1) :
    eval (dyckRhs A r) - eval (dyckRhs B r) = 2*eval beta*(eval (A r)-eval (B r)) := by
  have hs := eval_shifted_difference .dyck 1 ha
  have hc := eval_convolution_difference hr ha (fun i hi => shifted_congr .dyck 1 (r := i) (fun t ht => ha t (by omega)))
  rw [eval_shifted_zero, h₀, mul_one, one_mul, hs] at hc
  simp only [dyckRhs,eval_add,eval_mul]
  linear_combination eval beta*hc

theorem ballotRhs_difference (D : ℕ → Laurent) {A B : ℕ → Laurent} {r : ℕ} (hr : 0 < r)
    (ha : ∀ i < r, A i = B i) (h₀ : eval (D 0) = 1) :
    eval (ballotRhs D A r) - eval (ballotRhs D B r) = eval beta*(eval (A r)-eval (B r)) := by
  have hsh (i : ℕ) (hi : i < r) : shifted .ballot 2 A i = shifted .ballot 2 B i :=
    shifted_congr .ballot 2 (r := i) (fun j hj => ha j (by omega))
  have hc := eval_convolution_difference (A := stripped D) hr (fun _ _ => rfl) hsh
  have he := eval_exponential_difference (r := r) (A := convolution (stripped D) (shifted .ballot 2 A))
    (B := convolution (stripped D) (shifted .ballot 2 B))
    (fun i hi => convolution_congr (fun _ _ => rfl) (fun j hj => hsh j (by omega)))
  have hstr : eval (stripped D 0) = eval beta := by
    simp [stripped,eval_add,eval_scaleShift,rootPower_zero,unitColumn,h₀]
    linear_combination -alpha_add_beta
  rw [sub_self, zero_mul, zero_add, hstr, eval_shifted_difference .ballot 2 ha] at hc
  simp only [ballotRhs,eval_add]
  linear_combination he+hc

end CentralUnimodality.Laurent
