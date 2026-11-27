module

public import CentralUnimodality.CatalanBase
public import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.LinearCombination

/-! The size Euler derivative on the square-root coordinate and on the
Dyck and even-ballot base series. These identities drive the moment recurrence. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries

noncomputable def sizeEuler (f : PowerSeries ℚ) : PowerSeries ℚ := X * derivative f

theorem coeff_sizeEuler (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (sizeEuler f) = (n:ℚ) * coeff n f := by
  cases n with
  | zero => simp [sizeEuler]
  | succ n => simp [sizeEuler, coeff_succ_X_mul, coeff_derivative, mul_comm]

theorem sizeEuler_add (f g : PowerSeries ℚ) : sizeEuler (f+g) = sizeEuler f+sizeEuler g := by
  simp [sizeEuler, mul_add]

theorem sizeEuler_sub (f g : PowerSeries ℚ) : sizeEuler (f-g) = sizeEuler f-sizeEuler g := by
  simp [sizeEuler, mul_sub]

theorem sizeEuler_mul (f g : PowerSeries ℚ) : sizeEuler (f*g) = sizeEuler f*g+f*sizeEuler g := by
  simp only [sizeEuler, Derivation.leibniz, smul_eq_mul]
  ring

theorem sizeEuler_X : sizeEuler X = X := by simp [sizeEuler]

theorem sizeEuler_nat (n : ℕ) : sizeEuler (n:PowerSeries ℚ) = 0 := by simp [sizeEuler]

theorem sizeEuler_root : 2*sizeEuler catalanRoot = catalanRoot-ballotBase := by
  have h := congrArg sizeEuler catalanRoot_sq
  rw [pow_two, sizeEuler_mul, sizeEuler_sub, sizeEuler_mul, sizeEuler_X,
    show sizeEuler 1 = 0 from sizeEuler_nat 1, show sizeEuler 4 = 0 from sizeEuler_nat 4] at h
  have he : catalanRoot*(2*sizeEuler catalanRoot) = catalanRoot*(catalanRoot-ballotBase) := by
    linear_combination h - catalanRoot_sq + catalanRoot_mul_ballotBase
  calc
    _ = ballotBase*(catalanRoot*(2*sizeEuler catalanRoot)) := by
      rw [← mul_assoc, mul_comm ballotBase catalanRoot, catalanRoot_mul_ballotBase, one_mul]
    _ = _ := by rw [he, ← mul_assoc, mul_comm ballotBase catalanRoot, catalanRoot_mul_ballotBase, one_mul]

theorem sizeEuler_ballotBase : 2*sizeEuler ballotBase = ballotBase*(ballotBase^2-1) := by
  have h := congrArg sizeEuler catalanRoot_mul_ballotBase
  rw [sizeEuler_mul, show sizeEuler 1 = 0 from sizeEuler_nat 1] at h
  have hv := sizeEuler_root
  calc
    _ = ballotBase*(catalanRoot*(2*sizeEuler ballotBase)) := by
      rw [← mul_assoc, mul_comm ballotBase catalanRoot, catalanRoot_mul_ballotBase, one_mul]
    _ = ballotBase*(-(2*sizeEuler catalanRoot)*ballotBase) := by
      congr 1
      linear_combination 2*h
    _ = _ := by
      rw [hv]
      linear_combination -ballotBase*catalanRoot_mul_ballotBase

theorem sizeEuler_dyckBase : 2*sizeEuler dyckBase = dyckBase*(ballotBase-1) := by
  have h := congrArg sizeEuler dyckBase_eq
  rw [sizeEuler_add, show sizeEuler 1 = 0 from sizeEuler_nat 1, sizeEuler_mul, sizeEuler_X,
    pow_two, sizeEuler_mul] at h
  have he : catalanRoot * sizeEuler dyckBase = dyckBase-1 := by
    unfold catalanRoot
    linear_combination h - dyckBase_eq
  have hu : (2-dyckBase)*ballotBase = dyckBase := by
    rw [← dyckBase_mul_root, mul_assoc, catalanRoot_mul_ballotBase, mul_one]
  calc
    _ = 2*ballotBase*(catalanRoot*sizeEuler dyckBase) := by
      rw [← mul_assoc, mul_assoc 2, mul_comm ballotBase catalanRoot, catalanRoot_mul_ballotBase, mul_one]
    _ = _ := by rw [he]; linear_combination -hu

end CentralUnimodality
