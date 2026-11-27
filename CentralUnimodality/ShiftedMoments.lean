module

public import CentralUnimodality.Laurent
public import CentralUnimodality.MomentSeries
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-! Exact Laurent action of size rescaling on the moment columns, after
factoring out either the Catalan or the central binomial base series. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries

inductive MomentBase
  | dyck
  | ballot

namespace MomentBase

noncomputable def value : MomentBase → PowerSeries ℚ
  | dyck => dyckBase
  | ballot => ballotBase

def shift : MomentBase → ℤ
  | dyck => -1
  | ballot => -2

theorem euler_value (b : MomentBase) :
    2*sizeEuler b.value = b.value*(rootPower b.shift - 1) := by
  cases b with
  | dyck => simpa only [value, shift, rootPower_neg_one] using sizeEuler_dyckBase
  | ballot =>
    have he : rootPower (-2) = ballotBase^2 := by
      rw [show (-2:ℤ) = (-1)+(-1) by decide, rootPower_add, rootPower_neg_one, pow_two]
    simpa only [value, shift, he] using sizeEuler_ballotBase

def euler (b : MomentBase) (p : Laurent) : Laurent :=
  Laurent.add (Laurent.euler p) (Laurent.add (Laurent.scaleShift (1/2) b.shift p)
    (Laurent.scaleShift (-1/2) 0 p))

theorem eval_euler (b : MomentBase) (p : Laurent) :
    b.value*Laurent.eval (b.euler p) = sizeEuler (b.value*Laurent.eval p) := by
  simp only [euler, Laurent.eval_add, Laurent.eval_euler, Laurent.eval_scaleShift, rootPower_zero,
    mul_one, sizeEuler_mul, neg_div, map_neg]
  have hhalf : C ((1:ℚ)/2) * 2 = (1:PowerSeries ℚ) := by
    rw [← map_ofNat (C (R := ℚ)) 2, ← map_mul]
    norm_num
  linear_combination -C ((1:ℚ)/2)*Laurent.eval p*b.euler_value +
    sizeEuler b.value*Laurent.eval p*hhalf

def divided (b : MomentBase) (d : ℕ) (p : Laurent) : ℕ → Laurent
  | 0 => p
  | j+1 => Laurent.scaleShift ((d:ℚ)/(j+1)) 0 (b.euler (b.divided d p j))

end MomentBase

theorem dividedEuler_zero (d : ℕ) (F : PowerSeries ℚ) : dividedEuler d 0 F = F := by
  apply PowerSeries.ext
  simp [dividedEuler]

theorem dividedEuler_succ (d j : ℕ) (F : PowerSeries ℚ) :
    dividedEuler d (j+1) F = C ((d:ℚ)/(j+1)) * sizeEuler (dividedEuler d j F) := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_C_mul, coeff_sizeEuler, dividedEuler, coeff_mk, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_succ, pow_succ]
  field_simp

theorem MomentBase.eval_divided (b : MomentBase) (d j : ℕ) (p : Laurent) :
    b.value * Laurent.eval (b.divided d p j) = dividedEuler d j (b.value * Laurent.eval p) := by
  induction j with
  | zero => rw [MomentBase.divided, dividedEuler_zero]
  | succ j ih =>
    rw [MomentBase.divided, Laurent.eval_scaleShift, rootPower_zero, mul_one, dividedEuler_succ, ← ih,
      ← MomentBase.eval_euler]
    ac_rfl

end CentralUnimodality
