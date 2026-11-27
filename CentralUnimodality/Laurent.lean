module

public import CentralUnimodality.RootCoefficients
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! Executable sparse Laurent arithmetic for the rational moment certificates.
Each list is interpreted in the actual length series via the Catalan root. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries

abbrev Laurent := List (ℤ × ℚ)

namespace Laurent

noncomputable def eval : Laurent → PowerSeries ℚ
  | [] => 0
  | (h,a)::p => C a * rootPower h + eval p

def insert (h : ℤ) (a : ℚ) : Laurent → Laurent
  | [] => if a = 0 then [] else [(h,a)]
  | (k,b)::p =>
    if a = 0 then (k,b)::p else
    if h < k then (h,a)::(k,b)::p else
    if h = k then (if a+b = 0 then p else (k,a+b)::p)
    else (k,b)::insert h a p

theorem eval_insert (h : ℤ) (a : ℚ) (p : Laurent) :
    eval (insert h a p) = C a * rootPower h + eval p := by
  induction p with
  | nil => by_cases ha : a = 0 <;> simp [insert, eval, ha]
  | cons b p ih =>
    obtain ⟨k,b⟩ := b
    by_cases ha : a = 0
    · simp [insert,ha]
    by_cases hk : h < k
    · simp [insert, ha, hk, eval]
    by_cases he : h = k
    · subst k
      by_cases hz : a+b = 0
      · have hb : b = -a := by linarith
        simp [insert,ha,eval,hb]
      · simp [insert,ha,hz,eval,add_mul,add_assoc]
    · simp [insert,ha,hk,he,eval,ih,add_left_comm]

def add (p q : Laurent) := p.foldr (fun t acc => insert t.1 t.2 acc) q

theorem eval_add (p q : Laurent) : eval (add p q) = eval p + eval q := by
  induction p with
  | nil => simp [add,eval]
  | cons t p ih =>
    obtain ⟨h,c⟩ := t
    change eval (insert h c (add p q)) = _
    rw [eval_insert, ih, eval, add_assoc]

def scaleShift (a : ℚ) (s : ℤ) (p : Laurent) : Laurent :=
  p.map fun t => (s+t.1, a*t.2)

theorem eval_scaleShift (a : ℚ) (s : ℤ) (p : Laurent) :
    eval (scaleShift a s p) = C a * rootPower s * eval p := by
  induction p with
  | nil => simp [scaleShift,eval]
  | cons t p ih =>
    obtain ⟨h,c⟩ := t
    change C (a*c)*rootPower (s+h)+eval (scaleShift a s p) = _
    rw [eval, rootPower_add, map_mul, ih]
    ring

def mul : Laurent → Laurent → Laurent
  | [], _ => []
  | (h,c)::p, q => add (scaleShift c h q) (mul p q)

theorem eval_mul (p q : Laurent) : eval (mul p q) = eval p * eval q := by
  induction p with
  | nil => simp [mul,eval]
  | cons t p ih =>
    obtain ⟨h,c⟩ := t
    rw [mul, eval_add, eval_scaleShift, ih, eval, add_mul]

/-- Apply z*d/dz in the square-root coordinate to a Laurent polynomial. -/
def euler : Laurent → Laurent
  | [] => []
  | (h,c)::p => insert h (c*h/2) (insert (h-2) (-(c*h/2)) (euler p))

theorem eval_euler (p : Laurent) : eval (euler p) = sizeEuler (eval p) := by
  induction p with
  | nil => simp [euler, eval, sizeEuler]
  | cons t p ih =>
    obtain ⟨h,c⟩ := t
    rw [euler, eval_insert, eval_insert, ih, eval, sizeEuler_add, sizeEuler_mul]
    have hz : sizeEuler (C c) = 0 := by simp [sizeEuler]
    rw [hz, zero_mul, zero_add]
    have hhalf : C ((1:ℚ)/2) * 2 = (1:PowerSeries ℚ) := by
      rw [← map_ofNat (C (R := ℚ)) 2, ← map_mul]
      norm_num
    have he : C (c*h/2) = C c * (h:PowerSeries ℚ) * C ((1:ℚ)/2) := by
      simp [div_eq_mul_inv, mul_assoc]
    rw [map_neg, he]
    linear_combination -C c * C ((1:ℚ)/2) * sizeEuler_rootPower h +
      C c * sizeEuler (rootPower h) * hhalf

end Laurent

end CentralUnimodality
