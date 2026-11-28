module

public import CentralUnimodality.HeightBlockChecks
public import CentralUnimodality.DyckReduction
import Mathlib.Data.Nat.Sqrt

/-! An integer square root bounds the exact real comparison threshold.
The resulting index can be evaluated using natural number arithmetic. -/
@[expose] public section

namespace CentralUnimodality.HeightBlock

def dyckCut (n : ℕ) : ℕ :=
  if n=0 then 0 else ((8*n^3).sqrt+3)/3-n

theorem ceil_dyck_le_cut (n : ℕ) : ⌈dyckLower n⌉₊≤dyckCut n := by
  by_cases hz : n=0
  · simp [hz,dyckLower,dyckCut]
  have sq : 8*(n:ℝ)^3<(((8*n^3).sqrt:ℝ)+1)^2 := by
    exact_mod_cast Nat.lt_succ_sqrt' (8*n^3)
  have eq : (2*Real.sqrt 2*(n:ℝ)*Real.sqrt n)^2=8*(n:ℝ)^3 := by
    rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sq_sqrt (by positivity)]
    ring
  have lt : 2*Real.sqrt 2*(n:ℝ)*Real.sqrt n<((8*n^3).sqrt:ℝ)+1 := by
    by_contra! h
    nlinarith only [sq,eq,sq_nonneg (2*Real.sqrt 2*n*Real.sqrt n-(((8*n^3).sqrt:ℝ)+1)),h,
      mul_nonneg (sub_nonneg.mpr h) (show 0≤2*Real.sqrt 2*n*Real.sqrt n+(((8*n^3).sqrt:ℝ)+1) by positivity)]
  have rounded : (8*n^3).sqrt+1≤3*(dyckCut n+n) := by rw [dyckCut,ite_eq_right hz]; omega
  have hr : ((8*n^3).sqrt:ℝ)+1≤3*((dyckCut n:ℝ)+n) := by exact_mod_cast rounded
  apply Nat.ceil_le.mpr
  unfold dyckLower
  linarith only [lt,hr]

end CentralUnimodality.HeightBlock
