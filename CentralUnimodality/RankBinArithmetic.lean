module

public import CentralUnimodality.InnerArcNumbers
import Mathlib.Data.Nat.Sqrt

/-! Rational enclosures for the time and saddle parameter checks. Rounding
is outward at each boundary, including arbitrarily small positive costs. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic
open Real

def scale : ℕ := 1000000

def rootLo (x : ℚ) : ℚ := (Nat.sqrt ⌊(scale:ℚ)^2*x⌋₊:ℚ)/scale
def rootHi (x : ℚ) : ℚ := rootLo x+1/scale

theorem root_enclosure {x : ℚ} (hx : 0 ≤ x) : (rootLo x:ℝ) ≤ √(x:ℝ) ∧ √(x:ℝ) ≤ (rootHi x:ℝ) := by
  let y := (scale:ℚ)^2*x
  let t := ⌊y⌋₊
  let a := Nat.sqrt t
  have low : (t:ℚ) ≤ y := Nat.floor_le (by dsimp [y]; positivity)
  have high : y < (t:ℚ)+1 := Nat.lt_floor_add_one _
  have hl : (a:ℚ)^2 ≤ t := by exact_mod_cast Nat.sqrt_le' t
  have hh : (t:ℚ)+1 ≤ ((a:ℚ)+1)^2 := by exact_mod_cast (Nat.lt_succ_sqrt' t)
  have bounds : (a:ℝ)^2 ≤ (scale:ℝ)^2*(x:ℝ) ∧ (scale:ℝ)^2*(x:ℝ) ≤ ((a:ℝ)+1)^2 := by
    dsimp [y] at low high
    exact ⟨by exact_mod_cast hl.trans low,by exact_mod_cast high.le.trans hh⟩
  have hs : 0 < (scale:ℝ) := by norm_num [scale]
  have hx' : 0 ≤ (x:ℝ) := by exact_mod_cast hx
  have H := (sq_le_sq₀ (Nat.cast_nonneg (α:=ℝ) a) (mul_nonneg (sqrt_nonneg (x:ℝ)) hs.le)).mp
    (show (a:ℝ)^2 ≤ (√(x:ℝ)*scale)^2 by rw [mul_pow,sq_sqrt hx']; linarith only [bounds.1])
  have H' := (sq_le_sq₀ (mul_nonneg (sqrt_nonneg (x:ℝ)) hs.le) (by positivity : 0 ≤ (a:ℝ)+1)).mp
    (show (√(x:ℝ)*scale)^2 ≤ ((a:ℝ)+1)^2 by rw [mul_pow,sq_sqrt hx']; linarith only [bounds.2])
  have he : (rootLo x:ℝ)=(a:ℝ)/(scale:ℝ) := by unfold rootLo; push_cast; rfl
  refine ⟨he ▸ (div_le_iff₀ hs).mpr H,?_⟩
  unfold rootHi; push_cast; rw [he,← add_div]
  exact (le_div_iff₀ hs).mpr H'

def charge (x : ℚ) : ℚ := (⌈(scale:ℚ)*x⌉₊:ℚ)/scale

theorem charge_upper (x : ℚ) : x ≤ charge x := by
  apply (le_div_iff₀ (by norm_num [scale] : (0:ℚ) < scale)).mpr
  simpa only [mul_comm] using Nat.le_ceil ((scale:ℚ)*x)

/-- Round the eighth-interval input down before the reciprocal Taylor sum.
The upward rounding of its output keeps the eighth power inexpensive. -/
def decay (x : ℚ) : ℚ :=
  (charge (upperNegExp ((⌊128*x⌋₊:ℚ)/1024)))^8

theorem decay_upper {x : ℚ} (hx : 0 ≤ x) : exp (-(x:ℝ)) ≤ (decay x:ℝ) := by
  let y : ℚ := (⌊128*x⌋₊:ℚ)/1024
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hfloor := Nat.floor_le (mul_nonneg (by norm_num : (0:ℚ) ≤ 128) hx)
  have hy' : y ≤ x/8 := by dsimp [y]; linarith only [hfloor]
  have hreal : (y:ℝ) ≤ (x:ℝ)/8 := by exact_mod_cast hy'
  have hu := (upperNegExp_sound hy).trans ((Rat.cast_le (K:=ℝ)).mpr (charge_upper _))
  have H := pow_le_pow_left₀ (exp_pos _).le hu 8
  rw [← exp_nat_mul] at H
  unfold decay; push_cast
  norm_num only [Nat.cast_ofNat] at H
  exact (exp_le_exp.mpr (by linarith only [hreal] : -(x:ℝ) ≤ (8:ℝ)*(-(y:ℝ)))).trans H

end CentralUnimodality.MarkedExcursion.BinArithmetic
