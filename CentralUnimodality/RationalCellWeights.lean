module

public import CentralUnimodality.BinnedInverseAllowance
import Mathlib.Data.Nat.Sqrt

/-! Rational square-root brackets and upward rounding for the local
inverse and the final frequency sums. Both brackets have step 10⁻⁹. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Real ReturnSplit

def rootUnits (x : ℚ) := Nat.sqrt ⌊10^18*x⌋₊
def rootLow (x : ℚ) : ℚ := (rootUnits x:ℚ)/10^9
def rootHigh (x : ℚ) : ℚ := ((rootUnits x:ℚ)+1)/10^9

theorem root_brackets {x : ℚ} (hx : 0≤x) : (rootLow x:ℝ)≤sqrt (x:ℝ) ∧ sqrt (x:ℝ)≤(rootHigh x:ℝ) := by
  let n := ⌊10^18*x⌋₊
  let k := rootUnits x
  have lo : k^2≤n := Nat.sqrt_le' n
  have hi : n+1≤(k+1)^2 := Nat.lt_succ_sqrt' n
  have fl : (n:ℚ)≤10^18*x := Nat.floor_le (by positivity)
  have fu : 10^18*x<(n:ℚ)+1 := Nat.lt_floor_add_one _
  have left : (k:ℚ)^2≤10^18*x := (by exact_mod_cast lo : (k:ℚ)^2≤(n:ℚ)) |>.trans fl
  have right : 10^18*x≤((k:ℚ)+1)^2 := fu.le.trans (by exact_mod_cast hi)
  have lr := (Rat.cast_le (K:=ℝ)).mpr left
  have rr := (Rat.cast_le (K:=ℝ)).mpr right
  push_cast at lr rr
  have xr : 0≤(x:ℝ) := by exact_mod_cast hx
  constructor
  · apply (le_sqrt (by unfold rootLow; push_cast; positivity) xr).mpr
    unfold rootLow; push_cast; dsimp only [k] at lr; linarith only [lr]
  · apply (sqrt_le_iff).mpr
    unfold rootHigh; push_cast; dsimp only [k] at rr
    exact ⟨by positivity,by linarith only [rr]⟩

theorem rootLow_pos {x : ℚ} (hx : 1/20≤x) : 0<rootLow x := by
  have fx : 1≤⌊10^18*x⌋₊ := (Nat.le_floor_iff (by linarith only [hx] : (0:ℚ)≤10^18*x)).mpr (by push_cast; linarith only [hx])
  have pos : 0<rootUnits x := Nat.sqrt_pos.mpr fx
  unfold rootLow; positivity

def roundUpper (x : ℚ) : ℚ := (⌈10^30*x⌉₊:ℚ)/10^30

theorem round_upper (x : ℚ) : x≤roundUpper x := by
  apply (le_div_iff₀ (by positivity)).mpr
  simpa only [mul_comm x] using Nat.le_ceil (10^30*x)

def latePart (i k : ℕ) : ℚ := max (1/20) (1-((k:ℚ)+1)/i)

def lateWeight (i k : ℕ) : ℚ :=
  let p := latePart i k
  (1/(i:ℚ)+1/150000)*(501/1000)/(p*rootLow p)

theorem late_weight_bound {N i : ℕ} (hn : 150000≤N) (ip : 0< i) (k : ℕ) :
    (1/(i:ℝ)+1/(N:ℝ))*((501/1000:ℝ)/(lateFraction i k*sqrt (lateFraction i k)))≤(lateWeight i k:ℝ) := by
  let p := latePart i k
  have hp : (1/20:ℚ)≤p := le_max_left ..
  have pr : lateFraction i k=(p:ℝ) := by simp [p,latePart,lateFraction]
  have rp := rootLow_pos hp
  have pr0 : 0<(p:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℚ)<1/20) hp)
  have rpr : 0<(rootLow p:ℝ) := by exact_mod_cast rp
  have root := (root_brackets (x:=p) (by exact_mod_cast pr0.le)).1
  have nr : (150000:ℝ)≤N := by exact_mod_cast hn
  have inv := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<150000) nr
  rw [pr,← mul_div_assoc]
  unfold lateWeight; push_cast
  change _≤(1/(i:ℝ)+1/150000)*(501/1000)/((p:ℝ)*(rootLow p:ℝ))
  apply div_le_div₀ (by positivity) (by gcongr) (mul_pos pr0 rpr) (mul_le_mul_of_nonneg_left root pr0.le)

end CentralUnimodality.PolynomialTrial
