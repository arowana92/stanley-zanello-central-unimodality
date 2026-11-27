module

public import CentralUnimodality.EulerBase
public import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Coefficient extraction from integer powers of the formal Catalan square
root. The explicit ratio is relative to the middle binomial coefficient. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries

noncomputable def rootUnit : (PowerSeries ℚ)ˣ :=
  ⟨catalanRoot, ballotBase, catalanRoot_mul_ballotBase,
    (mul_comm ..).trans catalanRoot_mul_ballotBase⟩

noncomputable def rootPower (h : ℤ) : PowerSeries ℚ := ↑(rootUnit^h)

theorem rootPower_add (h k : ℤ) : rootPower (h+k) = rootPower h * rootPower k := by
  simp [rootPower, zpow_add]

theorem rootPower_zero : rootPower 0 = 1 := by simp [rootPower]
theorem rootPower_one : rootPower 1 = catalanRoot := by simp [rootPower, rootUnit]
theorem rootPower_neg_one : rootPower (-1) = ballotBase := by simp [rootPower, rootUnit]

private def SatisfiesEuler (h : ℤ) (f : PowerSeries ℚ) : Prop :=
  (1-4*X)*(2*sizeEuler f) = -4*(h:PowerSeries ℚ)*X*f

private theorem euler_product {h k : ℤ} {f g : PowerSeries ℚ}
    (hf : SatisfiesEuler h f) (hg : SatisfiesEuler k g) : SatisfiesEuler (h+k) (f*g) := by
  unfold SatisfiesEuler at *
  rw [sizeEuler_mul, Int.cast_add]
  linear_combination g*hf + f*hg

private theorem euler_root : SatisfiesEuler 1 catalanRoot := by
  unfold SatisfiesEuler
  rw [Int.cast_one, sizeEuler_root]
  have h : (1-4*X)*ballotBase = catalanRoot := by
    rw [← catalanRoot_sq, pow_two, mul_assoc, catalanRoot_mul_ballotBase, mul_one]
  linear_combination -h

private theorem euler_inverse : SatisfiesEuler (-1) ballotBase := by
  unfold SatisfiesEuler
  rw [Int.cast_neg, Int.cast_one, sizeEuler_ballotBase]
  have h : (1-4*X)*ballotBase^2 = 1 := by
    rw [← catalanRoot_sq, ← mul_pow, catalanRoot_mul_ballotBase, one_pow]
  linear_combination ballotBase*h

private theorem euler_power_nat {f : PowerSeries ℚ} {h : ℤ} (hf : SatisfiesEuler h f) (n : ℕ) :
    SatisfiesEuler (n*h) (f^n) := by
  induction n with
  | zero => simp [SatisfiesEuler, show sizeEuler 1 = 0 from sizeEuler_nat 1]
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact euler_product ih hf

private theorem euler_rootPower (h : ℤ) : SatisfiesEuler h (rootPower h) := by
  cases h with
  | ofNat n =>
    simpa [rootPower, rootUnit] using euler_power_nat euler_root n
  | negSucc n =>
    rw [rootPower, zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    change SatisfiesEuler (Int.negSucc n) (ballotBase^(n+1))
    rw [show Int.negSucc n = ((n+1:ℕ):ℤ)*(-1) by omega]
    exact euler_power_nat euler_inverse (n+1)

theorem rootPower_shift_two (h : ℤ) : (1-4*X)*rootPower (h-2) = rootPower h := by
  rw [← catalanRoot_sq, ← rootPower_one, pow_two, ← rootPower_add, ← rootPower_add]
  congr 1
  omega

/-- Twice the Euler derivative on the v-coordinate is
h times the difference of the monomials at exponents h and h-2. -/
theorem sizeEuler_rootPower (h : ℤ) :
    2*sizeEuler (rootPower h) = (h:PowerSeries ℚ)*(rootPower h-rootPower (h-2)) := by
  have hr : (1-4*X:PowerSeries ℚ) ≠ 0 := by
    intro h
    have e := congrArg constantCoeff h
    simp at e
  apply mul_left_cancel₀ hr
  have hd := euler_rootPower h
  unfold SatisfiesEuler at hd
  linear_combination hd + (h:PowerSeries ℚ)*rootPower_shift_two h

theorem rootPower_coeff_step (h : ℤ) (n : ℕ) :
    ((n:ℚ)+1)*coeff (n+1) (rootPower h) = (4*n-2*h)*coeff n (rootPower h) := by
  let f := rootPower h
  have he : (1-4*X)*(2*sizeEuler f) = -4*(h:PowerSeries ℚ)*X*f := euler_rootPower h
  have h' : C (2:ℚ)*sizeEuler f - C (8:ℚ)*(X*sizeEuler f) = C (-4*(h:ℚ))*(X*f) := by
    rw [map_mul]
    simp only [map_neg, map_ofNat, map_intCast]
    linear_combination he
  have hc := congrArg (coeff (n+1)) h'
  simp only [map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_sizeEuler, Nat.cast_succ] at hc
  change ((n:ℚ)+1)*coeff (n+1) f = (4*n-2*h)*coeff n f
  linarith only [hc]

def rootRatio (h : ℤ) : ℕ → ℚ
  | 0 => 1
  | n+1 => rootRatio h n * ((2*(n:ℚ)-h)/(2*n+1))

theorem rootPower_coeff_zero (h : ℤ) : coeff 0 (rootPower h) = 1 := by
  have hv : constantCoeff catalanRoot = 1 := by simp [catalanRoot]
  have hb : constantCoeff ballotBase = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_ballotBase]
    norm_num
  cases h with
  | ofNat n => simp [rootPower, rootUnit, coeff_zero_eq_constantCoeff_apply, hv]
  | negSucc n =>
    rw [rootPower, zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val, coeff_zero_eq_constantCoeff_apply, map_pow]
    change constantCoeff ballotBase ^ (n+1) = 1
    rw [hb, one_pow]

theorem rootPower_coeff (h : ℤ) (n : ℕ) :
    coeff n (rootPower h) = (n.centralBinom : ℚ)*rootRatio h n := by
  induction n with
  | zero => simp [rootRatio,rootPower_coeff_zero]
  | succ n ih =>
    have hc := rootPower_coeff_step h n
    rw [ih] at hc
    have hb : ((n:ℚ)+1)*(n+1).centralBinom = 2*(2*(n:ℚ)+1)*n.centralBinom := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    rw [rootRatio]
    field_simp
    apply (mul_left_cancel₀ (by positivity : (n:ℚ)+1 ≠ 0))
    linear_combination (2*(n:ℚ)+1)*hc - rootRatio h n*(2*(n:ℚ)-h)*hb

end CentralUnimodality
