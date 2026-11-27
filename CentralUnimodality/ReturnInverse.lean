module

public import CentralUnimodality.FirstReturn
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! Length generating series for the signed walk. The inverse of the bridge
series has coefficients given by the first-return law. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries

noncomputable def walkSeries {R : Type*} [CommSemiring R] (q : R) (χ : ℤ → R)
    (T : ℕ → Finset (List Bool)) : PowerSeries R :=
  PowerSeries.mk (fun n => q^n * ∑ w ∈ T n, χ (walkArea w))

theorem coeff_walkSeries {R : Type*} [CommSemiring R] (q : R) (χ : ℤ → R)
    (T : ℕ → Finset (List Bool)) (n : ℕ) :
    coeff n (walkSeries q χ T) = q^n * ∑ w ∈ T n, χ (walkArea w) := coeff_mk ..

theorem coeff_walkSeries_mul {R : Type*} [CommSemiring R] (q : R) (χ : ℤ → R)
    (A B : ℕ → Finset (List Bool)) (n : ℕ) :
    coeff n (walkSeries q χ A * walkSeries q χ B) =
      q^n * ∑ i ∈ Finset.range (n+1),
        (∑ u ∈ A i, χ (walkArea u)) * (∑ v ∈ B (n-i), χ (walkArea v)) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : i + (n-i) = n := by have := Finset.mem_range.mp hi; omega
  have hp : q^i * q^(n-i) = q^n := by rw [← pow_add, he]
  rw [coeff_walkSeries, coeff_walkSeries, ← hp]
  ac_rfl

theorem walkSeries_lastReturn {R : Type*} [CommSemiring R] (q : R) (χ : ℤ → R)
    (hχ : ∀ x y, χ (x+y) = χ x * χ y) :
    walkSeries q χ words = walkSeries q χ bridges * walkSeries q χ strictWords := by
  exact PowerSeries.ext fun n => by rw [coeff_walkSeries, coeff_walkSeries_mul, lastReturn_convolution χ hχ]

theorem walkSeries_firstReturn {R : Type*} [CommSemiring R] (q : R) (χ : ℤ → R)
    (h₀ : χ 0 = 1) (hχ : ∀ x y, χ (x+y) = χ x * χ y) :
    walkSeries q χ bridges = 1 + walkSeries q χ firstReturns * walkSeries q χ bridges := by
  apply PowerSeries.ext
  intro n
  rw [coeff_walkSeries, map_add, coeff_one, coeff_walkSeries_mul]
  cases n with
  | zero => have hB : bridges 0 = {[]} := by decide
            have hF : firstReturns 0 = ∅ := by decide
            simp [hB, hF, walkArea, heights, h₀]
  | succ n => simp only [Nat.succ_ne_zero, ite_false, zero_add]; rw [firstReturn_renewal χ hχ]

theorem walkSeries_bridge_inverse {R : Type*} [CommRing R] (q : R) (χ : ℤ → R)
    (h₀ : χ 0 = 1) (hχ : ∀ x y, χ (x+y) = χ x * χ y) :
    (1 - walkSeries q χ firstReturns) * walkSeries q χ bridges = 1 := by
  rw [sub_mul, one_mul, sub_eq_iff_eq_add]
  exact walkSeries_firstReturn q χ h₀ hχ

/-- Turn a residual of any proposed no-return series into its exact error. -/
theorem walkSeries_residual {R : Type*} [CommRing R] (q : R) (χ : ℤ → R)
    (h₀ : χ 0 = 1) (hχ : ∀ x y, χ (x+y) = χ x * χ y) (V : PowerSeries R) :
    walkSeries q χ strictWords - V = (1 - walkSeries q χ firstReturns) *
      (walkSeries q χ words - walkSeries q χ bridges * V) := by
  rw [walkSeries_lastReturn q χ hχ, ← mul_sub, ← mul_assoc, walkSeries_bridge_inverse q χ h₀ hχ, one_mul]

end CentralUnimodality
