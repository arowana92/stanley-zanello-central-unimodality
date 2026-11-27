module

public import CentralUnimodality.Stump
public import CentralUnimodality.Survival
import Mathlib.Tactic.LinearCombination

/-! At q = 1 the Dyck and even-length meander series give both branches
needed for the moment recursion. All square roots are formal series with
specified constant coefficient. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries

theorem dyckSeries_eq {R : Type*} [CommSemiring R] (q : R) :
    dyckSeries q = 1 + X * (dyckSeries q * rescale q (dyckSeries q)) := by
  apply PowerSeries.ext
  intro n
  rw [map_add]
  cases n with
  | zero =>
    have h : dycks 0 = {[]} := by decide
    simp [dyckSeries, h, corankSum, walkCorank, staircaseDegree, wordParts]
  | succ n =>
    rw [coeff_one, ite_eq_right n.succ_ne_zero, zero_add, coeff_succ_X_mul, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simpa only [dyckSeries, coeff_mk, coeff_rescale] using dyck_convolution q n

noncomputable abbrev dyckBase : PowerSeries ℚ := dyckSeries (1:ℚ)
noncomputable abbrev ballotBase : PowerSeries ℚ := evenBallotSeries (1:ℚ)
noncomputable def catalanRoot : PowerSeries ℚ := 1-2*X*dyckBase

theorem dyckBase_eq : dyckBase = 1 + X * dyckBase^2 := by
  simpa only [rescale_one, RingHom.id_apply, pow_two] using dyckSeries_eq (1:ℚ)

theorem coeff_ballotBase (n : ℕ) : coeff n ballotBase = ((2*n).choose n : ℚ) := by
  have h := ballot_rank_polynomial (1:ℚ) n 0 (by decide)
  have hs := sum_rankCount n 0 (by decide)
  simp only [Nat.add_zero] at hs
  simpa [evenBallotSeries, ballotBase, ← Nat.cast_sum, hs] using h

theorem catalanRoot_sq : catalanRoot^2 = 1-4*X := by
  unfold catalanRoot
  linear_combination -4*X*dyckBase_eq

theorem dyckBase_mul_root : dyckBase*catalanRoot = 2-dyckBase := by
  unfold catalanRoot
  linear_combination 2*dyckBase_eq

theorem catalanRoot_mul_ballotBase : catalanRoot * ballotBase = 1 := by
  let D := dyckBase
  let B := ballotBase
  have hd : D = 1+X*D^2 := dyckBase_eq
  have hodd := oddBallotSeries_eq (1:ℚ)
  have hb := evenBallotSeries_eq (1:ℚ)
  rw [hodd] at hb
  simp only [map_one, rescale_one, RingHom.id_apply, one_mul] at hb
  change B = D + X*(D*(D*B)) at hb
  have he : (2-D)*B = D := by linear_combination hb - B*hd
  have hu : D*(1-X*D) = 1 := by linear_combination hd
  have hroot : D*catalanRoot = 2-D := dyckBase_mul_root
  calc
    _ = (1-X*D)*(D*catalanRoot)*B := by rw [← mul_assoc, mul_comm (1-X*D) D, hu, one_mul]
    _ = (1-X*D)*D := by rw [hroot, mul_assoc, he]
    _ = 1 := (mul_comm ..).trans hu

end CentralUnimodality
