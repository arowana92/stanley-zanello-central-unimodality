module

public import CentralUnimodality.DyckRecurrence
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! Eliminate the odd-length ballot series to recover Stump's type B area
recurrence. All identities hold with q an indeterminate. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries

variable {R : Type*} [CommSemiring R]

noncomputable def dyckSeries (q : R) : PowerSeries R :=
  PowerSeries.mk (fun n => corankSum q (dycks n))

noncomputable def evenBallotSeries (q : R) : PowerSeries R :=
  PowerSeries.mk (fun n => corankSum q (ballots (2*n)))

noncomputable def oddBallotSeries (q : R) : PowerSeries R :=
  PowerSeries.mk (fun n => corankSum q (ballots (2*n+1)))

private noncomputable def dyckTail (q : R) : PowerSeries R :=
  PowerSeries.mk (fun n => corankSum q (dycks (n+1)))

private theorem coeff_product (A B : PowerSeries R) (n : ℕ) :
    coeff n (A*B) = ∑ i ∈ Finset.range (n+1), coeff i A * coeff (n-i) B := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

private theorem dyckTail_eq (q : R) :
    dyckTail q = dyckSeries q * rescale q (dyckSeries q) := by
  apply PowerSeries.ext
  intro n
  simpa only [coeff_product, coeff_rescale, dyckTail, dyckSeries, coeff_mk] using dyck_convolution q n

theorem oddBallotSeries_eq (q : R) :
    oddBallotSeries q = dyckSeries q * rescale q (evenBallotSeries q) := by
  apply PowerSeries.ext
  intro n
  simpa only [coeff_product, coeff_rescale, oddBallotSeries, dyckSeries, evenBallotSeries, coeff_mk]
    using odd_ballot_convolution q n

theorem evenBallotSeries_eq (q : R) : evenBallotSeries q = dyckSeries q +
    X * (C q * (dyckSeries q * rescale q (oddBallotSeries q))) := by
  apply PowerSeries.ext
  intro n
  rw [map_add]
  cases n with
  | zero =>
    have hd : dycks 0 = {[]} := by decide
    have hb : ballots 0 = {[]} := by decide
    simp [evenBallotSeries, dyckSeries, hb, hd]
  | succ n =>
    rw [coeff_succ_X_mul, coeff_C_mul, coeff_product, Finset.mul_sum]
    simp only [evenBallotSeries, dyckSeries, oddBallotSeries, coeff_rescale, coeff_mk]
    rw [even_ballot_convolution]
    apply congrArg (_ + ·)
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]
    ac_rfl

/-- The odd-part staircase polynomial of size n+1 is expressed using only
smaller odd-part staircase polynomials and ordinary Dyck polynomials. -/
theorem stump_convolution (q : R) (n : ℕ) :
    corankSum q (ballots (2*(n+1))) = corankSum q (dycks (n+1)) +
      ∑ i ∈ Finset.range (n+1), corankSum q (dycks (i+1)) *
        (q^(2*(n-i)+1) * corankSum q (ballots (2*(n-i)))) := by
  have h := evenBallotSeries_eq q
  rw [oddBallotSeries_eq, map_mul, rescale_rescale, ← mul_assoc (dyckSeries q), ← dyckTail_eq] at h
  have hc := congrArg (coeff (n+1)) h
  rw [map_add, coeff_succ_X_mul, coeff_C_mul, coeff_product, Finset.mul_sum] at hc
  simp only [coeff_rescale, dyckSeries, dyckTail, evenBallotSeries, coeff_mk] at hc
  rw [hc]
  apply congrArg (_ + ·)
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ, pow_mul, ← pow_two]
  ac_rfl

end CentralUnimodality
