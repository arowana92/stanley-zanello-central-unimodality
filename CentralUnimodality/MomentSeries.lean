module

public import CentralUnimodality.Stump
public import Mathlib.RingTheory.PowerSeries.Exp

/-! Generate the exact corank moments by substituting the formal exponential
for the area variable. Columns are series in the size variable z, with fixed
moment order in the inner variable x. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries

abbrev MomentBiseries := PowerSeries (PowerSeries ℚ)

noncomputable def momentColumn (r : ℕ) (F : MomentBiseries) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => coeff r (coeff n F))

theorem coeff_momentColumn (r n : ℕ) (F : MomentBiseries) :
    coeff n (momentColumn r F) = coeff r (coeff n F) := coeff_mk ..

theorem coeff_exp_power (r k : ℕ) : coeff r ((exp ℚ)^k) = (k:ℚ)^r / r.factorial := by
  rw [exp_pow_eq_rescale_exp, coeff_rescale, coeff_exp]
  simp [div_eq_mul_inv]

def rankMoment (n δ r : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n*(n+δ)+1), rankCount (2*n+δ) j * (n*(n+δ)-j)^r

theorem exp_ballot_moment (n δ r : ℕ) (hδ : δ ≤ 1) :
    coeff r (corankSum (exp ℚ) (ballots (2*n+δ))) = (rankMoment n δ r : ℚ) / r.factorial := by
  rw [ballot_rank_polynomial _ n δ hδ, map_sum]
  simp only [rankMoment, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_nsmul (coeff (R := ℚ) r) (rankCount (2*n+δ) j) ((exp ℚ)^(n*(n+δ)-j)),
    coeff_exp_power, nsmul_eq_mul, div_eq_mul_inv, mul_assoc]

theorem even_momentColumn (n r : ℕ) :
    coeff n (momentColumn r (evenBallotSeries (exp ℚ))) = (rankMoment n 0 r : ℚ) / r.factorial := by
  simpa only [coeff_momentColumn, evenBallotSeries, coeff_mk, Nat.add_zero] using
    exp_ballot_moment n 0 r (by decide)

theorem odd_momentColumn (n r : ℕ) :
    coeff n (momentColumn r (oddBallotSeries (exp ℚ))) = (rankMoment n 1 r : ℚ) / r.factorial := by
  simpa only [coeff_momentColumn, oddBallotSeries, coeff_mk] using exp_ballot_moment n 1 r (by decide)

private theorem coeff_prod_range {R : Type*} [CommSemiring R] (F G : PowerSeries R) (n : ℕ) :
    coeff n (F*G) = ∑ i ∈ Finset.range (n+1), coeff i F * coeff (n-i) G := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem momentColumn_mul (r : ℕ) (F G : MomentBiseries) :
    momentColumn r (F*G) = ∑ i ∈ Finset.range (r+1), momentColumn i F * momentColumn (r-i) G := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_momentColumn, coeff_prod_range, map_sum]
  exact Finset.sum_comm

/-- At coefficient n this is multiplication by (d*n)^j/j!, the divided
Euler derivative for the substitution z ↦ exp(d*x) z. -/
noncomputable def dividedEuler (d j : ℕ) (P : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => ((d*n : ℕ):ℚ)^j / j.factorial * coeff n P)

theorem momentColumn_rescale (d r : ℕ) (F : MomentBiseries) :
    momentColumn r (rescale ((exp ℚ)^d) F) =
      ∑ j ∈ Finset.range (r+1), dividedEuler d j (momentColumn (r-j) F) := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_momentColumn, coeff_rescale, ← pow_mul, coeff_prod_range, coeff_exp_power,
    map_sum, dividedEuler, coeff_mk]

end CentralUnimodality
