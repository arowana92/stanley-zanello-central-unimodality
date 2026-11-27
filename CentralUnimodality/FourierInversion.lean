module

public import CentralUnimodality.FourierInputs
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-! Exact periodized inversion at a staircase site. The two terms are
the congruence classes of the positive and reflected half-area sites.
Their differences are integers even on the half-integral lattice. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries

noncomputable def halfGrid (Q r : ℕ) : ℝ := Real.pi*r/Q

private theorem grid_orthogonality {Q : ℕ} (hQ : 0 < Q) (z : ℤ) :
    ∑ r ∈ Finset.range Q, areaCharacter (halfGrid Q r) (2*z) =
      if (Q:ℤ) ∣ z then (Q:ℂ) else 0 := by
  let v := Complex.exp (2*(Real.pi:ℂ)*Complex.I/Q)
  have hv : IsPrimitiveRoot v Q := Complex.isPrimitiveRoot_exp Q hQ.ne'
  have hn : v ≠ 0 := Complex.exp_ne_zero _
  have he (r : ℕ) : areaCharacter (halfGrid Q r) (2*z) = (v^z)^r := by
    rw [areaCharacter,halfGrid,show v = _ from rfl,← Complex.exp_int_mul,← Complex.exp_nat_mul]
    push_cast
    congr 1
    ring
  simp_rw [he]
  by_cases hd : (Q:ℤ) ∣ z
  · simp [hd,(hv.zpow_eq_one_iff_dvd z).mpr hd]
  · rw [ite_eq_right hd]
    have hz : v^z ≠ 1 := fun h => hd ((hv.zpow_eq_one_iff_dvd z).mp h)
    apply eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero_of_ne hz)
    rw [mul_comm,geom_sum_mul]
    have hq : (v^z)^Q = 1 := by
      rw [← zpow_natCast,← zpow_mul,Int.mul_comm,zpow_mul, zpow_natCast,hv.pow_eq_one,one_zpow]
    rw [hq,sub_self]

/-- The normalization is fair-walk mass. Divide by the survival probability
to obtain the conditional characteristic function used in the window proof. -/
theorem periodized_ranks (n δ : ℕ) (hδ : δ ≤ 1) {Q : ℕ} (hQ : 0 < Q) (j : ℕ) :
    (∑ r ∈ Finset.range Q,
      areaCharacter (halfGrid Q r) (-signedAreaAtRank n δ j) *
      coeff (2*n+δ+1) (fairSeries (areaCharacter (halfGrid Q r)) strictWords)) / Q =
      (2:ℂ)⁻¹^(2*n+δ+1) * ∑ l ∈ Finset.range (n*(n+δ)+1), (rankCount (2*n+δ) l:ℂ) *
        ((if (Q:ℤ) ∣ (j:ℤ)-l then 1 else 0) +
         (if (Q:ℤ) ∣ (j:ℤ)+l-signedAreaAtRank n δ 0 then 1 else 0)) := by
  let A := signedAreaAtRank n δ
  let W (r : ℕ) := areaCharacter (halfGrid Q r)
  let L := 2*n+δ+1
  let D := n*(n+δ)
  let w := (2:ℂ)⁻¹^L
  have splitR (r : ℕ) :
      W r (-A j)*coeff L (fairSeries (W r) strictWords) =
        ∑ l ∈ Finset.range (D+1), (w*(rankCount (2*n+δ) l:ℂ))*
          (W r (2*((j:ℤ)-l))+W r (2*((j:ℤ)+l-A 0))) := by
    rw [coeff_walkSeries,signed_ranks (W r) n δ hδ]
    simp only [Finset.mul_sum,nsmul_eq_mul]
    apply Finset.sum_congr rfl
    intro l _
    have h₁ : -A j+A l = 2*((j:ℤ)-l) := by dsimp [A,signedAreaAtRank]; ring
    have h₂ : -A j+ -A l = 2*((j:ℤ)+l-A 0) := by dsimp [A,signedAreaAtRank]; ring
    rw [← h₁,← h₂]
    change _ = _*(areaCharacter _ _ + areaCharacter _ _)
    rw [areaCharacter_add,areaCharacter_add]
    dsimp [w,W]
    ring
  change (∑ r ∈ Finset.range Q, W r (-A j)*coeff L (fairSeries (W r) strictWords))/Q = _
  simp_rw [splitR]
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_mul,← Finset.mul_sum,Finset.sum_add_distrib]
  change (w*_) * ((∑ r ∈ Finset.range Q, areaCharacter _ _) + (∑ r ∈ Finset.range Q, areaCharacter _ _)) * _ = _
  rw [grid_orthogonality hQ,grid_orthogonality hQ]
  by_cases h₁ : (Q:ℤ) ∣ (j:ℤ)-l <;>
    by_cases h₂ : (Q:ℤ) ∣ (j:ℤ)+l-A 0 <;>
    simp [h₁,h₂,A,w,L,Nat.cast_ne_zero.mpr hQ.ne']
  field_simp [show (Q:ℂ) ≠ 0 by exact_mod_cast hQ.ne']

end CentralUnimodality
