module

public import CentralUnimodality.IntervalProduct
public import Mathlib.Algebra.Polynomial.BigOperators

/-! Support bounds for the two factors in the staircase convolutions. -/
@[expose] public section

namespace CentralUnimodality

open Polynomial

theorem twice_choose_two (n : ℕ) : 2*n.choose 2 + n = n*n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.choose_succ_succ,Nat.choose_one_right]
    nlinarith only [ih]

theorem dyck_degree_le (n : ℕ) : (dyckPoly n).natDegree ≤ n.choose 2 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero =>
      have h : dyckPoly 0 = 1 := by
        rw [dyckPoly,show dycks 0 = {[]} by decide,corankSum,Finset.sum_singleton]
        rfl
      simp [h]
    | succ n =>
      have he := dyck_convolution (X:Polynomial ℕ) n
      change dyckPoly (n+1) = ∑ i ∈ Finset.range (n+1),
        dyckPoly i * (X^(n-i)*dyckPoly (n-i)) at he
      rw [he]
      apply (natDegree_sum_le ..).trans
      apply Finset.sup_le
      intro i hi
      have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
      have ha := ih i (by omega)
      have hb := ih (n-i) (by omega)
      apply (natDegree_mul_le ..).trans
      apply (Nat.add_le_add ha (natDegree_mul_le ..)).trans
      rw [natDegree_X_pow]
      have hsum : (n-i)+i=n := by omega
      have hfinal := twice_choose_two (n+1)
      conv at hfinal => rhs; rw [← hsum]
      nlinarith only [hsum,hb,twice_choose_two i,twice_choose_two (n-i),hfinal, Nat.zero_le ((n-i)*i)]

theorem ballot_degree_le (n δ : ℕ) (hδ : δ ≤ 1) : (ballotPoly (2*n+δ)).natDegree ≤ n*(n+δ) := by
  rw [ballotPoly,ballot_rank_polynomial _ n δ hδ]
  apply (natDegree_sum_le ..).trans
  apply Finset.sup_le
  intro i _
  exact (natDegree_smul_le ..).trans ((natDegree_X_pow_le _).trans (Nat.sub_le ..))

end CentralUnimodality
