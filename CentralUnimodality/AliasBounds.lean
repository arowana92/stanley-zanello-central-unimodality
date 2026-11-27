module

public import CentralUnimodality.FourierSites

/-! On a shorter Fourier grid, bound the extra congruence classes at a
central site by one copy of the upper corank tail. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries

def aliasWeight (Q k t b : ℕ) : ℕ :=
  (if (Q:ℤ) ∣ (t:ℤ)-k then 1 else 0) +
  (if (Q:ℤ) ∣ (k:ℤ)+t+b then 1 else 0)

private theorem alias_disjoint {Q k t b : ℕ} (hb : 0 < b) (hk : 2*k+b < Q)
    (hp : (Q:ℤ) ∣ (t:ℤ)-k) (hm : (Q:ℤ) ∣ (k:ℤ)+t+b) : False := by
  have hd := dvd_sub hm hp
  have ht : (k:ℤ)+t+b-(t-k) = 2*k+b := by ring
  rw [ht] at hd
  have he := Int.eq_zero_of_dvd_of_nonneg_of_lt (by positivity)
    (by exact_mod_cast hk : 2*(k:ℤ)+b < Q) hd
  omega

theorem alias_weight_bounds {Q k t b : ℕ} (hb : 0 < b) (hk : 2*k+b < Q) :
    (if k = t then 1 else 0) ≤ aliasWeight Q k t b ∧
    aliasWeight Q k t b ≤ (if k = t then 1 else 0) + (if Q ≤ k+t+b then 1 else 0) := by
  by_cases he : k = t
  · subst t
    simp only [aliasWeight,sub_self,dvd_zero,ite_true]
    have hc : ¬(Q:ℤ) ∣ (k:ℤ)+k+b := by
      intro hd
      exact alias_disjoint hb hk (t := k) (by simp) hd
    simp [hc]
  · simp only [ite_eq_right he,Nat.zero_le,true_and,zero_add]
    by_cases htail : Q ≤ k+t+b
    · rcases (by by_contra! h; exact alias_disjoint hb hk h.1 h.2 :
         ¬(Q:ℤ) ∣ (t:ℤ)-k ∨ ¬(Q:ℤ) ∣ (k:ℤ)+t+b) with h|h <;>
        simp [aliasWeight,htail,h] <;> split <;> decide
    · have h₁ : ¬(Q:ℤ) ∣ (t:ℤ)-k := by
        intro hp
        rcases le_total k t with h|h
        · have hd := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega : 0 ≤ (t:ℤ)-k) (by omega : (t:ℤ)-k < Q) hp
          omega
        · have hd := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega : 0 ≤ -((t:ℤ)-k))
            (by omega : -((t:ℤ)-k) < Q) (dvd_neg.mpr hp)
          omega
      have h₂ : ¬(Q:ℤ) ∣ (k:ℤ)+t+b := by
        intro hp
        have hd := Int.eq_zero_of_dvd_of_nonneg_of_lt (by positivity) (by omega : (k:ℤ)+t+b < Q) hp
        omega
      simp [aliasWeight,htail,h₁,h₂]

def periodicCount (n δ Q j : ℕ) : ℕ :=
  let D := n*(n+δ)
  ∑ l ∈ Finset.range (D+1), rankCount (2*n+δ) l * aliasWeight Q (D-j) (D-l) (3*n+2*δ+1)

theorem inverse_periodicCount (n δ : ℕ) (hδ : δ ≤ 1) {Q : ℕ} (hQ : 0 < Q)
    {j : ℕ} (hj : j ≤ n*(n+δ)) :
    siteInverse Q (signedAreaAtRank n δ j) (fun r =>
      coeff (2*n+δ+1) (fairSeries (areaCharacter (halfGrid Q r)) strictWords)) =
      (2:ℂ)⁻¹^(2*n+δ+1)*(periodicCount n δ Q j:ℂ) := by
  rw [siteInverse,periodized_ranks n δ hδ hQ]
  congr 1
  simp only [periodicCount,Nat.cast_sum,Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro l hl
  have hl' := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
  have hpos : ((n*(n+δ)-l:ℕ):ℤ)-(n*(n+δ)-j:ℕ) = (j:ℤ)-l := by
    rw [Nat.cast_sub hl',Nat.cast_sub hj]; ring
  have hneg : -(((n*(n+δ)-j:ℕ):ℤ)+(n*(n+δ)-l:ℕ)+(3*n+2*δ+1:ℕ)) =
        (j:ℤ)+l-signedAreaAtRank n δ 0 := by
    rw [Nat.cast_sub hj,Nat.cast_sub hl']
    simp only [signedAreaAtRank,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,Nat.cast_zero]
    ring
  simp only [aliasWeight,Nat.cast_add,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,hpos,← hneg,dvd_neg]

theorem periodicCount_bounds {n δ Q j : ℕ} (hj : j ≤ n*(n+δ))
    (hc : 2*(n*(n+δ)-j)+(3*n+2*δ+1) < Q) :
    rankCount (2*n+δ) j ≤ periodicCount n δ Q j ∧
    periodicCount n δ Q j ≤ rankCount (2*n+δ) j +
      ∑ l ∈ Finset.range (n*(n+δ)+1),
        if Q ≤ (n*(n+δ)-j)+(n*(n+δ)-l)+(3*n+2*δ+1) then rankCount (2*n+δ) l else 0 := by
  let D := n*(n+δ)
  let f := rankCount (2*n+δ)
  have he : (∑ l ∈ Finset.range (D+1), f l * (if D-j = D-l then 1 else 0)) = f j := by
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr (by omega))]
    · simp
    · intro l hl hne
      have := Finset.mem_range.mp hl
      simp [show D-j ≠ D-l by omega]
  unfold periodicCount
  constructor
  · change f j ≤ _
    rw [← he]
    exact Finset.sum_le_sum fun l _ => Nat.mul_le_mul_left _ (alias_weight_bounds (t := D-l) (by omega) hc).1
  · change _ ≤ f j+_
    rw [← he,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro l _
    have h := Nat.mul_le_mul_left (f l) (alias_weight_bounds (t := D-l) (by omega) hc).2
    simpa only [f,D,Nat.mul_add,mul_ite,mul_one,mul_zero] using h

end CentralUnimodality
