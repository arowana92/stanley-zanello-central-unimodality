module

public import CentralUnimodality.DyckDegrees
public import CentralUnimodality.OddMean
public import CentralUnimodality.PrefixInduction

/-! Right-flank induction from smaller odd-part rows. Beyond the degree
of a Dyck factor plus the shift and a peak of its ballot factor, every
term of the coefficient convolution is nonincreasing. -/
@[expose] public section

namespace CentralUnimodality

open Polynomial

theorem product_decreasing_after {P Q : Polynomial ℕ} {q s p k : ℕ} (hd : Q.natDegree ≤ q)
    (hp : ∀ i ≥ p, P.coeff (i+1) ≤ P.coeff i) (hk : s+p+q ≤ k) :
    (Q*(X^s*P)).coeff (k+1) ≤ (Q*(X^s*P)).coeff k := by
  simp only [coeff_mul (p := Q),Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_range_succ _ (k+1),coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < k+1),zero_mul,add_zero]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ≤ q
  · apply Nat.mul_le_mul_left
    rw [coeff_X_pow_mul',coeff_X_pow_mul',ite_eq_left (by omega),ite_eq_left (by omega),
      show k+1-i-s = (k-i-s)+1 by omega]
    exact hp _ (by omega)
  · simp [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd (by omega : q < i))]

private theorem odd_poly_peak (h : ℕ) (hu : UnimodalOn (rankCount (2*h)) 0 (h*h)) :
    ∃ p ≤ h*h, (49 ≤ h → 2*p+4*h+2 ≤ h*h) ∧
      ∀ k ≥ p, (ballotPoly (2*h)).coeff (k+1) ≤ (ballotPoly (2*h)).coeff k := by
  obtain ⟨p,_,hp,hinc,hdec⟩ := hu.reverse
  refine ⟨p,hp,fun hn => odd_prefix_peak_bound hn hp (fun k hk => hinc k (Nat.zero_le _) hk),?_⟩
  intro k hk
  have he (i : ℕ) (hi : i ≤ h*h) : (ballotPoly (2*h)).coeff i = rankCount (2*h) (h*h-i) := by
    simpa only [Nat.add_zero] using ballotPoly_coeff h 0 i (by decide) (by simpa using hi)
  by_cases htop : k < h*h
  · rw [he _ (by omega),he _ htop.le]
    exact hdec _ hk htop
  · have hd : (ballotPoly (2*h)).natDegree ≤ h*h := by simpa only [Nat.add_zero] using ballot_degree_le h 0 (by decide)
    rw [coeff_eq_zero_of_natDegree_lt (by omega : (ballotPoly (2*h)).natDegree < k+1)]
    exact Nat.zero_le _

private theorem midpoint_offset {h l p s : ℕ} (hn : 96 ≤ h+l) (hp : p ≤ h*h)
    (hpeak : 49 ≤ h → 2*p+4*h+2 ≤ h*h) (hs : s ≤ 2*h+1) :
    2*(s+p+l.choose 2) ≤ (h+l)*(h+l) := by
  have ht := twice_choose_two l
  by_cases hh : 49 ≤ h
  · nlinarith only [ht,hpeak hh,hs,Nat.zero_le (h*l),Nat.zero_le l]
  · have h48 : 48 ≤ l := by omega
    have hhl : h ≤ l := by omega
    have h₁ := Nat.mul_le_mul_left h hhl
    have h₂ := Nat.mul_le_mul_left h h48
    nlinarith only [ht,hs,hp,h₁,h₂,h48]

private theorem summand_tail {h l s k : ℕ} (hn : 96 ≤ h+l) (hs : s ≤ 2*h+1)
    (hu : UnimodalOn (rankCount (2*h)) 0 (h*h)) (hk : (h+l)*(h+l)/2 ≤ k) :
    (dyckPoly l * (X^s*ballotPoly (2*h))).coeff (k+1) ≤
      (dyckPoly l * (X^s*ballotPoly (2*h))).coeff k := by
  obtain ⟨p,hp,he,hd⟩ := odd_poly_peak h hu
  have hmin := midpoint_offset hn hp he hs
  apply product_decreasing_after (dyck_degree_le l) hd
  omega

theorem odd_midpoint_tail {n k : ℕ} (hn : 96 ≤ n+1) (hk : (n+1)*(n+1)/2 ≤ k)
    (hu : ∀ h ≤ n, UnimodalOn (rankCount (2*h)) 0 (h*h)) :
    (ballotPoly (2*(n+1))).coeff (k+1) ≤ (ballotPoly (2*(n+1))).coeff k := by
  have he := stump_convolution (X:Polynomial ℕ) n
  change ballotPoly (2*(n+1)) = dyckPoly (n+1) + ∑ i ∈ Finset.range (n+1),
    dyckPoly (i+1) * (X^(2*(n-i)+1)*ballotPoly (2*(n-i))) at he
  simp only [he,coeff_add,finsetSum_coeff]
  apply add_le_add
  · have ht := twice_choose_two (n+1)
    rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (dyck_degree_le _) (by omega : (n+1).choose 2 < k+1))]
    exact Nat.zero_le _
  · apply Finset.sum_le_sum
    intro i hi
    have hsum : n-i+(i+1) = n+1 := by have := Finset.mem_range.mp hi; omega
    exact summand_tail (hsum ▸ hn) (le_refl _) (hu _ (Nat.sub_le ..)) (hsum ▸ hk)

theorem even_midpoint_tail {n k : ℕ} (hn : 96 ≤ n) (hk : n*n/2 ≤ k)
    (hu : ∀ h ≤ n, UnimodalOn (rankCount (2*h)) 0 (h*h)) :
    (ballotPoly (2*n+1)).coeff (k+1) ≤ (ballotPoly (2*n+1)).coeff k := by
  have he := odd_ballot_convolution (X:Polynomial ℕ) n
  change ballotPoly (2*n+1) = ∑ i ∈ Finset.range (n+1),
    dyckPoly i * (X^(n-i)*ballotPoly (2*(n-i))) at he
  simp only [he,finsetSum_coeff]
  apply Finset.sum_le_sum
  intro i hi
  have hsum : n-i+i = n := by have := Finset.mem_range.mp hi; omega
  exact summand_tail (by rwa [hsum]) (by omega) (hu _ (Nat.sub_le ..)) (by rwa [hsum])

end CentralUnimodality
