module

public import CentralUnimodality.ModeMean
public import CentralUnimodality.AliasTail
public import CentralUnimodality.RatioPolynomials

/-! The first moment confines the peak of any unimodal odd-part row well
before its midpoint. This estimate only uses weak increase up to that peak. -/
@[expose] public section

namespace CentralUnimodality

theorem odd_first_moment (n : ℕ) :
    4*rankMoment n 0 1 + (6*n+2)*n.centralBinom = (3*n+2)*4^n := by
  have h := Laurent.exact_even_moment n 1
  have ht : Laurent.evenNumerator (Laurent.lookup (Laurent.tables 1).2 1) =
      [(-4,3/4),(-3,-3/4),(-2,-1/4),(-1,1/4)] := by decide +kernel
  rw [ht] at h
  have h₁ := rootRatio_lower_two (-1) n
  have h₂ := rootRatio_lower_two (-2) n
  norm_num only [Int.reduceSub,Int.cast_neg,Int.cast_one,Int.cast_ofNat,rootRatio_neg_one,mul_one] at h₁ h₂
  norm_num only [Laurent.ratioSum,Nat.factorial_one,Nat.cast_one,one_mul,rootRatio_neg_one,mul_one,add_zero] at h
  have hs := rootRatio_neg_two n
  exact_mod_cast (show 4*(rankMoment n 0 1:ℚ)+(6*n+2)*(n.centralBinom:ℚ) = (3*n+2)*(4:ℚ)^n by
    linear_combination 4*h - (3*n.centralBinom:ℚ)/2*h₂ + (3*n.centralBinom:ℚ)*h₁ + (3*n+2:ℚ)*hs)

private theorem odd_reflect_sum (n : ℕ) (f : ℕ → ℕ) :
    (∑ k ∈ Finset.range (n*n+1), f (n*n-k)) = ∑ k ∈ Finset.range (n*n+1), f k := by
  simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect f (n*n+1)

theorem odd_prefix_peak_bound {n p : ℕ} (hn : 49 ≤ n) (hp : p ≤ n*n)
    (hu : ∀ k < p, rankCount (2*n) (n*n-k) ≤ rankCount (2*n) (n*n-(k+1))) :
    2*p+4*n+2 ≤ n*n := by
  have h := prefix_mean_bound (fun k => rankCount (2*n) (n*n-k)) hp hu
  have hm := odd_reflect_sum n (fun k => rankCount (2*n) k * (n*n-k))
  have he : (∑ k ∈ Finset.range (n*n+1), k*rankCount (2*n) (n*n-k)) = rankMoment n 0 1 := by
    simpa only [rankMoment,Nat.add_zero,pow_one,← hm] using (show
      (∑ k ∈ Finset.range (n*n+1), k*rankCount (2*n) (n*n-k)) =
        ∑ k ∈ Finset.range (n*n+1), rankCount (2*n) (n*n-k)*(n*n-(n*n-k)) by
      apply Finset.sum_congr rfl
      intro k hk
      have := Finset.mem_range.mp hk
      rw [show n*n-(n*n-k) = k by omega,mul_comm])
  rw [odd_reflect_sum,he] at h
  have hmass := sum_rankCount n 0 (by decide)
  simp only [Nat.add_zero] at hmass
  rw [hmass] at h
  let C : ℝ := n.centralBinom
  have hC : 0 < C := by dsimp [C]; exact_mod_cast Nat.centralBinom_pos n
  have hsurv := survival_inv_le (N := n) (by omega)
  rw [survival,inv_div] at hsurv
  have hroot : Real.sqrt n ≤ (n:ℝ)/7 := by
    apply Real.sqrt_le_iff.mpr
    have hh : (49:ℝ) ≤ n := by exact_mod_cast hn
    exact ⟨by positivity,by nlinarith only [mul_nonneg (sub_nonneg.mpr hh) (Nat.cast_nonneg (α := ℝ) n)]⟩
  have hpow : (4:ℝ)^n ≤ 2*((n:ℝ)/7)*C := (div_le_iff₀ hC).mp (hsurv.trans (by linarith only [hroot]))
  have hmom : 4*(rankMoment n 0 1:ℝ)+(6*n+2)*C = (3*n+2)*(4:ℝ)^n := by dsimp [C]; exact_mod_cast odd_first_moment n
  have hpeak : (p:ℝ)*C ≤ 2*(rankMoment n 0 1:ℝ) := by dsimp [C,Nat.centralBinom]; exact_mod_cast h
  have hcoef := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 3*(n:ℝ)+2)
  have hfin : (2*(p:ℝ)+4*n+2)*C ≤ ((n:ℝ)*n)*C := by
    nlinarith only [hmom,hpeak,hcoef,mul_nonneg (sq_nonneg (n:ℝ)) hC.le,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hC.le]
  exact_mod_cast (le_of_mul_le_mul_right hfin hC)

end CentralUnimodality
