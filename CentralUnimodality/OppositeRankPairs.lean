module

public import CentralUnimodality.TwoHarmonicRows
public import CentralUnimodality.LateRankBlocks

/-! Pair the first position of each even block with the last, and work
inward. The endpoint contraction retains all the odd label spacings. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real Polynomial

noncomputable def oppositeEnergy (l : ℕ) (θ : ℝ) : ℝ :=
  (1/5)*∑ i ∈ Finset.range l, sin ((2*(i:ℝ)+1)*θ/2)^2

noncomputable def twoHarmonicFactor (l : ℕ) (θ : ℝ) : ℝ :=
  3/8+exp (-oppositeEnergy l θ)/2+exp (-oppositeEnergy l (2*θ))/8

theorem free_opposite_pairs (c u a θ : ℝ) (l : ℕ)
    (hp : ∀ i<2*l, 9/25 ≤ upChance (-(u-c*i)) ∧ upChance (-(u-c*i)) ≤ 31/50) :
    endpointNorm (endpointRow c u a θ (words (2*l))) ≤ exp (-oppositeEnergy l θ) := by
  let p (i : ℕ) := upChance (-(u-c*i))
  let F (i : ℕ) := signFactor (p i) (θ*(a-i))
  rw [endpointRow_product,two_mul]
  change endpointNorm (∏ i ∈ Finset.range (l+l), F i) ≤ _
  rw [Finset.prod_range_add,← Finset.prod_range_reflect F l,← Finset.prod_mul_distrib]
  apply (endpointNorm_prod ..).trans
  have pair (i : ℕ) (hi : i ∈ Finset.range l) :
      endpointNorm (F (l-1-i)*F (l+i)) ≤ exp (-(1/5)*sin ((2*(i:ℝ)+1)*θ/2)^2) := by
    have hit := Finset.mem_range.mp hi
    let j := l-1-i
    have hj : j<2*l := by dsimp [j]; omega
    have hk : l+i<2*l := by omega
    have hj₀ : 0<p j := (by norm_num : (0:ℝ)<9/25).trans_le (hp j hj).1
    have hj₁ : p j<1 := (hp j hj).2.trans_lt (by norm_num)
    have hk₀ : 0<p (l+i) := (by norm_num : (0:ℝ)<9/25).trans_le (hp _ hk).1
    have hk₁ : p (l+i)<1 := (hp _ hk).2.trans_lt (by norm_num)
    have hd : 0 < p j*(1-p (l+i))+(1-p j)*p (l+i) := add_pos
      (mul_pos hj₀ (sub_pos.mpr hk₁)) (mul_pos (sub_pos.mpr hj₁) hk₀)
    have H := weighted_pair_bound hj₀.le hj₁.le hk₀.le hk₁.le (by norm_num : (0:ℝ)≤1/5)
      ((pair_probability_ranges ..).1 (hp j hj) (hp _ hk)) hd (θ*(a-j)) (θ*(a-(l+i:ℕ)))
    have hdiff : (j:ℝ)+2*i+1=(l+i:ℕ) := by exact_mod_cast (show j+2*i+1=l+i by dsimp [j]; omega)
    apply H.trans_eq
    congr 4
    linarith only [congrArg (θ*·) hdiff]
  apply (Finset.prod_le_prod₀ (fun _ _ => endpointNorm_nonneg _) pair).trans_eq
  rw [← Real.exp_sum,oppositeEnergy,Finset.mul_sum]
  congr 1; rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem opposite_wall_block (c u a θ : ℝ) (l : ℕ) (A : Finset (List Bool)) (hA : A⊆words (2*l))
    (hp : ∀ i<2*l, 9/25 ≤ upChance (-(u-c*i)) ∧ upChance (-(u-c*i)) ≤ 31/50) :
    endpointNorm (endpointRow c u a θ A) ≤ twoHarmonicFactor l θ := by
  apply (retained_two_harmonics c u a θ A hA).trans
  dsimp only [twoHarmonicFactor]
  linarith only [free_opposite_pairs c u a θ l hp,free_opposite_pairs c u a (2*θ) l hp]

theorem opposite_wall_powers (c u a θ : ℝ) (h p l k : ℕ)
    (hp : ∀ i : ℕ, p ≤ i → i < p+k*(2*l) →
      9/25 ≤ upChance (-(u-c*i)) ∧ upChance (-(u-c*i)) ≤ 31/50) :
    endpointNorm (wallRow c u a θ h (p+k*(2*l))) ≤
      (∑ w ∈ (words p).filter (BallotFrom h), signMass c u w)*(twoHarmonicFactor l θ)^k := by
  have hfac : 0≤twoHarmonicFactor l θ := by dsimp [twoHarmonicFactor]; positivity
  apply (wallRow_blocks c u a θ h p (2*l) k hfac _).trans
    (mul_le_mul_of_nonneg_right (endpointRow_mass ..) (pow_nonneg hfac _))
  intro j hj b
  apply opposite_wall_block _ _ _ θ l _ (Finset.filter_subset ..)
  intro i hi
  have H := Nat.mul_le_mul_right (2*l) (show j+1≤k by omega)
  rw [Nat.add_mul,one_mul] at H
  have h₁ := hp (p+j*(2*l)+i) (by omega) (by omega)
  have he : u-c*(p+j*(2*l):ℕ)-c*i=u-c*(p+j*(2*l)+i:ℕ) := by push_cast; ring
  rwa [he]

end CentralUnimodality.MarkedExcursion
