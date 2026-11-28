module

public import CentralUnimodality.UpperHalfFirstCharge
public import CentralUnimodality.UpperHalfLateRanks
public import CentralUnimodality.UpperHalfPrefixRanks
public import CentralUnimodality.RightFlankRanks

/-! Strict adjacent growth from the midpoint through corank
three quarters of the Brownian scale, for both central families. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic
open Real

theorem far_early_ranks {m : ℕ} (hm : 4096≤m) {c : ℝ} (hc : 0<c) (hcm : c*m≤1)
    (hγ : 119/5≤2*c*sizeScale m) (r : Fin 3) (hr : r.val≤1) (k : ℤ) :
    let L := timeCut m (1/10)
    let σ := √(suffixVariance c (m-L))
    let P := live c (c*m) L 1
    σ^(r.val+1)/P*earlyRankLoss c m L (timeCut m lateCut) r k ≤ 1/40 := by
  let L := timeCut m (1/10)
  let S (i : ℕ) := timeCut m (farCut i)
  let A := (√(suffixVariance c (m-L)))^(r.val+1)/live c (c*m) L 1
  have s₀ : S 0=L := by change timeCut m (farCut 0)=_; rw [show farCut 0=1/10 by decide +kernel]
  have s₇ : S 7=timeCut m lateCut := by change timeCut m (farCut 7)=_; rw [show farCut 7=lateCut by decide +kernel]
  have mono : Monotone S := by
    apply monotone_nat_of_le_succ
    intro i; apply Nat.ceil_mono
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg (α:=ℝ) m)
    apply (Rat.cast_le (K:=ℝ)).mpr
    exact min_le_min_left _ (by push_cast; linarith)
  have part (b : ℕ) (hb : b≤7) :
      A*earlyRankLoss c m L (S b) r k ≤ ∑ i ∈ Finset.range b, (charge (farTimeCost i):ℝ) := by
    induction b with
    | zero => simp [s₀,earlyRankLoss]
    | succ b IH =>
      rw [early_loss_split (S:=S b) c m (by rw [← s₀]; exact mono (Nat.zero_le _)) (mono (Nat.le_succ _)),
        mul_add,Finset.sum_range_succ]
      exact add_le_add (IH (by omega)) (far_first_charge hm hc hcm hγ r hr k ⟨b,by omega⟩)
  have H := part 7 le_rfl
  rw [s₇] at H
  exact H.trans (by simpa using (Rat.cast_le (K:=ℝ)).mpr far_time_total)

theorem far_corank_growth {m j : ℕ} (hm : 4096≤m) (hmid : staircaseDegree m≤2*(j+1))
    (hj : j+1≤staircaseDegree m) (hlo : 2*sizeScale m ≤ (staircaseDegree m:ℝ)-(j+1)) :
    rankCount m (j+1)<rankCount m (j+2) := by
  obtain ⟨c,hc,he,hcm,hbound⟩ := upper_half_saddle (by omega : 770≤m) hmid hj
  have hp : 0<(m:ℝ) := by exact_mod_cast (show 0<m by omega)
  have hs : 0<sizeScale m := mul_pos hp (sqrt_pos.mpr hp)
  change (119/10)*((staircaseDegree m:ℝ)-((j+1:ℕ):ℝ))≤2*c*sizeScale m*sizeScale m at hbound
  push_cast at hbound
  have hγ : 119/5≤2*c*sizeScale m := by
    apply le_of_mul_le_mul_right (a:=sizeScale m) _ hs
    linarith only [hbound,hlo]
  have hcp : 0<c := lt_of_le_of_ne hc (fun h => by rw [← h] at hγ; norm_num at hγ)
  have cut := cut_geometry hm (by norm_num : (1/14:ℚ)≤1/10) (le_refl (1/10:ℚ))
  apply far_growth_of_losses hm hcp hcm.le hγ he cut.2.2.1 cut.2.1.le
  have H₀ := far_early_ranks hm hcp hcm.le hγ 0 (by decide) (j+1:ℕ)
  have H₁ := far_early_ranks hm hcp hcm.le hγ 1 (by decide) (j+1:ℕ)
  have ⟨L₀,L₁⟩ := far_late_ranks hm hcp hcm.le hγ (j+1:ℕ)
  dsimp only at H₀ H₁ L₀ L₁ ⊢
  norm_num only [Fin.val_zero,Fin.val_one,Nat.zero_add,Nat.reduceAdd,pow_one] at H₀ H₁ ⊢
  constructor <;> rw [mul_add]
  · linarith only [H₀,L₀]
  · linarith only [H₁,L₁]

/-- Strict growth in the original natural-number rank, uniformly in
the parity of m. The midpoint inequality refers to the lower rank. -/
theorem upper_half_growth {m j : ℕ} (hm : 4096≤m) (hmid : staircaseDegree m≤2*(j+1))
    (hj : j+1≤staircaseDegree m) (hlo : (3/4)*sizeScale m ≤ (staircaseDegree m:ℝ)-(j+1)) :
    rankCount m (j+1)<rankCount m (j+2) := by
  by_cases h : (staircaseDegree m:ℝ)-(j+1) ≤ 2*sizeScale m
  · exact right_flank_growth hm hj hlo h
  · exact far_corank_growth hm hmid hj (le_of_not_ge h)

end CentralUnimodality.MarkedExcursion.BinArithmetic
