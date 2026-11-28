module

public import CentralUnimodality.RankBinFirstCharge

/-! Telescope all the half-open ceiling intervals. The last interval ends
at the late-event cut for each of the two prefix fractions. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic
open Real

theorem all_rank_charges {curve : Bool} {i m j : ℕ} {c : ℝ}
    (hcheck : checkSigns curve i=true) (h : SaddleAt (saddleBin curve i) m c)
    (hj : meanRank c m=(j+1:ℕ)) (r : Fin 3) :
    let B := saddleBin curve i
    let L := timeCut m B.fraction
    let T := timeCut m lateCut
    let σ := √(suffixVariance c (m-L))
    let P := live c (c*m) L 1
    σ^(r.val+1)/P*(earlyRankLoss c m L T r (j+1:ℕ)+
      signedRank r (j+1:ℕ) (eventSiteMass c m (lateHitEvent m T))) ≤ (sumCharges B (shiftRow curve i) r:ℝ) := by
  let B := saddleBin curve i
  let row := shiftRow curve i
  let L := timeCut m B.fraction
  let T := timeCut m lateCut
  let S (k : ℕ) := timeCut m (cutAt B k)
  let U (k : ℕ) := (firstCharge B row k r).units
  let V := (lateCharge B row r).units
  let A := (√(suffixVariance c (m-L)))^(r.val+1)/live c (c*m) L 1
  have ⟨_,_,_,_,_,_,_,_,hl,hl'⟩ := checked_bin_data hcheck
  have s₀ : S 0=L := by
    dsimp only [S,L,cutAt]; norm_num only [Nat.cast_zero,zero_div,add_zero]
    rw [min_eq_right (by dsimp [lateCut]; linarith only [hl'] : B.fraction ≤ lateCut)]
  have s₄₂ : S 42=T := by
    dsimp only [S,T,cutAt]; norm_num only [Nat.cast_ofNat]
    rw [min_eq_left (by dsimp [lateCut]; linarith only [hl] : lateCut ≤ B.fraction+7/8)]
  have mono : Monotone S := by
    apply monotone_nat_of_le_succ
    intro k; apply Nat.ceil_mono
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg (α:=ℝ) m)
    exact (Rat.cast_le (K:=ℝ)).mpr (cutAt_bounds (by linarith only [hl] : 0≤B.fraction) k).2.1
  have part (k : ℕ) (hk : k ≤ 42) :
      A*earlyRankLoss c m L (S k) r (j+1:ℕ) ≤ (∑ b ∈ Finset.range k, (U b:ℝ))/(scale:ℝ) := by
    induction k with
    | zero => simp [s₀,earlyRankLoss]
    | succ k IH =>
      have U₁ := actual_first_charge hcheck h hj r (⟨k,by omega⟩ : Fin 42)
      change A*earlyRankLoss c m (S k) (S (k+1)) r (j+1:ℕ) ≤ (U k:ℝ)/scale at U₁
      rw [early_loss_split (S:=S k) c m (by rw [← s₀]; exact mono (Nat.zero_le _)) (mono (Nat.le_succ _)),
        mul_add,Finset.sum_range_succ,add_div]
      exact add_le_add (IH (by omega)) U₁
  have H := part 42 le_rfl
  rw [s₄₂] at H
  have H' := actual_late_charge hcheck h hj r
  change A*signedRank r (j+1:ℕ) (eventSiteMass c m (lateHitEvent m T)) ≤ (V:ℝ)/scale at H'
  change A*(_+_) ≤ _
  rw [mul_add]
  apply (add_le_add H H').trans_eq
  dsimp only [sumCharges]; push_cast
  rw [add_div]

end CentralUnimodality.MarkedExcursion.BinArithmetic
