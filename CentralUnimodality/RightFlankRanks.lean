module

public import CentralUnimodality.RankBinCoverage
public import CentralUnimodality.RankBinLossSum
public import CentralUnimodality.RankBinPrefixCharge

/-! Integer growth and log-concavity on the right-flank saddle windows.
The integer parameter m covers both central staircase parities. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic
open Real

private theorem step_factor {B : SaddleBin} {m : ℕ} {c σ : ℝ}
    (h : SaddleAt B m c) (hG : B.upper ≤ 25)
    (hz : 0<B.zlo) (hσ : sizeScale m*B.zlo ≤ σ) :
    (999/1000)*(B.zlo:ℝ)*B.lower ≤ σ*(1-exp (-2*c)) := by
  have hM : (4096:ℝ) ≤ m := by exact_mod_cast h.large
  have hmp : 0<(m:ℝ) := by linarith
  have hr : 64 ≤ √(m:ℝ) := (le_sqrt (by norm_num) hmp.le).mpr (by linarith)
  have hs : (262144:ℝ) ≤ sizeScale m := by
    dsimp only [sizeScale]; nlinarith only [mul_le_mul hM hr (by norm_num) hmp.le]
  have hmax := h.upper.trans (show (B.upper:ℝ) ≤ 25 by exact_mod_cast hG)
  have hc := mul_nonneg (by norm_num : (0:ℝ) ≤ 2) h.positive.le
  have hsmall : 2*c ≤ 1/1000 := by linarith only [mul_le_mul_of_nonneg_left hs hc,hmax]
  have he := tiny_tilt_step hc hsmall
  have hzr : 0 ≤ (B.zlo:ℝ) := by exact_mod_cast hz.le
  have hσ₀ : 0 ≤ σ := (mul_nonneg (by linarith only [hs]) hzr).trans hσ
  have H₁ := mul_le_mul_of_nonneg_right h.lower hzr
  have H₂ := mul_le_mul_of_nonneg_right hσ hc
  have H₃ := mul_le_mul_of_nonneg_left he hσ₀
  rw [neg_mul]
  linarith only [H₁,H₂,H₃]

theorem certified_bin_sign {curve : Bool} {i m j : ℕ} {c : ℝ}
    (hcheck : checkSigns curve i=true) (h : SaddleAt (saddleBin curve i) m c)
    (hj : meanRank c m=(j+1:ℕ)) (hN : 3989/10000 ≤ normalHeight) :
    if curve then rankCount m j*rankCount m (j+2)<rankCount m (j+1)^2
    else rankCount m (j+1)<rankCount m (j+2) := by
  let B := saddleBin curve i
  let L := timeCut m B.fraction
  let T := timeCut m lateCut
  let σ := √(suffixVariance c (m-L))
  let P := live c (c*m) L 1
  let lost := sumCharges B (shiftRow curve i)
  let margin (r : Fin 3) := binPrefix B r-lost r
  have ⟨_,_,hG,_,hz,_,_,_,hl,hl'⟩ := checked_bin_data hcheck
  have ⟨_,hLT,hTm,_,_,_⟩ := cut_geometry h.large hl hl'
  have ⟨hzlo,_,_,hP,_⟩ := bin_actual_scales hcheck h
  have hs : 0<sizeScale m := by
    have hp : 0<(m:ℝ) := by exact_mod_cast (show 0<m by have := h.large; omega)
    exact mul_pos hp (sqrt_pos.mpr hp)
  have hσ : 0<σ := (mul_pos hs (by exact_mod_cast hz)).trans_le hzlo
  have H (r : Fin 3) : (margin r:ℝ) ≤ σ^(r.val+1)/P*signedRank r (j+1:ℕ) (eventSiteMass c m (ballots m)) := by
    rw [show (margin r:ℝ)=(binPrefix B r:ℝ)-(lost r:ℝ) from Rat.cast_sub ..]
    exact ballot_rank_margins hLT.le hTm c _ (fun k => (binPrefix B k:ℝ)) (fun k => (lost k:ℝ))
      (bin_prefix_margins hcheck h hj hN) (all_rank_charges hcheck h hj) r
  have actual := integer_rank_signs c h.positive.le m j hσ hP (by simpa only [Fin.val_zero,Nat.zero_add,pow_one] using H 0) (H 1) (H 2)
  have C := of_decide_eq_true hcheck
  have hmass : 0<margin 0 := C.2.2.2.2.2.2.2.2.1
  have signs := C.2.2.2.2.2.2.2.2.2.2
  change (if curve then 3/100 < -((3989/10000)*binCentral B+10/1000+lost 2)
    else 33/1000 < 999/1000*B.zlo*B.lower*margin 0-1/4-lost 1) at signs
  have fac := step_factor h hG hz hzlo
  split
  · rename_i ht
    rw [ite_eq_left ht] at signs
    apply actual.2
    have pos : (0:ℚ)<margin 2 := by
      change 0< -(3989/10000*binCentral B+10/1000)-lost 2
      linarith only [signs]
    exact_mod_cast pos
  · rename_i ht
    rw [ite_eq_right ht] at signs
    apply actual.1
    have hq : (0:ℚ) < margin 1+(999/1000)*B.zlo*B.lower*margin 0 := by
      change 0 < -(1/4)-lost 1+999/1000*B.zlo*B.lower*margin 0
      linarith only [signs]
    have hr := (Rat.cast_lt (K:=ℝ)).mpr hq
    push_cast at hr
    have Hfac := mul_le_mul_of_nonneg_right fac (show 0 ≤ (margin 0:ℝ) by exact_mod_cast hmass.le)
    linarith only [hr,Hfac]

/-- Strict growth of the actual staircase coefficients throughout the
closed window 3/4 ≤ (D-j)/m^(3/2) ≤ 2 at all lengths m ≥ 4096. -/
theorem right_flank_growth {m j : ℕ} (hm : 4096 ≤ m) (hj : j+1 ≤ staircaseDegree m)
    (hlo : (3/4)*sizeScale m ≤ (staircaseDegree m:ℝ)-(j+1))
    (hhi : (staircaseDegree m:ℝ)-(j+1) ≤ 2*sizeScale m) : rankCount m (j+1)<rankCount m (j+2) := by
  obtain ⟨i,c,H,hs,he⟩ := checked_rank_saddle false hm hj
    (by simpa [corankStart] using hlo) (by simpa using hhi)
  exact certified_bin_sign H hs he normal_height_bounds.1

/-- Strict log-concavity in the narrower closed window 15/16 through 2,
for the same two families and the same integer rank counts. -/
theorem right_flank_log_concave {m j : ℕ} (hm : 4096 ≤ m) (hj : j+1 ≤ staircaseDegree m)
    (hlo : (15/16)*sizeScale m ≤ (staircaseDegree m:ℝ)-(j+1))
    (hhi : (staircaseDegree m:ℝ)-(j+1) ≤ 2*sizeScale m) :
    rankCount m j*rankCount m (j+2)<rankCount m (j+1)^2 := by
  obtain ⟨i,c,H,hs,he⟩ := checked_rank_saddle true hm hj
    (by simpa [corankStart] using hlo) (by simpa using hhi)
  exact certified_bin_sign H hs he normal_height_bounds.1

end CentralUnimodality.MarkedExcursion.BinArithmetic
