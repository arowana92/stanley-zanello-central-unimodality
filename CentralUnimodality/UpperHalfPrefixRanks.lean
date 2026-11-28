module

public import CentralUnimodality.UpperHalfPrefixScales
public import CentralUnimodality.UpperHalfSpectralMoments
public import CentralUnimodality.RankBinGaussian

/-! A positive lower bound on the actual normalized prefix mass and a
forward-difference bound throughout the remaining far-corank range. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real BinArithmetic

theorem upper_half_free_suffix {m M : ℕ} (hM : 3685 ≤ M) (hMm : M ≤ m) {c σ : ℝ}
    (hc : 0 ≤ c) (hcm : c*m ≤ 1) (hσ : 0<σ) (hV : suffixVariance c M=σ^2) :
    FreeSuffixApproximation c M σ (16/1000) (32/1000) (69/1000) := by
  obtain ⟨H₀,H₁,H₂⟩ := upper_half_spectral_moments hM hMm hc hcm hσ hV
  exact free_suffix_of_spectral_allowances c hσ M H₀ H₁ H₂

theorem far_prefix_ranks {m : ℕ} (hm : 4096 ≤ m) {c : ℝ} (hc : 0<c) (hcm : c*m ≤ 1)
    (hγ : 119/5 ≤ 2*c*sizeScale m) {j : ℤ} (hj : meanRank c m=j) :
    let L := timeCut m (1/10)
    let P := live c (c*m) L 1
    let σ := √(suffixVariance c (m-L))
    let A := fun k => prefixSiteMass c m L k/P
    37/200 ≤ σ*A j ∧ |σ^2*(A (j+1)-A j)| ≤ 11/40 ∧ 15/4 ≤ σ*(1-exp (-2*c)) := by
  let L := timeCut m (1/10)
  let f : ℝ := 1/10+1/4096
  let σ := √(suffixVariance c (m-L))
  have ⟨_,_,hσlo,_,hV⟩ := far_prefix_scales hm hc hcm hγ
  have ⟨_,_,_,hB,hLf,_⟩ := cut_geometry hm (show (1/14:ℚ)≤1/10 by norm_num) (show (1/10:ℚ)≤1/10 from le_rfl)
  have hfL : (L:ℝ) ≤ f*m := by simpa [L,f,epsilon] using hLf
  have hM : (4096:ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0<(m:ℝ) := by linarith
  have hs : 0<sizeScale m := mul_pos hp (sqrt_pos.mpr hp)
  have hσ : 0<σ := (mul_pos (by norm_num : (0:ℝ)<79/500) hs).trans_le hσlo
  have hfree := upper_half_free_suffix hB (Nat.sub_le m L) hc.le hcm hσ (sq_sqrt ((sqrt_pos.mp hσ).le)).symm
  have ⟨H₀,H₁,_⟩ := conditional_prefix_allowances (by omega : 0<m) hc
    (by norm_num [f] : 0 ≤ f) (by norm_num [f] : f < 1) hfL hσ hfree hj
  have hG := (gaussian_cubic_lower (2/3)).trans
    (exp_le_exp.mpr (show -(2/3:ℝ) ≤ -varianceLimit m c f σ/2 by linarith only [hV]))
  have hfac : 0 ≤ 2*c := by positivity
  have ht := tiny_tilt_step hfac (by linarith only [hcm,mul_le_mul_of_nonneg_right hM hc.le])
  have HT := mul_le_mul_of_nonneg_left ht hσ.le
  rw [← neg_mul] at HT
  have Hs := mul_le_mul_of_nonneg_left hσlo hfac
  dsimp only at H₀ H₁ ⊢
  exact ⟨by linarith only [H₀,hG],by linarith only [H₁],by linarith only [HT,Hs,hγ]⟩

/-- The remaining far-corank input can be restricted to two signed
losses. Mass loss at most .05 and forward loss at most .20 suffice. -/
theorem far_growth_of_losses {m j T : ℕ} (hm : 4096 ≤ m) {c : ℝ} (hc : 0<c) (hcm : c*m ≤ 1)
    (hγ : 119/5 ≤ 2*c*sizeScale m) (hj : meanRank c m=(j+1:ℕ)) (hT : T≤m)
    (hLT : timeCut m (1/10) ≤ T)
    (loss : let L := timeCut m (1/10)
            let P := live c (c*m) L 1
            let σ := √(suffixVariance c (m-L))
            let Q (r : Fin 3) := σ^(r.val+1)/P*(earlyRankLoss c m L T r (j+1:ℕ)+
              signedRank r (j+1:ℕ) (eventSiteMass c m (lateHitEvent m T)))
            Q 0 ≤ 1/20 ∧ Q 1 ≤ 1/5) :
    rankCount m (j+1)<rankCount m (j+2) := by
  let L := timeCut m (1/10)
  let P := live c (c*m) L 1
  let σ := √(suffixVariance c (m-L))
  let k : ℤ := (j+1:ℕ)
  let A := eventSiteMass c m (ballots m)
  have ⟨_,hP,hσlo,_,_⟩ := far_prefix_scales hm hc hcm hγ
  have hp : 0<(m:ℝ) := by exact_mod_cast (show 0<m by omega)
  have hσ : 0<σ := (mul_pos (by norm_num : (0:ℝ)<79/500) (mul_pos hp (sqrt_pos.mpr hp))).trans_le hσlo
  have hk : meanRank c m=k := by dsimp [k]; exact_mod_cast hj
  obtain ⟨H₀,H₁,HT⟩ := far_prefix_ranks hm hc hcm hγ hk
  let pre := prefixSiteMass c m L
  let cost := fun r => earlyRankLoss c m L T r k+signedRank r k (eventSiteMass c m (lateHitEvent m T))
  have Hpre₀ : 37/200 ≤ σ/P*signedRank 0 k pre := by
    change 37/200 ≤ σ/P*pre k; change _ ≤ σ*(pre k/P) at H₀
    linarith only [H₀,show σ*(pre k/P)=σ/P*pre k by ring]
  have Hpre₁ : -(11/40) ≤ σ^2/P*signedRank 1 k pre := by
    change _ ≤ σ^2/P*(pre (k+1)-pre k)
    change |σ^2*(pre (k+1)/P-pre k/P)| ≤ _ at H₁
    exact (abs_le.mp H₁).1.trans_eq (by ring)
  have Hloss₀ : σ/P*cost 0 ≤ 1/20 := by
    have H : σ^1/P*cost 0 ≤ 1/20 := loss.1
    simpa only [pow_one] using H
  have Hloss₁ : σ^2/P*cost 1 ≤ 1/5 := loss.2
  have step (r : Fin 3) : signedRank r k A=signedRank r k pre-cost r := by
    dsimp only [A,pre,cost]; rw [ballot_signed_loss c hLT hT]; ring
  have G : 27/200 ≤ σ/P*signedRank 0 k A := by rw [step]; linarith only [Hpre₀,Hloss₀]
  have J : -(19/40) ≤ σ^2/P*signedRank 1 k A := by rw [step]; linarith only [Hpre₁,Hloss₁]
  apply (integer_rank_signs c hc.le m j hσ hP G J (le_refl _)).1
  linarith only [HT]

end CentralUnimodality.MarkedExcursion
