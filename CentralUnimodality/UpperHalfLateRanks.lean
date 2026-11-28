module

public import CentralUnimodality.UpperHalfLateBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The same final-cut rank bounds in the complementary tilt range,
using the retained Fourier cancellation during survival to the last cut. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real BinArithmetic

private theorem wider_late_budget {m L T : ℕ} (hm : 4096 ≤ m) (hd : (837/1000)*(m:ℝ) ≤ (T-L:ℕ))
    {σ : ℝ} (hσ : 0 ≤ σ) (hu : σ ≤ (3/10)*sizeScale m) (r : Fin 3) :
    σ^(r.val+1)*lateFourierBudget (T-L:ℕ) r.val ≤ 2*lateUniformLimit r := by
  have hM : (4096:ℝ) ≤ m := by exact_mod_cast hm
  have H := late_uniform_budget hM hd (show 0 ≤ (259/300)*σ by positivity)
    (show (259/300)*σ ≤ 259/1000*((m:ℝ)*√m) by change _ ≤ 259/1000*sizeScale m; linarith only [hu]) r
  rw [mul_pow] at H
  fin_cases r <;> norm_num [lateUniformLimit] at H ⊢ <;> linarith only [H]

private theorem exp_neg_thirteen : exp (-13) ≤ 1/300000 := by
  have h : (27/10:ℝ) ≤ exp 1 := by linarith only [exp_one_gt_d9]
  have H := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤27/10) h 13
  rw [← exp_nat_mul] at H
  norm_num at H
  rw [exp_neg,← one_div]; exact one_div_le_one_div_of_le (by norm_num) (by linarith only [H])

theorem late_loss_moderate_tilt {m L T : ℕ} (hm : 4096 ≤ m) (hL : 0<L) (hLT : L<T) (hT : T≤m)
    (hcut : 15/16*(m:ℝ) ≤ T) (hlow : (m:ℝ)/10 ≤ L) (hd : (837/1000)*(m:ℝ) ≤ (T-L:ℕ))
    {c σ P : ℝ} (hc : 0<c) (hhi : c*m ≤ 2/5) (hγ : 119/5 ≤ 2*c*sizeScale m)
    (hσ : 0 ≤ σ) (hu : σ ≤ (3/10)*sizeScale m) (hP : tanh (c*m) ≤ P) (hn : 9 ≤ P*√m)
    (r : Fin 3) (k : ℤ) :
    σ^(r.val+1)/P*signedRank r k (eventSiteMass c m (lateHitEvent m T)) ≤ (6/300000)*lateUniformLimit r := by
  let u := c*m
  let d := tanh u
  let b := (15/32)*d
  let U := u-b
  have hM : (4096:ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0<(m:ℝ) := by linarith
  have hr := sqrt_pos.mpr hp
  have hLp : 0<(L:ℝ) := by exact_mod_cast hL
  have hup : 0<u := mul_pos hc hp
  have hsmall₀ : 0 ≤ u := hup.le
  have hsmall : u^2 ≤ (2/5)^2 := pow_le_pow_left₀ hup.le hhi 2
  have hd₀ : (94/100)*u ≤ d := by
    dsimp only [d]; nlinarith only [tanh_cubic_lower hup.le,mul_le_mul_of_nonneg_left hsmall hup.le,hsmall₀]
  have hdu : d ≤ u := tanh_le_linear hup.le
  have hdp : 0<d := (mul_pos (by norm_num) hup).trans_le hd₀
  have hb₀ : 0 ≤ b := by dsimp [b]; positivity
  have hb₁ : b ≤ 6/25 := by dsimp only [b]; change u ≤ 2/5 at hhi; linarith only [hdu,hhi]
  have hU₀ : 0 ≤ U := by dsimp only [U,b]; linarith only [hdu,hdp]
  have hU₁ : U ≤ 6/25 := by dsimp only [U,b]; change u ≤ 2/5 at hhi; linarith only [hd₀,hhi]
  have he := late_rank_moments hc.le (by norm_num : (0:ℝ)≤0) hb₀ hb₁ hU₀ hU₁ hL hLT hT
    (by simp only [add_zero]; exact le_refl U) (by simpa only [add_zero] using far_late_height hp hT hcut hdp.le) r k
  simp [rankChange_zero] at he
  have hsig := wider_late_budget hm hd hσ hu r
  have hγ₁ : 119/10 ≤ u*√m := by dsimp only [sizeScale] at hγ; dsimp only [u]; linarith only [hγ]
  have hb' : (51/10:ℝ) ≤ b*√m := by dsimp only [b]; linarith only [hγ₁,mul_le_mul_of_nonneg_right hd₀ hr.le]
  have hb2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 51/10) hb' 2
  rw [mul_pow,sq_sqrt hp.le] at hb2
  have hdec : exp (-(m*b^2/2)) ≤ 1/300000 := (exp_le_exp.mpr (by linarith only [hb2] : -((m:ℝ)*b^2/2) ≤ -13)).trans exp_neg_thirteen
  have hPp : 0<P := hdp.trans_le hP
  have hroot : √(m:ℝ)/4 ≤ √L := by
    apply (le_sqrt (by positivity) hLp.le).mpr
    rw [div_pow,sq_sqrt hp.le]; linarith only [hlow,hp]
  have hnorm : 1 ≤ √(L:ℝ)*P := by linarith only [hn,mul_le_mul_of_nonneg_right hroot hPp.le]
  have hfrac : (4/5:ℝ)/√L ≤ (4/5)*P := (div_le_iff₀ (sqrt_pos.mpr hLp)).mpr (by linarith only [hnorm])
  have hW : (2*U+(4/5)/√L)/P ≤ 3 := by
    apply (div_le_iff₀ hPp).mpr
    change d ≤ P at hP
    dsimp only [U]; linarith only [hb₀,hfrac,hP,hd₀,hup]
  let F := signedRank r k (eventSiteMass c m (lateHitEvent m T))
  have hf : F ≤ |rankDifference r k (eventSiteMass c m (lateHitEvent m T))| := by
    dsimp only [F,signedRank]; split_ifs <;> first | exact neg_le_abs _ | exact le_abs_self _
  have hmul := mul_le_mul_of_nonneg_left (hf.trans he) (show 0 ≤ σ^(r.val+1)/P by positivity)
  have W₀ : 0 ≤ (2*U+(4/5)/√L)/P := by positivity
  have HH := mul_le_mul_of_nonneg_left hsig (mul_nonneg (exp_pos (-((m:ℝ)*b^2/2))).le W₀)
  have lim : 0 ≤ lateUniformLimit r := by fin_cases r <;> norm_num [lateUniformLimit]
  have J := mul_le_mul_of_nonneg_right (mul_le_mul hdec hW W₀ (by norm_num)) (mul_nonneg (by norm_num : (0:ℝ)≤2) lim)
  apply hmul.trans
  apply le_trans _ (HH.trans (J.trans_eq (by ring)))
  apply le_of_eq; ring

/-- Total normalized mass and forward loss after ceil(15m/16). -/
theorem far_late_ranks {m : ℕ} (hm : 4096 ≤ m) {c : ℝ} (hc : 0<c) (hcm : c*m ≤ 1)
    (hγ : 119/5 ≤ 2*c*sizeScale m) (k : ℤ) :
    let L := timeCut m (1/10)
    let T := timeCut m lateCut
    let σ := √(suffixVariance c (m-L))
    let P := live c (c*m) L 1
    let A := eventSiteMass c m (lateHitEvent m T)
    σ/P*signedRank 0 k A ≤ 1/200 ∧ σ^2/P*signedRank 1 k A ≤ 1/50 := by
  let L := timeCut m (1/10)
  let T := timeCut m lateCut
  obtain ⟨hL,hLT,hTm,_,hLf,hd⟩ := cut_geometry hm (by norm_num : (1/14:ℚ)≤1/10) (show (1/10:ℚ)≤1/10 from le_rfl)
  have hT : 15/16*(m:ℝ) ≤ T := by
    have H : (lateCut:ℝ)*m ≤ T := Nat.le_ceil _
    simpa [lateCut] using H
  have hl : (m:ℝ)/10 ≤ L := by
    have H : ((1/10:ℚ):ℝ)*m ≤ L := Nat.le_ceil _
    push_cast at H; linarith only [H]
  have hLf' : (L:ℝ) ≤ (1/10+1/4096)*m := by simpa [L,epsilon] using hLf
  have hP := far_prefix_survival hc (by exact_mod_cast (show 0<m by omega)) hcm hLf'
  have ⟨hn,_,_,hu,_⟩ := far_prefix_scales hm hc hcm hγ
  by_cases h : c*m ≤ 2/5
  · have H := late_loss_moderate_tilt hm hL hLT hTm hT hl hd hc h hγ (sqrt_nonneg _) hu hP hn
    obtain h₀ := H 0 k
    obtain h₁ := H 1 k
    norm_num [lateUniformLimit] at h₀ h₁
    exact ⟨h₀.trans (by norm_num),h₁.trans (by norm_num)⟩
  · have H := late_loss_large_tilt hm hTm hT hc.le (le_of_not_ge h) hcm (sqrt_nonneg _) hu hP k
    exact ⟨H.1.trans (by norm_num),H.2.trans (by norm_num)⟩

end CentralUnimodality.MarkedExcursion
