module

public import CentralUnimodality.UpperHalfSaddle
public import CentralUnimodality.UpperHalfVariance
public import CentralUnimodality.RankBinSetup

/-! Actual surviving-prefix scales once the corank is at least twice the
Brownian scale. The tilt is allowed to range all the way to the midpoint. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real BinArithmetic

private theorem drift_cap {u : ℝ} (hu : 0 ≤ u) (hcap : u ≤ 1) : tanh u ≤ 77/100 := by
  have H := (upper_half_label_floors hu hcap).1
  rw [← mul_one u,← label_variance_cosh u 1] at H
  have ha := up_total u
  have hb := up_drift u
  have h₁ : upChance u=(1+tanh u)/2 := by linarith only [ha,hb]
  have h₂ : upChance (-u)=(1-tanh u)/2 := by linarith only [ha,hb]
  simp only [labelVariance,mul_one] at H
  rw [h₁,h₂] at H
  have hsq : (tanh u)^2 ≤ (77/100:ℝ)^2 := by nlinarith only [H]
  exact (le_abs_self _).trans ((sq_le_sq₀ (abs_nonneg _) (by norm_num)).mp (by rwa [sq_abs]))

theorem far_prefix_survival {c : ℝ} {m L : ℕ} (hc : 0<c) (hM : 0<(m:ℝ)) (hu' : c*m ≤ 1)
    (hL : (L:ℝ) ≤ (1/10+1/4096)*m) : tanh (c*m) ≤ live c (c*m) L 1 := by
  let f : ℝ := 1/10+1/4096
  let u := c*m
  let d := tanh u
  change (L:ℝ) ≤ f*m at hL
  have hu : 0<u := mul_pos hc hM
  have hd₁ : d ≤ 77/100 := drift_cap hu.le hu'
  have hd₀ : 0<d := (mul_pos (by norm_num) hu).trans_le (upper_half_drift hu.le hu')
  have hlive := live_lower c u ((1-f)*u) L 1 (fun i hi => by
    have h' : (i:ℝ) ≤ L := by exact_mod_cast hi.le
    dsimp only [u]; linarith only [mul_le_mul_of_nonneg_left (h'.trans hL) hc.le])
  rw [pow_one] at hlive
  have hf : 0 ≤ f := by norm_num [f]
  have hf' : f<1 := by norm_num [f]
  have hprob := (drift_cost hu hf hf').1.trans (mul_le_mul_of_nonneg_left hlive (by positivity : 0 ≤ 1+d))
  have hcoef : 1+d ≤ 2*(1-f) := by dsimp only [f]; linarith only [hd₁]
  apply le_of_mul_le_mul_left _ (by positivity : 0<1+d)
  exact (mul_le_mul_of_nonneg_right hcoef hd₀.le).trans hprob

/-- Mass normalization and variance bounds for L = ceil(m/10). The only
rank information needed after choosing the saddle is γ ≥ 23.8. -/
theorem far_prefix_scales {m : ℕ} (hm : 4096 ≤ m) {c : ℝ} (hc : 0<c) (hcm : c*m ≤ 1)
    (hγ : 119/5 ≤ 2*c*sizeScale m) :
    let L := timeCut m (1/10)
    let f : ℝ := 1/10+1/4096
    let P := live c (c*m) L 1
    let σ := √(suffixVariance c (m-L))
    9 ≤ P*√m ∧ 0<P ∧ (79/500)*sizeScale m ≤ σ ∧ σ ≤ (3/10)*sizeScale m ∧
      varianceLimit m c f σ ≤ 4/3 := by
  let L := timeCut m (1/10)
  let f : ℝ := 1/10+1/4096
  let B := m-L
  let u := c*m
  let d := tanh u
  let P := live c u L 1
  let σ := √(suffixVariance c B)
  have hM : (4096:ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0<(m:ℝ) := by linarith
  have hs : 0<sizeScale m := mul_pos hp (sqrt_pos.mpr hp)
  have hu : 0<u := mul_pos hc hp
  have hd₁ : d ≤ 77/100 := drift_cap hu.le hcm
  have hd₀ : 0<d := (mul_pos (by norm_num) hu).trans_le (upper_half_drift hu.le hcm)
  have hk : 9 ≤ √m*d := by
    have H := mul_le_mul_of_nonneg_right (upper_half_drift hu.le hcm) (sqrt_nonneg (m:ℝ))
    dsimp only [u,d,sizeScale] at *
    linarith only [H,hγ]
  obtain ⟨_,hLT,hTm,_,hLf,_⟩ := cut_geometry hm (show (1/14:ℚ)≤1/10 by norm_num) (show (1/10:ℚ) ≤ 1/10 by rfl)
  have hL : (L:ℝ) ≤ f*m := by simpa [L,f,epsilon] using hLf
  have hLm : L ≤ m := hLT.le.trans hTm
  have hB : B ≤ m := Nat.sub_le ..
  have hlab := upper_half_suffix_labels hB hc.le hcm
  have ⟨hlo,hhi⟩ := suffix_variance_bounds c B (by norm_num : (0:ℝ) ≤ 13/125)
    (fun i hi => ⟨(hlab i hi).1,(hlab i hi).2.1⟩)
  have hB' : (1-f)*(m:ℝ) ≤ (B:ℝ) := by dsimp only [B]; rw [Nat.cast_sub hLm]; linarith only [hL]
  have hss : (sizeScale m)^2=(m:ℝ)^3 := by dsimp [sizeScale]; rw [mul_pow,sq_sqrt hp.le]; ring
  have hslo : (79/500)*sizeScale m ≤ σ := by
    apply (le_sqrt (by positivity) (by linarith only [hlo,pow_nonneg (Nat.cast_nonneg (α:=ℝ) B) 3])).mpr
    rw [mul_pow,hss]
    have H := pow_le_pow_left₀ (mul_nonneg (by norm_num [f]) hp.le) hB' 3
    rw [mul_pow] at H
    dsimp only [f] at H; linarith only [hlo,H,pow_nonneg hp.le 3]
  have hshi : σ ≤ 3/10*sizeScale m := by
    apply (sqrt_le_left (by positivity)).mpr
    have hle : (B:ℝ)+1 ≤ (4097/4096)*m := by
      have h' : (B:ℝ) ≤ m := by exact_mod_cast hB
      linarith only [h',hM]
    have H := pow_le_pow_left₀ (by positivity) hle 3
    rw [mul_pow] at H ⊢; rw [hss]
    linarith only [hhi,H,pow_nonneg hp.le 3]
  have hf : 0 ≤ f := by norm_num [f]
  have hf' : f<1 := by norm_num [f]
  have hdP : d ≤ P := far_prefix_survival hc hp hcm hL
  refine ⟨hk.trans (by linarith only [mul_le_mul_of_nonneg_right hdP (sqrt_nonneg (m:ℝ))]),hd₀.trans_le hdP,hslo,hshi,?_⟩
  have HV := bin_prefix_variance hp hf hf' (by norm_num : (0:ℝ)<79/500) (by norm_num : (0:ℝ)<9)
    hd₀ hd₁ (by simpa only [sizeScale,mul_comm (79/500:ℝ)] using hslo) hk
  exact HV.trans (by norm_num [f])

end CentralUnimodality.MarkedExcursion
