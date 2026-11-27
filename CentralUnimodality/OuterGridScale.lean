module

public import CentralUnimodality.GridPointCount
public import CentralUnimodality.NormalizedCells

/-! The outer-arc error bound is greatest at the first half-length 2049.
The square scale bound is deliberately crude. Its resulting sixth power
is absorbed by the exponential decay with room to spare. -/
@[expose] public section

namespace CentralUnimodality

theorem sample_scale_bound {N : ℕ} (hN : 2049 ≤ N) :
    Witness.cellScale N ≤ 262337*((N:ℝ)/2049)^2 := by
  let t := (N:ℝ)/2049
  have ht : 1 ≤ t := by
    dsimp [t]
    have hn : (2049:ℝ) ≤ N := by exact_mod_cast hN
    linarith only [hn]
  have ht₀ := zero_le_one.trans ht
  have hs : Real.sqrt t ≤ t := (Real.sqrt_le_left ht₀).mpr (by nlinarith only [mul_le_mul_of_nonneg_right ht ht₀])
  have hbase : (4098:ℝ)*Real.sqrt 4098 ≤ 262337 := by
    apply (sq_le_sq₀ (by positivity) (by norm_num)).mp
    rw [mul_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  have he : 2*(N:ℝ) = t*4098 := by dsimp [t]; ring
  rw [Witness.cellScale,he,Real.sqrt_mul ht₀]
  change _ ≤ 262337*t^2
  calc
    _ = (4098*Real.sqrt 4098)*(t*Real.sqrt t) := by ring
    _ ≤ 262337*(t*t) := mul_le_mul hbase (mul_le_mul_of_nonneg_left hs ht₀) (by positivity) (by norm_num)
    _ = _ := by ring

private theorem scaled_width {t S Δ lo hi : ℝ} (ht : 1 ≤ t) (hS : 0 ≤ S) (hb : S ≤ 262337*t^2)
    (hstep : Δ ≤ 1.257) (hl : 0 ≤ lo) (hw : lo ≤ hi) {r : ℕ} (hr : r ≤ 2) :
    ((hi-lo)*S+Δ)*(hi*S)^r ≤ (((hi-lo)*262337+1.257)*(hi*262337)^r)*t^6 := by
  have hh := hl.trans hw
  have hdiff := sub_nonneg.mpr hw
  have ht₀ := zero_le_one.trans ht
  have ht₂ : 1 ≤ t^2 := one_le_pow₀ ht
  have hw₁ : (hi-lo)*S+Δ ≤ ((hi-lo)*262337+1.257)*t^2 := by
    linarith only [mul_le_mul_of_nonneg_left hb hdiff,hstep,
      mul_le_mul_of_nonneg_left ht₂ (by norm_num : (0:ℝ) ≤ 1.257)]
  have hw₂ := pow_le_pow_left₀ (mul_nonneg hh hS) (mul_le_mul_of_nonneg_left hb hh) r
  have hm := mul_le_mul hw₁ hw₂ (pow_nonneg (mul_nonneg hh hS) r) (by positivity)
  have hnorm : (((hi-lo)*262337+1.257)*t^2)*(hi*(262337*t^2))^r =
      (((hi-lo)*262337+1.257)*(hi*262337)^r)*t^(2+2*r) := by
    rw [← mul_assoc hi,mul_pow,← pow_mul,pow_add]
    ring
  apply hm.trans
  rw [hnorm]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (by omega)) (by positivity)

theorem outer_grid_scale {N m L r : ℕ} {c lo hi Δ : ℝ} (hN : 2049 ≤ N) (hm : 2*N ≤ m+1)
    (hc : 0 ≤ c) (hdecay : 6 ≤ 2*c*(63/64)*2049) (hr : r ≤ 2)
    (hl : 0 ≤ lo) (hw : lo ≤ hi) (hstep : Δ ≤ 1.257) :
    (((hi-lo)*Witness.cellScale N+Δ)*(hi*Witness.cellScale N)^r)*
       Real.exp (c*L-c*(63/64)*m) ≤
      (((hi-lo)*262337+1.257)*(hi*262337)^r)*Real.exp (c*L-c*(63/64)*4097) := by
  let t := (N:ℝ)/2049
  have ht : 1 ≤ t := by
    dsimp [t]
    have hn : (2049:ℝ) ≤ N := by exact_mod_cast hN
    linarith only [hn]
  have hs := scaled_width ht (by unfold Witness.cellScale; positivity) (sample_scale_bound hN) hstep hl hw hr
  have ht' : t ≤ Real.exp (t-1) := by linarith only [Real.add_one_le_exp (t-1)]
  have htn := pow_le_pow_left₀ (zero_le_one.trans ht) ht' 6
  rw [← Real.exp_nat_mul] at htn
  have hm' : 2*(N:ℝ) ≤ (m:ℝ)+1 := by exact_mod_cast hm
  have hd := mul_le_mul_of_nonneg_right hdecay (sub_nonneg.mpr ht)
  have hf := mul_le_mul_of_nonneg_left hm' (by positivity : 0 ≤ c*(63/64))
  have he : 6*(t-1)+(c*L-c*(63/64)*m) ≤ c*L-c*(63/64)*4097 := by
    dsimp [t] at hd ⊢
    nlinarith only [hd,hf]
  have htail := (mul_le_mul_of_nonneg_right htn (Real.exp_pos (c*L-c*(63/64)*m)).le)
  rw [← Real.exp_add] at htail
  apply (mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le).trans
  rw [mul_assoc]
  have hdif := sub_nonneg.mpr hw
  have hhi := hl.trans hw
  exact mul_le_mul_of_nonneg_left (htail.trans (Real.exp_le_exp.mpr (by norm_num at he ⊢; exact he))) (by positivity)

end CentralUnimodality
