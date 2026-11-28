module

public import CentralUnimodality.UpperHalfHitGeometry
public import CentralUnimodality.UpperHalfLateBounds
public import CentralUnimodality.FirstHitRankMixture
public import CentralUnimodality.RankLossBins

/-! Combine the centered first-passage bound with the unshifted free
suffix, at an arbitrary integer rank and an actual odd hit time. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real BinArithmetic

theorem far_tilt_square {m : ℕ} {c : ℝ} (hc : 0 ≤ c) (hcm : c*m ≤ 1) :
    (2*c*sizeScale m)^2 ≤ 4*m := by
  have H := pow_le_pow_left₀ (mul_nonneg hc (Nat.cast_nonneg (α:=ℝ) m)) hcm 2
  have eq : (2*c*sizeScale m)^2 = 4*(c*m)^2*m := by
    dsimp only [sizeScale]; ring_nf; rw [sq_sqrt (Nat.cast_nonneg (α:=ℝ) m)]; ring
  rw [eq]
  linarith only [mul_le_mul_of_nonneg_right H (Nat.cast_nonneg (α:=ℝ) m)]

theorem far_first_site {m d : ℕ} (hm : 4096 ≤ m) (ht : 2*d+1 ≤ m) (hb : 255 ≤ m-(2*d+1))
    {c γ v e : ℝ} (hc : 0≤c) (hcm : c*m ≤ 1) (hγ : γ=2*c*sizeScale m)
    (he : e≤2) (hlo : v*m ≤ 2*(d:ℝ)+1) (hhi : 2*(d:ℝ)+1 ≤ e*m) (hcore : 80≤(v/3-2/4096)*m)
    (r : Fin 3) (hr : r.val≤1) (k : ℤ) :
    let B := m-(2*d+1)
    let σ' := √(suffixVariance c B)
    let R := √(v/3-2/4096)
    let a := v*(1-e/2)^2/8
    0<σ' ∧ firstRankLoss c m (2*d+1) r k ≤
      exp (-(a*γ^2*(1-γ^2/(6*m))))*((γ*e/2+(4/5)/R)^2/(R*sizeScale m))*(1/σ'^(r.val+1)) := by
  let B := m-(2*d+1)
  let σ' := √(suffixVariance c B)
  let R := √(v/3-2/4096)
  let a := v*(1-e/2)^2/8
  have hBm : B ≤ m := Nat.sub_le ..
  have hB : 0<(B:ℝ) := by exact_mod_cast (show 0<B by dsimp only [B]; omega)
  have hlab := upper_half_suffix_labels hBm hc hcm
  have H := (suffix_variance_bounds c B (by norm_num : (0:ℝ)≤13/125)
    (fun i hi => ⟨(hlab i hi).1,(hlab i hi).2.1⟩)).1
  have hv : 0 < suffixVariance c B := (by positivity : 0<(13/125)/3*(B:ℝ)^3).trans_le H
  have hσ : 0<σ' := sqrt_pos.mpr hv
  refine ⟨hσ,?_⟩
  have free (j : ℤ) : |rankDifference r j (freeRankMass (c+0) B)| ≤ 1/σ'^(r.val+1) := by
    rw [add_zero,le_div_iff₀ (pow_pos hσ _),mul_comm]
    exact upper_half_first_suffix hm hb hBm hc hcm hσ (sq_sqrt hv.le).symm r hr j
  have hs : (sizeScale m)^2=(m:ℝ)^3 := by dsimp only [sizeScale]; rw [mul_pow,sq_sqrt (Nat.cast_nonneg _)]; ring
  have cap := hγ ▸ far_tilt_square hc hcm
  have Hhit := first_hit_rank_bin ht hc (le_refl (0:ℝ)) hs hγ (by ring : (0:ℝ)=2*0*sizeScale m)
    (by linarith only [cap,Nat.cast_nonneg (α:=ℝ) m]) he hlo hhi r free k
  simp only [rankChange_zero,one_mul,add_zero,zero_pow (by decide : 2≠0),zero_mul,zero_div,zero_sub] at Hhit
  have heq : -(v*(1-e/2)^2*γ*(γ*(1-γ^2/(6*m)))/8) = -(a*γ^2*(1-γ^2/(6*m))) := by dsimp only [a]; ring
  rw [heq] at Hhit
  have hpin := far_pinned_hit hm ht hc hcm hγ hlo hhi hcore
  have hne : r≠2 := by intro h; subst r; norm_num at hr
  unfold firstRankLoss signedRank; rw [ite_eq_right hne]
  exact (le_abs_self _).trans (Hhit.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpin (exp_pos _).le) (by positivity)))

end CentralUnimodality.MarkedExcursion
