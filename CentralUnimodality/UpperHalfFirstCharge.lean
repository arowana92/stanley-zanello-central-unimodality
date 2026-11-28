module

public import CentralUnimodality.UpperHalfFirstSite
public import CentralUnimodality.UpperHalfHitScale
public import CentralUnimodality.RankBinFirstCharge

/-! A common rational charge for mass and forward difference in each
of the seven time intervals. Both endpoints are rounded up in time. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic
open Real

theorem far_first_charge {m : ℕ} (hm : 4096≤m) {c : ℝ} (hc : 0<c) (hcm : c*m≤1)
    (hγ : 119/5≤2*c*sizeScale m) (r : Fin 3) (hr : r.val≤1) (k : ℤ) (i : Fin 7) :
    let L := timeCut m (1/10)
    let σ := √(suffixVariance c (m-L))
    let P := live c (c*m) L 1
    σ^(r.val+1)/P*earlyRankLoss c m (timeCut m (farCut i)) (timeCut m (farCut (i+1:ℕ))) r k ≤
      (charge (farTimeCost i):ℝ) := by
  let v := farCut i
  let w := farCut (i+1:ℕ)
  let e := w+epsilon
  let x := v/3-2*epsilon
  let R := rootLo x
  let a := v*(1-e/2)^2/8
  let y := a*(19/20)*farBase^2
  let W := e/2+(4/5)/(R*farBase)
  let L := timeCut m (1/10)
  let σ := √(suffixVariance c (m-L))
  let P := live c (c*m) L 1
  let γ := 2*c*sizeScale m
  have ⟨hv,hvw,hw,he,hR,hcore,ha⟩ := far_time_data i
  change e<1 at he; change 0<R at hR; change 1/160≤a at ha
  have hp : 0<(m:ℝ) := by exact_mod_cast (show 0<m by omega)
  have hM : (4096:ℝ) ≤ m := by exact_mod_cast hm
  have hE₀ : 0≤e := by dsimp only [e,w,epsilon]; linarith only [hv,hvw]
  have hW : 0≤W := by dsimp only [W,farBase]; positivity
  have hY : 0≤y := by dsimp only [y,farBase]; linarith only [ha]
  have hD := decay_upper hY
  have hC : 0 ≤ decay y := by exact_mod_cast (exp_pos _).le.trans hD
  have hcost : 0 ≤ farHitCost i := by
    change 0 ≤ (farBase/farDrift)*W^2/R*decay y/(1-e)^3
    have hex := sub_pos.mpr he
    dsimp only [farBase,farDrift]; positivity
  have ⟨_,hP,hσlo,_,_⟩ := far_prefix_scales hm hc hcm hγ
  have hσ : 0<σ := (mul_pos (by norm_num : (0:ℝ)<79/500) (mul_pos hp (sqrt_pos.mpr hp))).trans_le hσlo
  have hcuts := cut_geometry hm (by norm_num : (1/14:ℚ)≤1/10) (le_refl (1/10:ℚ))
  have hL : (L:ℝ) ≤ (1/10+1/4096)*m := by simpa [L,epsilon] using hcuts.2.2.2.2.1
  have hden := mul_le_mul_of_nonneg_right ((upper_half_drift (mul_nonneg hc.le hp.le) hcm).trans
    (far_prefix_survival hc hp hcm hL)) (sqrt_nonneg (m:ℝ))
  have hd : (19/50)*γ ≤ P*√m := by dsimp only [P,γ,sizeScale]; linarith only [hden]
  have Hsum := scaled_time_sum hm hv hvw c r k hσ hP ((Rat.cast_nonneg (K:=ℝ)).mpr hcost) (fun d H₀ H₁ => ?_)
  · exact Hsum.trans (by rw [← Rat.cast_mul]; exact (Rat.cast_le (K:=ℝ)).mpr (charge_upper _))
  obtain ⟨hl,hh,hx,he₀,he₁,ht⟩ := hit_cut_geometry hm hv hvw hw (show e=w+epsilon from rfl) H₀ H₁ rfl hcore
  have hb : 2*d+1+255 ≤ m := by
    have H : 2*(d:ℝ)+1+255≤m := by linarith only [hh,hM,mul_le_mul_of_nonneg_right he₁ hp.le]
    exact_mod_cast H
  have hstart : (1/10:ℚ)≤v := le_min (by norm_num [lateCut]) (le_add_of_nonneg_right (by positivity))
  have hLt : L ≤ 2*d+1 := (Nat.ceil_mono (mul_le_mul_of_nonneg_right ((Rat.cast_le (K:=ℝ)).mpr hstart) hp.le)).trans H₀.le
  let B := m-(2*d+1)
  let σ' := √(suffixVariance c B)
  let t := √((v:ℝ)/3-2/4096)
  let E := exp (-((a:ℝ)*γ^2*(1-γ^2/(6*m))))
  obtain ⟨hσ',HX⟩ := far_first_site hm ht (by omega) hc.le hcm (show γ=2*c*sizeScale m from rfl)
    (by linarith only [he₁]) hl hh hx r hr k
  have ha' : (a:ℝ)=(v:ℝ)*(1-(e:ℝ)/2)^2/8 := by dsimp only [a]; push_cast; rfl
  have hex : 0 ≤ x := by change 80≤4096*x at hcore; linarith only [hcore]
  have ht' : (R:ℝ)≤t := by
    apply (root_enclosure hex).1.trans_eq
    dsimp only [t,x,epsilon]; push_cast; norm_num
  have hr' : 0<(R:ℝ) := by exact_mod_cast hR
  have hw' : (W:ℝ)=(e:ℝ)/2+(4/5)/((R:ℝ)*(119/5)) := by dsimp only [W,farBase]; push_cast; rfl
  have hwidth := far_first_width (by norm_num : (0:ℝ)<119/5) hγ hr' ht' (e:=(e:ℝ))
  rw [← hw'] at hwidth
  have ha₀ : (1/160:ℝ) ≤ (a:ℝ) := by simpa using (Rat.cast_le (K:=ℝ)).mpr ha
  have hdec := far_hit_decay hM hγ (far_tilt_square hc.le hcm) ha₀
  have hy : (y:ℝ)=(a:ℝ)*(19/20)*(119/5)^2 := by dsimp only [y,farBase]; push_cast; rfl
  rw [hy] at hD
  have hE : E*γ ≤ (119/5)*(decay y:ℝ) :=
    (mul_comm E γ).le.trans (hdec.trans (mul_le_mul_of_nonneg_left hD (by norm_num)))
  have hratio := far_suffix_ratio (by omega : 0<m) hLt ht he₀ (by simpa using (Rat.cast_lt (K:=ℝ)).mpr he)
    (by exact_mod_cast hh) hσ.le hσ' (sq_sqrt (sqrt_pos.mp hσ).le).symm (sq_sqrt (sqrt_pos.mp hσ').le).symm r hr
  have H := far_hit_scale (r.val+1) hp hP hσ.le hσ' hr' ht' (by norm_num : (0:ℝ)<119/5)
    hγ (by norm_num : (0:ℝ)<19/50) (exp_pos _).le
    (show 0≤γ*(e:ℝ)/2+(4/5)/t by
      have htpos := hr'.trans_le ht'
      have hγpos : 0≤γ := (by norm_num : (0:ℝ)≤119/5).trans hγ
      positivity)
    hwidth hd hE hratio (by change firstRankLoss c m (2*d+1) r k ≤ E*_*(1/σ'^(r.val+1)); dsimp only [E]; rw [ha']; exact HX)
  apply H.trans_eq
  change _ = (((farBase/farDrift)*W^2/R*decay y/(1-e)^3:ℚ):ℝ)
  dsimp only [farBase,farDrift]; push_cast; ring

end CentralUnimodality.MarkedExcursion.BinArithmetic
