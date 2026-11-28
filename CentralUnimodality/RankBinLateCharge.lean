module

public import CentralUnimodality.RankBinLateScale
public import CentralUnimodality.ScaledEventLoss

/-! The recorded late charge bounds the signed loss in the actual ballot
rank law, for each saddle in the row and each of the three orders. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic
open Real

theorem signedCost_cast (r : Fin 3) (d z a b c : ℚ) :
    (signedCost r d z a b c:ℝ)=restoredCost r ((d:ℝ)*z)
      (fun j => if j=0 then (a:ℝ) else if j=1 then (b:ℝ) else (c:ℝ)) := by
  fin_cases r <;> norm_num [signedCost,restoredCost] <;> ring <;> simp

theorem actual_late_charge {curve : Bool} {i m j : ℕ} {c : ℝ}
    (hcheck : checkSigns curve i=true) (h : SaddleAt (saddleBin curve i) m c)
    (hj : meanRank c m=(j+1:ℕ)) (r : Fin 3) :
    let B := saddleBin curve i
    let L := timeCut m B.fraction
    let T := timeCut m lateCut
    let σ := √(suffixVariance c (m-L))
    let P := live c (c*m) L 1
    σ^(r.val+1)/P*signedRank r (j+1:ℕ) (eventSiteMass c m (lateHitEvent m T)) ≤
      ((lateCharge B (shiftRow curve i) r).units:ℝ)/scale := by
  let B := saddleBin curve i
  let row := shiftRow curve i
  let d := lateShift row r
  let a := (B.drift+d/2)*lateCut*(1-lateCut/2)
  let cap := (B.upper+d)/2-a
  let x := d^2*energy/8-a^2/2
  let prob := decay (-x)*(2*cap+(4/5)/rootLo B.fraction)/B.denom
  let cost := signedCost r d B.zhi 19 810 98000
  let L := timeCut m B.fraction
  let T := timeCut m lateCut
  let σ := √(suffixVariance c (m-L))
  let P := live c (c*m) L 1
  let z := (d:ℝ)/(2*sizeScale m)
  have Hcheck := of_decide_eq_true hcheck
  have Hlate := of_decide_eq_true (Hcheck.1 r).1
  change x ≤ 0 ∧ 0 ≤ a ∧ a ≤ 6/25*64 ∧ 0 ≤ cap ∧ cap ≤ 6/25*64 ∧ 0 ≤ d ∧ d ≤ 32 at Hlate
  obtain ⟨hxn,_,ha,hcap,hcu,hd,hd'⟩ := Hlate
  obtain ⟨hg,hgG,hG,hden,_,hZ,_,_,hl,hl'⟩ := checked_bin_data hcheck
  obtain ⟨hL,hLT,hT,_,_,hspan⟩ := cut_geometry h.large hl hl'
  obtain ⟨_,hsig,hP,hPp,_⟩ := bin_actual_scales hcheck h
  have hM : (4096:ℝ) ≤ m := by exact_mod_cast h.large
  have hp : 0<(m:ℝ) := by linarith
  have hs : 0<sizeScale m := mul_pos hp (sqrt_pos.mpr hp)
  have hσ : 0 ≤ σ := sqrt_nonneg _
  have hd₀ : 0 ≤ (d:ℝ) := by exact_mod_cast hd
  have hz : 0 ≤ z := div_nonneg hd₀ (by positivity)
  have hstep : (d:ℝ)=2*z*sizeScale m := by dsimp only [z]; field_simp
  have hscaled : σ*(2*z) ≤ (d:ℝ)*B.zhi := by
    rw [hstep]; linarith only [mul_le_mul_of_nonneg_right hsig (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hz)]
  have hha : lateHeightParameter B.lower d lateCut=(a:ℝ) := by
    change _ = (((B.lower/2*(1-B.lower^2*epsilon/12)+d/2)*lateCut*(1-lateCut/2):ℚ):ℝ)
    dsimp [lateHeightParameter,epsilon]; push_cast; ring
  have hhc : ((B.upper:ℝ)+d)/2-a=(cap:ℝ) := by dsimp only [cap]; push_cast; rfl
  have hg₀ : 0 ≤ (B.lower:ℝ) := by exact_mod_cast hg
  have hgmax : (B.lower:ℝ) ≤ 25 := by exact_mod_cast hgG.trans hG
  have hh₀ : 0 ≤ (lateCut:ℝ) := by norm_num [lateCut]
  have hh₁ : (lateCut:ℝ) ≤ 1 := by norm_num [lateCut]
  have hhT : (lateCut:ℝ)*m ≤ T := Nat.le_ceil _
  have ha' : (a:ℝ) ≤ (6/25)*64 := by simpa using (Rat.cast_le (K:=ℝ)).mpr ha
  have hc' : (cap:ℝ) ≤ (6/25)*64 := by simpa using (Rat.cast_le (K:=ℝ)).mpr hcu
  have U := late_rank_loss h.large hL hLT hT h.positive.le hz hg₀ h.lower h.upper hstep
    (by exact_mod_cast hd') (by linarith only [pow_le_pow_left₀ hg₀ hgmax 2]) hh₀ hh₁ hhT
    (hha ▸ ha') (by rw [hha,hhc]; exact_mod_cast hcap) (by rwa [hha,hhc]) hj
  have hroot : 0<rootLo B.fraction := by
    cases curve
    · change 0<rootLo (1/10); decide +kernel
    · change 0<rootLo (1/14); decide +kernel
  have hl₀ : 0 ≤ B.fraction := by linarith only [hl]
  have hZr : (B.zhi:ℝ) ≤ 259/1000 := by simpa using (Rat.cast_le (K:=ℝ)).mpr hZ
  have hs' : σ ≤ 259/1000*sizeScale m := hsig.trans (by linarith only [mul_le_mul_of_nonneg_left hZr hs.le])
  let A := lateRankAllowance m L T B.lower B.upper d lateCut
  have hA (k : Fin 3) : σ^(k.val+1)/P*A k ≤ (prob:ℝ)*lateUniformLimit k :=
    late_scale_to_bin h.large hspan hσ hs' hl₀ hroot (Nat.le_ceil _) hden hP hha hcap hhc rfl hxn k
  have hdec := (exp_pos _).le.trans (decay_upper (neg_nonneg.mpr hxn))
  have hdec' : 0 ≤ decay (-x) := by exact_mod_cast hdec
  have hprob : 0 ≤ prob := by dsimp only [prob]; positivity
  have hcaste : (cost:ℝ)=restoredCost r ((d:ℝ)*B.zhi) lateUniformLimit := by
    rw [show cost=signedCost r d B.zhi 19 810 98000 from rfl,signedCost_cast]
    congr 1
  have H := signed_of_neighbors _ _ (eventSiteMass_rank c m (lateHitEvent m T)) j A (2*z) U r
  have H' := scale_restored_cost hσ (by positivity : 0 ≤ 2*z) hscaled
    (by exact_mod_cast hprob : 0 ≤ (prob:ℝ)) A lateUniformLimit
    (fun k => by fin_cases k <;> norm_num [lateUniformLimit]) hA r
  change σ^(r.val+1)/P*_ ≤ _
  apply (mul_le_mul_of_nonneg_left H (by positivity : 0 ≤ σ^(r.val+1)/P)).trans
  apply H'.trans
  rw [← hcaste,← Rat.cast_mul]
  have hch := (Rat.cast_le (K:=ℝ)).mpr (charge_upper (prob*cost))
  change _ ≤ (((⌈(scale:ℚ)*prob*cost⌉₊:ℕ):ℝ)/(scale:ℝ))
  simpa [charge,mul_assoc] using hch

end CentralUnimodality.MarkedExcursion.BinArithmetic
