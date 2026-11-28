module

public import CentralUnimodality.RankBinFirstScale
public import CentralUnimodality.RankBinFirstGeometry
public import CentralUnimodality.RankBinLateCharge

/-! Apply the certified shift at every possible original first hit in a
rounded time bin and sum over its odd times. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic
open Real

theorem scaled_time_sum {m : ℕ} (hm : 4096 ≤ m) {v w : ℚ} (hv : 0 ≤ v) (hvw : v ≤ w)
    (c : ℝ) (r : Fin 3) (j : ℤ) {σ P C : ℝ} (hσ : 0<σ) (hP : 0<P) (hC : 0 ≤ C)
    (H : ∀ k : ℕ, timeCut m v < 2*k+1 → 2*k+1 ≤ timeCut m w →
      σ^(r.val+1)/(P/m)*firstRankLoss c m (2*k+1) r j ≤ C) :
    σ^(r.val+1)/P*earlyRankLoss c m (timeCut m v) (timeCut m w) r j ≤
      (((w-v)/2+epsilon:ℚ):ℝ)*C := by
  have hp : 0<(m:ℝ) := by exact_mod_cast (show 0<m by omega)
  let A := σ^(r.val+1)/P
  have hA : 0<A := by dsimp [A]; positivity
  have eq : σ^(r.val+1)/(P/m)=A*m := by dsimp [A]; field_simp
  have bound := early_loss_bin_bound hm ((Rat.cast_nonneg (K:=ℝ)).mpr hv) ((Rat.cast_le (K:=ℝ)).mpr hvw)
    c r j (div_nonneg hC (mul_pos hA hp).le) (fun k h₀ h₁ => (le_div_iff₀ (mul_pos hA hp)).mpr
      (by have hh := H k h₀ h₁; rw [eq,mul_comm] at hh; exact hh))
  apply (mul_le_mul_of_nonneg_left bound hA.le).trans_eq
  dsimp only [epsilon]; push_cast; field_simp

theorem actual_first_charge {curve : Bool} {i m j : ℕ} {c : ℝ}
    (hcheck : checkSigns curve i=true) (h : SaddleAt (saddleBin curve i) m c)
    (hj : meanRank c m=(j+1:ℕ)) (r : Fin 3) (t : Fin 42) :
    let B := saddleBin curve i
    let L := timeCut m B.fraction
    let σ := √(suffixVariance c (m-L))
    let P := live c (c*m) L 1
    σ^(r.val+1)/P*earlyRankLoss c m (timeCut m (cutAt B t)) (timeCut m (cutAt B (t+1:ℕ))) r (j+1:ℕ) ≤
      ((firstCharge B (shiftRow curve i) t r).units:ℝ)/scale := by
  let B := saddleBin curve i
  let row := shiftRow curve i
  let v := cutAt B t
  let w := cutAt B (t+1:ℕ)
  let e := w+epsilon
  let d := firstShift row t r
  let lam := B.upper+d
  let β := lam*e/4
  let chunk := v/3-2*epsilon
  let root := rootLo chunk
  let F := 2*β+(4/5)/root
  let lo := rootLo ((1-(lam*(1-v)/128)^2)*(1-e)^3/12)
  let x := d^2*energy/8-v*(1-e/2)^2*(B.lower+d)*(B.lower*(1-B.lower^2*epsilon/6)+d)/8
  let prob := decay (-x)*(1/2+β/128)*F^2/(root*B.denom)
  let ratio := B.zhi/lo
  let cost := signedCost r d B.zhi ((23/50)*ratio) ((23/50)*ratio^2) ((14/25)*ratio^3)
  let L := timeCut m B.fraction
  let σ := √(suffixVariance c (m-L))
  let P := live c (c*m) L 1
  let z := (d:ℝ)/(2*sizeScale m)
  let γ := 2*c*sizeScale m
  by_cases heq : v=w
  · change _*earlyRankLoss c m (timeCut m v) (timeCut m w) _ _ ≤ _
    rw [heq]; simp only [earlyRankLoss,Nat.sub_self,Finset.range_zero,Finset.sum_empty,mul_zero]
    positivity
  have Hcheck := of_decide_eq_true hcheck
  have HH := ((Hcheck.1 r).2 t)
  change (firstCharge B row t r).admissible=true at HH
  unfold firstCharge at HH
  rw [ite_eq_right heq] at HH
  have had := of_decide_eq_true HH
  change x≤0 ∧ 0<root ∧ 0<lo ∧ 80≤4096*chunk ∧ 0≤d ∧ d≤32 ∧ lam≤57 at had
  obtain ⟨hxn,hroot,hlo,hcore,hd,hd',hcap⟩ := had
  obtain ⟨hg,hgG,hG,hden,hZ,_,_,_,hl,_⟩ := checked_bin_data hcheck
  obtain ⟨hσlow,hsig,hP,hPp,_⟩ := bin_actual_scales hcheck h
  obtain ⟨hv,hvw,hw⟩ := cutAt_bounds (show 0≤B.fraction by linarith only [hl]) t
  have hM : (4096:ℝ) ≤ m := by exact_mod_cast h.large
  have hp : 0<(m:ℝ) := by linarith
  have hs : 0<sizeScale m := mul_pos hp (sqrt_pos.mpr hp)
  have hσ : 0<σ := (mul_pos hs (by exact_mod_cast hZ)).trans_le hσlow
  have hZhi : 0<(B.zhi:ℝ) := pos_of_mul_pos_right (hσ.trans_le hsig) hs.le
  have hZh : 0<B.zhi := by exact_mod_cast hZhi
  have hd₀ : 0 ≤ (d:ℝ) := by exact_mod_cast hd
  have hz : 0 ≤ z := div_nonneg hd₀ (by positivity)
  have hstep : (d:ℝ)=2*z*sizeScale m := by dsimp only [z]; field_simp
  have hscaled : σ*(2*z) ≤ (d:ℝ)*B.zhi := by
    rw [hstep]; linarith only [mul_le_mul_of_nonneg_right hsig (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hz)]
  have he₀ : 0≤e := by dsimp only [e,epsilon]; linarith only [hv,hvw]
  have hlam : 0≤lam := add_nonneg (hg.trans hgG) hd
  have hβ : 0≤β := by dsimp only [β]; positivity
  have hdec := (exp_pos _).le.trans (decay_upper (neg_nonneg.mpr hxn))
  have hdec' : 0 ≤ decay (-x) := by exact_mod_cast hdec
  have hprob : 0≤prob := by dsimp only [prob]; positivity
  have hratio : 0 ≤ ratio := div_nonneg hZh.le hlo.le
  have hcost : 0≤cost := by
    dsimp only [cost,signedCost]; split_ifs <;> positivity
  have Hsum := scaled_time_sum h.large hv hvw c r (j+1:ℕ) hσ hPp
    ((Rat.cast_nonneg (K:=ℝ)).mpr (mul_nonneg hprob hcost)) (fun k H₀ H₁ => ?_)
  · apply Hsum.trans
    rw [← Rat.cast_mul]
    unfold firstCharge; rw [ite_eq_right heq]
    let count := (w-v)/2+epsilon
    change _ ≤ (((⌈(scale:ℚ)*(count*(1/2+β/128)*F^2*decay (-x)/(root*B.denom))*cost⌉₊:ℕ):ℝ)/scale)
    have eq : (scale:ℚ)*(count*(1/2+β/128)*F^2*decay (-x)/(root*B.denom))*cost=scale*(count*(prob*cost)) := by dsimp only [prob]; ring
    rw [eq]
    simpa [charge,count,v,w] using (Rat.cast_le (K:=ℝ)).mpr (charge_upper (count*(prob*cost)))
  obtain ⟨h₀,h₁,h₂,_,h₄,ht⟩ := hit_cut_geometry h.large hv hvw hw (show e=w+epsilon from rfl) H₀ H₁ rfl hcore
  have hlam' : (lam:ℝ)=(B.upper:ℝ)+d := Rat.cast_add ..
  have h57 : (B.upper:ℝ)+d ≤ 57 := hlam' ▸ (by exact_mod_cast hcap : (lam:ℝ)≤57)
  have hS := hit_suffix_scale h.large h.positive.le hz (show γ=2*c*sizeScale m from rfl) hstep h.upper h57
    hv hvw hw (show e=w+epsilon from rfl) h₀ h₁ ht hlam' (show lo=_ from rfl)
  have H := pinned_rank_loss h.large h.positive.le hz (show γ=2*c*sizeScale m from rfl) hstep
    (by linarith only [h.upper,h57,show γ=2*c*sizeScale m from rfl]) (by exact_mod_cast hd') h₄ h₀ h₁ h₂ hj
  let U := pinnedRankAllowance m k c z γ d v e
  let A := fun q : Fin 3 => shortSuffixLimit q*(ratio:ℝ)^(q.val+1)
  have hA (q : Fin 3) : 0 ≤ A q := by
    have hh : 0 ≤ (ratio:ℝ) := by exact_mod_cast hratio
    have hl' : 0 ≤ shortSuffixLimit q := by fin_cases q <;> norm_num [shortSuffixLimit]
    exact mul_nonneg hl' (pow_nonneg hh _)
  have hraw (q : Fin 3) : σ^(q.val+1)/(P/m)*U q ≤ (prob:ℝ)*A q :=
    first_scale_to_bin h.large hg h.lower h.upper hG hd hv he₀ rfl rfl hroot
      (show 0 ≤ chunk by linarith only [hcore]) rfl rfl rfl hxn hden hP hlo hσ.le hsig hS q
  have HH' := signed_of_neighbors _ _ (fun k' => prefixEventSiteMass_rankEvent c m (2*k+1) k' _) j U (2*z) H r
  have Hscaled := scale_restored_cost hσ.le (by positivity : 0 ≤ 2*z) hscaled
    (by exact_mod_cast hprob : 0 ≤ (prob:ℝ)) U A hA hraw r
  apply (mul_le_mul_of_nonneg_left HH' (by change 0 ≤ σ^(r.val+1)/(P/m); positivity)).trans
  apply Hscaled.trans_eq
  rw [Rat.cast_mul]; congr 1
  dsimp only [cost]; rw [signedCost_cast]; congr 1
  funext q; fin_cases q <;> norm_num [A,shortSuffixLimit]

end CentralUnimodality.MarkedExcursion.BinArithmetic
