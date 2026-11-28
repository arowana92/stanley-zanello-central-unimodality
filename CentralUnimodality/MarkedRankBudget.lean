module

public import CentralUnimodality.MarkedHighIntegral

/-! Size-uniform bounds for the mass and the two discrete differences
of the discarded late ballot event, at every integer rank. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.FrequencyGrid
open Real MeasureTheory Set BinArithmetic

def markedLimit (r : Fin 3) : ℚ := if r=0 then 18/5 else if r=1 then 109/2 else 3800

private theorem decay_number : exp (-(21/2:ℝ))≤3/100000 := by
  have H := pow_le_pow_left₀ (exp_pos _).le (upperNegExp_sound (by decide +kernel : (0:ℚ)≤21/4)) 2
  rw [← exp_nat_mul] at H
  have K : upperNegExp (21/4)^2≤(3/100000:ℚ) := by decide +kernel
  have h := (Rat.cast_le (K:=ℝ)).mpr K
  push_cast at h H
  exact (show exp (-(21/2:ℝ))=exp (2* -(21/4:ℝ)) by congr 1; ring).le.trans (H.trans h)

private theorem marked_scale {m : ℕ} {d σ : ℝ} (hm : 4096≤m) (hd : (837/1000)*(m:ℝ)≤d)
    (hσ : 0≤σ) (hσ' : σ≤(259/1000)*sizeScale m) (r : Fin 3) :
    σ^(r.val+1)*((∫ θ, lowEnvelope (sizeScale m) r θ)+(∫ θ, highEnvelope d r θ)) ≤ (2*π)*(markedLimit r:ℝ) := by
  have hm' : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  let s := sizeScale m
  have hs : 0<s := mul_pos hm' (sqrt_pos.mpr hm')
  have he : (0:ℝ)≤(lowLimit r:ℝ) := by fin_cases r <;> norm_num [lowLimit]
  have hrat : σ/s ≤ 259/1000 := (div_le_iff₀ hs).mpr hσ'
  have hz := pow_le_pow_left₀ (div_nonneg hσ hs.le) hrat (r.val+1)
  rw [div_pow] at hz
  have hL := (mul_le_mul_of_nonneg_left (low_integral hs r).2 (pow_nonneg hσ (r.val+1))).trans
    (by convert mul_le_mul_of_nonneg_right hz (mul_nonneg (by norm_num : (0:ℝ)≤2) he) using 1; ring)
  have hH := (high_integral hm hd hσ hσ' r).2
  have hc : 0≤lateUniformLimit r := by fin_cases r <;> norm_num [lateUniformLimit]
  have hdec := mul_le_mul_of_nonneg_right decay_number (mul_nonneg (by positivity : (0:ℝ)≤8^(r.val+1)) hc)
  have hi : σ^(r.val+1)*(∫ θ, highEnvelope d r θ) ≤
      2*π*(3/100000*8^(r.val+1)*lateUniformLimit r)+1 := by
    have hx := mul_le_mul_of_nonneg_left hdec (by positivity : (0:ℝ)≤2*π)
    rw [mul_add,show 2*π*((1/2)/π)=1 by field_simp] at hH
    linarith only [hH,hx]
  rw [mul_add]
  apply (add_le_add hL hi).trans
  fin_cases r <;> norm_num [lowLimit,markedLimit,lateUniformLimit] <;> linarith only [pi_gt_d2]

private theorem outer_cover {x : ℝ} (hx : 1/8≤x) (hπ : x≤π) :
    ∃ j : Fin 4, outerLo j≤x ∧ x≤outerHi j := by
  by_cases h₁ : x≤9/50
  · exact ⟨0,hx,h₁⟩
  by_cases h₂ : x≤1/4
  · exact ⟨1,le_of_not_ge h₁,h₂⟩
  by_cases h₃ : x≤1/2
  · exact ⟨2,le_of_not_ge h₂,h₃⟩
  exact ⟨3,le_of_not_ge h₃,hπ⟩

theorem marked_rank_budget_of_row {v b U R C σ : ℝ} {m : ℕ} (hm : 4096≤m)
    (hv : 0≤v) (hb' : b≤6/25) (hU' : U≤6/25) (hcap : v*m-b≤U) (hR : 0≤R) (hC : 0≤C)
    (hrow : ∀ θ : ℝ, R*‖lateRankCharacter v θ m (timeCut m (37/40))‖ ≤
      C*endpointNorm (wallRow v (v*m-b) m θ 0 (timeCut m (37/40))))
    (hσ : 0≤σ) (hσ' : σ≤(259/1000)*sizeScale m) (r : Fin 3) (j : ℤ) :
    let L := timeCut m (3/40)
    let T := timeCut m (37/40)
    σ^(r.val+1)*R*|rankDifference r j (eventSiteMass v m (lateHitEvent m T))| ≤
      C*live v (v*m-b) L 1*(markedLimit r:ℝ) := by
  let L := timeCut m (3/40)
  let T := timeCut m (37/40)
  let d : ℝ := (T-L:ℕ)
  let s := sizeScale m
  let N := live v (v*m-b) L 1
  have hN : 0≤N := live_nonneg ..
  have hp : 0<m := by omega
  have hmp : (0:ℝ)<m := by exact_mod_cast hp
  have hs : 0<s := mul_pos hmp (sqrt_pos.mpr hmp)
  have hL₂ : (L:ℝ)<(3/40:ℝ)*m+1 := by simpa [L,timeCut] using Nat.ceil_lt_add_one (by positivity : 0≤(3/40:ℝ)*m)
  have hT₁ : (37/40:ℝ)*m≤T := by simpa [T,timeCut] using Nat.le_ceil ((37/40:ℝ)*m)
  have hT₂ : (T:ℝ)<(37/40:ℝ)*m+1 := by simpa [T,timeCut] using Nat.ceil_lt_add_one (by positivity : 0≤(37/40:ℝ)*m)
  have hM : (4096:ℝ)≤m := by exact_mod_cast hm
  have hLT : L≤T := by exact_mod_cast (show (L:ℝ)≤T by linarith)
  have hTm : T≤m := by exact_mod_cast (show (T:ℝ)≤m by linarith)
  have hd : (837/1000)*(m:ℝ)≤d := by dsimp [d]; rw [Nat.cast_sub hLT]; linarith
  let G (θ : ℝ) := N*(lowEnvelope s r θ+highEnvelope d r θ)
  let W (θ : ℝ) := endpointNorm (wallRow v (v*m-b) m θ 0 T)
  have hI := (low_integral hs r).1.add (high_integral hm hd hσ hσ' r).1
  have hx (θ : ℝ) (hθ : θ∈Ioc (-π) π) : W θ*|θ|^r.val ≤ G θ := by
    have hlow := low_nonneg s r.val θ
    have hhigh := high_nonneg d r.val θ
    by_cases hsmall : s*|θ|≤4096
    · exact (wall_low_dominates hm hv hb' hU' hcap hsmall r.val).trans
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hhigh) hN)
    apply le_trans _ (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hlow) hN)
    have ⟨hi,ho⟩ := late_wall_arcs hv hb' hU' θ hLT hTm hcap
    let A := exp (-(21/2))*lateInnerKernel (arcScale d/4) r θ
    let O := ∑ x : Fin 4, outerBand d x r θ
    have hA : 0≤A := by dsimp only [A,lateInnerKernel]; positivity
    have hO : 0≤O := Finset.sum_nonneg (fun i _ => outer_nonneg d i r θ)
    change _ ≤ N*(2*(A+O))
    by_cases hθ' : |θ|≤1/8
    · have E := scaled_cut_decay hp hd (le_of_not_ge hsmall)
      have H := mul_le_mul_of_nonneg_left E (by positivity : 0≤N*2*|θ|^r.val)
      have S := mul_le_mul_of_nonneg_right (hi hθ') (by positivity : 0≤|θ|^r.val)
      change W θ*|θ|^r.val≤N*(2*exp (-(innerPairRate |θ|)*d))*|θ|^r.val at S
      dsimp only [A,lateInnerKernel]; linarith only [S,H,mul_nonneg hN hO]
    · obtain ⟨k,h₁,h₂⟩ := outer_cover (le_of_not_ge hθ') (abs_le.mpr ⟨hθ.1.le,hθ.2⟩)
      have hk := Finset.single_le_sum (s:=Finset.univ) (f:=fun i => outerBand d i r θ)
        (fun i _ => outer_nonneg d i r θ) (Finset.mem_univ k)
      change outerBand d k r θ≤O at hk
      rw [outerBand,lateOuterKernel,Set.indicator_of_mem (show |θ|∈Icc _ _ from ⟨h₁,h₂⟩)] at hk
      have S := mul_le_mul_of_nonneg_right (ho k h₁ h₂) (by positivity : 0≤|θ|^r.val)
      change W θ*|θ|^r.val≤N*(2*exp (-(pairRate k false:ℝ)*d))*|θ|^r.val at S
      linarith only [S,mul_le_mul_of_nonneg_left hk hN,mul_nonneg hN hA]
  have H := late_difference_integral v m T hR r j ((hI.const_mul N).const_mul C)
    (fun θ => mul_nonneg hC (mul_nonneg hN (add_nonneg (low_nonneg s r.val θ) (high_nonneg d r.val θ)))) (by
      intro θ hθ
      have H₁ := mul_le_mul_of_nonneg_right (hrow θ) (by positivity : 0≤|θ|^r.val)
      change R*‖lateRankCharacter v θ m T‖*|θ|^r.val≤C*W θ*|θ|^r.val at H₁
      exact H₁.trans ((mul_assoc C (W θ) _).le.trans (mul_le_mul_of_nonneg_left (hx θ hθ) hC)))
  change _≤∫ θ, C*G θ at H
  dsimp only [G] at H
  rw [integral_const_mul,integral_const_mul,integral_add (low_integral hs r).1 (high_integral hm hd hσ hσ' r).1] at H
  have H₁ := mul_le_mul_of_nonneg_left H (pow_nonneg hσ (r.val+1))
  have H₂ := mul_le_mul_of_nonneg_left (marked_scale hm hd hσ hσ' r) (mul_nonneg hC hN)
  apply le_of_mul_le_mul_left (a:=2*π) _ (by positivity)
  change 2*π*(σ^(r.val+1)*R*_)≤2*π*(C*N*(markedLimit r:ℝ))
  linarith only [H₁,H₂]

end CentralUnimodality.MarkedExcursion.FrequencyGrid
