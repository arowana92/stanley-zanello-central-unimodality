module

public import CentralUnimodality.MarkedLowIntegral
public import CentralUnimodality.LateUniformBudget

/-! Above scaled frequency 4096, three quarters of the available
two-thirds-power exponent pay a fixed factor exp(-10.5). The remaining
integral is an eightfold dilation of the previous inner arc. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.FrequencyGrid
open Real MeasureTheory Set BinArithmetic

noncomputable def arcScale (d : ℝ) := (14/25)/(17/2)*d

theorem scaled_cut_decay {m : ℕ} {d θ : ℝ} (hm : 0<m) (hd : (837/1000)*(m:ℝ)≤d)
    (hcut : 4096≤sizeScale m*|θ|) :
    exp (-(innerPairRate |θ|)*d) ≤ exp (-(21/2))*exp (-(arcScale d/4)*|θ|^(2/3:ℝ)) := by
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hpow : (sizeScale m)^(2/3:ℝ)=m := by
    rw [sizeScale,sqrt_eq_rpow,← rpow_one_add' hm'.le (by norm_num : (1:ℝ)+1/2≠0),← rpow_mul hm'.le]
    norm_num
  have H := Real.rpow_le_rpow (by norm_num : (0:ℝ)≤4096) hcut (by norm_num : (0:ℝ)≤2/3)
  rw [Real.mul_rpow (by dsimp [sizeScale]; positivity) (abs_nonneg _),hpow] at H
  have hbase : (4096:ℝ)^(2/3:ℝ)=256 := by
    rw [show (4096:ℝ)=(16:ℝ)^(3:ℝ) by norm_num,← rpow_mul (by norm_num)]; norm_num
  rw [hbase] at H
  rw [← exp_add,exp_le_exp]
  have hd' := mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg (abs_nonneg θ) (2/3:ℝ))
  dsimp only [arcScale,innerPairRate]
  linarith only [H,hd']

noncomputable def outerBand (d : ℝ) (s : Fin 4) (r : ℕ) (θ : ℝ) :=
  exp (-(pairRate s false:ℝ)*d)*lateOuterKernel s r θ

theorem outer_nonneg (d : ℝ) (s : Fin 4) (r : ℕ) (θ : ℝ) : 0≤outerBand d s r θ := by
  apply mul_nonneg (exp_pos _).le
  unfold lateOuterKernel; by_cases h : |θ|∈Icc (outerLo s) (outerHi s) <;> simp [h]

noncomputable def highEnvelope (d : ℝ) (r : ℕ) (θ : ℝ) :=
  2*(exp (-(21/2))*lateInnerKernel (arcScale d/4) r θ+∑ s : Fin 4, outerBand d s r θ)

theorem high_nonneg (d : ℝ) (r : ℕ) (θ : ℝ) : 0≤highEnvelope d r θ := by
  have h := Finset.sum_nonneg (s:=Finset.univ) (fun i _ => outer_nonneg d i r θ)
  dsimp only [highEnvelope,lateInnerKernel]; positivity

private theorem inner_dilate {a : ℝ} (ha : 0<a) (r : ℕ) :
    (a/4)^(-3*((r:ℝ)+1)/2:ℝ)=8^(r+1)*a^(-3*((r:ℝ)+1)/2:ℝ) := by
  let y := 3*((r:ℝ)+1)/2
  have H : (4:ℝ)^y=8^(r+1) := by
    rw [show (4:ℝ)=(2:ℝ)^(2:ℝ) by norm_num,← rpow_mul (by norm_num),
      show (8:ℝ)=(2:ℝ)^(3:ℝ) by norm_num,← rpow_natCast _ (r+1),← rpow_mul (by norm_num)]
    push_cast; dsimp [y]; congr 1; ring
  change (a/4)^(-3*((r:ℝ)+1)/2:ℝ)=_
  rw [show -3*((r:ℝ)+1)/2= -y by dsimp [y]; ring,div_rpow ha.le (by norm_num),
    rpow_neg (by norm_num : (0:ℝ)≤4),H,div_inv_eq_mul,mul_comm]

/-- The three normalized moments of the high-frequency envelope. -/
theorem high_integral {m : ℕ} {d σ : ℝ} (hm : 4096≤m) (hd : (837/1000)*(m:ℝ)≤d)
    (hσ : 0≤σ) (hσ' : σ≤(259/1000)*sizeScale m) (r : Fin 3) :
    Integrable (highEnvelope d r) ∧ σ^(r.val+1)*(∫ θ, highEnvelope d r θ) ≤
      (2*π)*(exp (-(21/2))*8^(r.val+1)*lateUniformLimit r+(1/2)/π) := by
  let a := arcScale d
  have hm' : (4096:ℝ)≤m := by exact_mod_cast hm
  have ha : 0<a := by dsimp [a,arcScale]; linarith only [hm',hd]
  have hi := late_inner_integral (show 0<a/4 by positivity) r.val
  have I (s : Fin 4) : Integrable (outerBand d s r) := (late_outer_integral s r).1.const_mul _
  have hsum := integrable_finsetSum Finset.univ (fun i _ => I i)
  refine ⟨((hi.1.const_mul _).add hsum).const_mul _,?_⟩
  let g := 3*a^(-3*((r.val:ℝ)+1)/2)*Gamma (3*((r.val:ℝ)+1)/2)
  let v (s : Fin 4) := exp (-(pairRate s false:ℝ)*d)*(2*(outerHi s^(r.val+1)-outerLo s^(r.val+1))/((r.val:ℝ)+1))
  have hv (s : Fin 4) : (∫ θ, outerBand d s r θ)=v s := by
    dsimp [outerBand,v]; rw [integral_const_mul,(late_outer_integral s r).2]
  have hpos : 0≤∑ s : Fin 4, v s := Finset.sum_nonneg (fun s _ => hv s ▸ integral_nonneg (outer_nonneg d s r))
  have V : σ^(r.val+1)*(∑ s : Fin 4, v s)≤1/2 := by
    rw [Finset.mul_sum]
    apply (Finset.sum_le_sum (fun s _ => late_scaled_outer s r hm' hd hσ hσ')).trans
    norm_num
  have hb := late_uniform_budget hm' hd hσ hσ' r
  change σ^(r.val+1)*((g+∑ s : Fin 4, v s)/π)≤lateUniformLimit r at hb
  have hg : σ^(r.val+1)*g≤π*lateUniformLimit r := by
    rw [← mul_div_assoc,div_le_iff₀ pi_pos] at hb
    linarith only [hb,mul_nonneg (pow_nonneg hσ (r.val+1)) hpos]
  change σ^(r.val+1)*(∫ θ, 2*(exp (-(21/2))*lateInnerKernel (a/4) r θ+∑ s : Fin 4, outerBand d s r θ))≤_
  rw [integral_const_mul,integral_add (hi.1.const_mul _) hsum,integral_const_mul,hi.2,inner_dilate ha,
    integral_finsetSum _ (fun i _ => I i)]
  simp_rw [hv]
  rw [show (2*π)*(exp (-(21/2))*8^(r.val+1)*lateUniformLimit r+(1/2)/π) =
    2*(exp (-(21/2))*8^(r.val+1)*(π*lateUniformLimit r)+1/2) by field_simp]
  have H := mul_le_mul_of_nonneg_left hg (by positivity : 0≤exp (-(21/2:ℝ))*8^(r.val+1))
  dsimp only [g] at H
  linarith only [H,V]

end CentralUnimodality.MarkedExcursion.FrequencyGrid
