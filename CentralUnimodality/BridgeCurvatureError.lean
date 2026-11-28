module

public import CentralUnimodality.CurveTaylorBounds
public import CentralUnimodality.PolynomialGaussianInputs

/-! Differentiate the certified bridge differential-equation residual to
control the second derivative needed in the first binomial correction. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial Real Set ReturnSplit

def bridgeDefectRow := (List.range (bridgeCandidate.length+2)).map (odeRow bridgeCandidate 32768)

private theorem defect_realRow : realRow bridgeDefectRow=
    weightedSeries (bridgeCandidate.length+2) (fun i => (odeRow bridgeCandidate 32768 i:ℝ)) := by
  let n := bridgeCandidate.length+2
  have atIndex (i : ℕ) (h : i<n) : entry bridgeDefectRow i=odeRow bridgeCandidate 32768 i := by
    simp [entry,bridgeDefectRow,List.getElem?_range (show i<bridgeCandidate.length+2 from h)]
  simp only [realRow,weightedSeries,show bridgeDefectRow.length=n by simp [bridgeDefectRow,n],
    atIndex 0 (by dsimp [n]; omega)]
  apply congrArg (fun p : ℝ[X] => 2*p-C (odeRow bridgeCandidate 32768 0:ℝ))
  apply Finset.sum_congr rfl
  intro i hi; rw [atIndex i (Finset.mem_range.mp hi)]

theorem bridge_defect_identity (v : ℝ) : value bridgeDefectRow v=
    256*(deriv (value bridgeCandidate) v+v^2/32*value bridgeCandidate v) := by
  rw [(value_hasDerivAt bridgeCandidate v).deriv]
  simp only [value,defect_realRow,ode_polynomial,eval_add,eval_mul,eval_neg,eval_ofNat,
    eval_C,eval_pow,eval_sub,eval_X,Int.cast_ofNat]
  ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem bridge_defect_slope_budget :
    rowBudget (derivativeRow 0 bridgeDefectRow)*10^18≤2*2^120*128 := by decide +kernel

private theorem rate_deriv (x : ℝ) : HasDerivAt (fun t : ℝ => t^2/32) (x/16) x := by
  convert (((hasDerivAt_id x).pow 2).div_const 32) using 1
  · rfl
  · simp; ring

theorem bridge_second_error {v : ℝ} (hv : v∈Icc (0:ℝ) 144) :
    |iteratedDeriv 2 (value bridgeCandidate) v-iteratedDeriv 2 bridgeCurve v|≤4/10^16 := by
  let B := value bridgeCandidate
  let H := fun t : ℝ => B t-bridgeCurve t
  let g := fun t : ℝ => t^2/32
  have big : v∈Icc (0:ℝ) 256 := ⟨hv.1,by linarith only [hv.2]⟩
  have hB (t : ℝ) : HasDerivAt B (deriv B t) t := (value_hasDerivAt _ t).differentiableAt.hasDerivAt
  have hb (t : ℝ) : HasDerivAt bridgeCurve (deriv bridgeCurve t) t := (bridge_hasDeriv t).differentiableAt.hasDerivAt
  have dB : DifferentiableAt ℝ (deriv B) v := by
    have f : deriv B=fun t => -value (derivativeRow 0 bridgeCandidate) t/128 :=
      funext (fun t => (value_hasDerivAt _ t).deriv)
    rw [f]; exact (value_hasDerivAt _ v).differentiableAt.neg.div_const _
  have f : deriv bridgeCurve=fun t => -(t^2/32)*bridgeCurve t := funext (fun t => (bridge_hasDeriv t).deriv)
  have db : DifferentiableAt ℝ (deriv bridgeCurve) v := by
    rw [f]; exact (rate_deriv v).differentiableAt.neg.mul (hb v).differentiableAt
  let Y := fun t => deriv B t-deriv bridgeCurve t
  have dY : HasDerivAt Y (deriv (deriv B) v-deriv (deriv bridgeCurve) v) v := dB.hasDerivAt.sub db.hasDerivAt
  have identity : (fun t => Y t+g t*H t)=fun t => value bridgeDefectRow t/256 := by
    funext t; rw [bridge_defect_identity]; dsimp only [Y,H,g,B]; rw [f]; ring
  have derivId := (dY.add ((rate_deriv v).mul ((hB v).sub (hb v)))).deriv
  change deriv (fun t => Y t+g t*H t) v=_ at derivId
  rw [identity,((value_hasDerivAt bridgeDefectRow v).div_const 256).deriv] at derivId
  have e₀ := (gaussian_inputs big).2.2.1
  have e₁ : |Y v|≤5/10^19 := by
    change |deriv (value bridgeCandidate) v-deriv bridgeCurve v|≤_
    rw [f]; convert (gaussian_inputs big).2.2.2 using 2; ring
  have dbud : (rowBudget (derivativeRow 0 bridgeDefectRow):ℝ)*10^18≤2*2^120*128 := by
    exact_mod_cast bridge_defect_slope_budget
  have budget := value_bound (derivativeRow 0 bridgeDefectRow) big
  have e₂ : |-value (derivativeRow 0 bridgeDefectRow) v/128/256|≤1/(256*10^18) := by
    rw [abs_div,abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<128),abs_of_pos (by norm_num : (0:ℝ)<256)]
    generalize (rowBudget (derivativeRow 0 bridgeDefectRow):ℝ)=z at budget dbud
    generalize |value (derivativeRow 0 bridgeDefectRow) v|=y at budget ⊢
    linarith only [dbud,budget]
  have bigsq := pow_le_pow_left₀ hv.1 hv.2 2
  have err₀ : |v/16*H v|≤9*(2/10^22) := by
    rw [abs_mul,abs_of_nonneg (by linarith only [hv.1] : 0≤v/16)]
    exact mul_le_mul (by linarith only [hv.2]) e₀ (abs_nonneg _) (by norm_num)
  have err₁ : |g v*Y v|≤648*(5/10^19) := by
    rw [abs_mul,abs_of_nonneg (by dsimp [g]; positivity : 0≤g v)]
    exact mul_le_mul (by dsimp only [g]; linarith only [bigsq]) e₁ (abs_nonneg _) (by norm_num)
  have eq : deriv (deriv B) v-deriv (deriv bridgeCurve) v=
      -value (derivativeRow 0 bridgeDefectRow) v/128/256-v/16*H v-g v*Y v := by
    dsimp only [H,g,Y,Pi.sub_apply] at derivId ⊢; linarith only [derivId]
  simp only [show 2=1+1 by rfl,iteratedDeriv_succ]
  change |deriv (deriv B) v-deriv (deriv bridgeCurve) v|≤_
  rw [eq]
  apply (abs_sub ..).trans
  apply (add_le_add (abs_sub ..) err₁).trans
  linarith only [e₂,err₀]

end CentralUnimodality.PolynomialTrial
