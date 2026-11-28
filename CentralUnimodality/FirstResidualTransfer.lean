module

public import CentralUnimodality.PhysicalCorrectionTrial
public import CentralUnimodality.BridgeCurvatureError
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-! Uniform cost of replacing the two cubic exponentials by their
dyadic polynomial approximations in the first residual. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Set Polynomial ReturnSplit

private theorem scaled_pair {v x : ℝ} (hv : v∈Icc (0:ℝ) 144) (hx : x∈Icc (0:ℝ) 1) :
    v*x∈Icc (0:ℝ) 144 ∧ v*(1-x)∈Icc (0:ℝ) 144 := by
  have part {y : ℝ} (lo : 0≤y) (hi : y≤1) : v*y∈Icc (0:ℝ) 144 :=
    ⟨mul_nonneg hv.1 lo,(mul_le_mul_of_nonneg_left hi hv.1).trans (by simpa using hv.2)⟩
  exact ⟨part hx.1 hx.2,part (by linarith only [hx.2]) (by linarith only [hx.1])⟩

private theorem widen {v : ℝ} (hv : v∈Icc (0:ℝ) 144) : v∈Icc (0:ℝ) 256 :=
  ⟨hv.1,by linarith only [hv.2]⟩

private theorem product_error {u v a b : ℝ} (h : |u|≤a) (k : |v|≤b) : |u*v|≤a*b := by
  rw [abs_mul]; exact mul_le_mul h k (abs_nonneg _) ((abs_nonneg _).trans h)

private theorem split_jet_error {v x : ℝ} (hv : v∈Icc (0:ℝ) 144) (hx : x∈Icc (0:ℝ) 1) :
    |splitJet 2 (value bridgeCandidate) (value candidate) v x-splitJet 2 bridgeCurve (value candidate) v x|
      ≤81/10^17 := by
  let a := v*x
  let b := v*(1-x)
  let F := value candidate
  let B := value bridgeCandidate
  have ⟨ha,hb⟩ := scaled_pair hv hx
  have e := (gaussian_inputs (widen ha)).2.2
  have e₁ : |deriv B a-deriv bridgeCurve a|≤5/10^19 := by
    rw [(bridge_hasDeriv a).deriv]; dsimp only [B,a]; convert e.2 using 2; ring
  have e₂ := bridge_second_error ha
  have f := candidate_bounds (widen hb)
  have f₂ : |iteratedDeriv 2 F b|≤2 := by
    simp only [show 2=1+1 by rfl,iteratedDeriv_succ]
    exact f.2.2
  let p := (iteratedDeriv 2 B a-iteratedDeriv 2 bridgeCurve a)*F b
  let q := (deriv B a-deriv bridgeCurve a)*deriv F b
  let s := (B a-bridgeCurve a)*iteratedDeriv 2 F b
  have ep : |p|≤4/10^16*2 := product_error e₂ f.1
  have eq : |q|≤5/10^19*2 := product_error e₁ f.2.1
  have es : |s|≤2/10^22*2 := product_error e.1 f₂
  rw [splitJet_two,splitJet_two,show _-_=p-2*q+s by dsimp only [p,q,s,F,B,a,b]; ring]
  apply (abs_add_le ..).trans
  apply (add_le_add (abs_sub ..) es).trans
  rw [abs_mul (2:ℝ) q,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith only [ep,eq]

private noncomputable def mixedPoly (σ : ℕ) (v x : ℝ) :=
  -value bridgeCandidate (v*x)*bridgeLogCorrection (v*x)*value candidate (v*(1-x))+
    value bridgeCandidate (v*x)*correctedValue σ (v*(1-x))

private theorem mixed_error {σ : ℕ} (hs : σ≤1) {v x : ℝ} (hv : v∈Icc (0:ℝ) 144)
    (hx : x∈Icc (0:ℝ) 1) :
    |mixedPoly σ v x-mixedCurve (value candidate) (correctedValue σ) v x|≤9/10^16 := by
  obtain ⟨ha,hb⟩ := scaled_pair hv hx
  let a := v*x
  let b := v*(1-x)
  have e := (gaussian_inputs (widen ha)).2.2.1
  have l := (retained_logs hs ha).2
  have f := (candidate_bounds (widen hb)).1
  have g := correctedValue_bound σ hb
  have eq : mixedPoly σ v x-mixedCurve (value candidate) (correctedValue σ) v x=
      (value bridgeCandidate a-bridgeCurve a)*(correctedValue σ b-bridgeLogCorrection a*value candidate b) := by
    dsimp [mixedPoly,mixedCurve,bridgeFirst,a,b]; ring
  rw [eq]
  have rhs := (abs_sub ..).trans (add_le_add g (product_error l f))
  exact (product_error e rhs).trans (by norm_num)

private theorem firstPoly_eval (σ : ℕ) (v : ℝ) : (firstPoly σ).eval v=
    -value freeCandidate v*freeLogCorrection σ v-arc (mixedPoly σ v)-
      (v/2)*arc (fun x => x*(1-x)*splitJet 2 (value bridgeCandidate) (value candidate) v x) := by
  simp only [firstPoly,firstResidualPoly_eval,eval_mul,eval_neg,physical_eval,(log_evals σ v).1,
    ← quadraticJet_eq_splitJet]
  congr 2
  apply congrArg arc
  funext x
  simp only [mixedPoly,splitFactor,eval_mul,eval_neg,physical_eval,correctedValue,correctedPoly,(log_evals σ (v*x)).2]

private theorem smooth_value (a : List ℤ) : ContDiff ℝ 2 (value a) := by
  rw [← physical_evaluation]
  simpa using (physicalPoly a).contDiff_aeval (𝕜:=ℝ) 2

private theorem jet_cont {A F : ℝ → ℝ} (hA : ContDiff ℝ 2 A) (hF : ContDiff ℝ 2 F) (v : ℝ) :
    Continuous (fun x => x*(1-x)*splitJet 2 A F v x) := by
  simp only [splitJet_two]
  have a := hA.continuous_iteratedDeriv 2 (by norm_num)
  have b := hF.continuous_iteratedDeriv 2 (by norm_num)
  have c := hA.continuous_deriv (by norm_num)
  have d := hF.continuous_deriv (by norm_num)
  have e := hA.continuous
  have f := hF.continuous
  fun_prop

theorem first_residual_transfer {σ : ℕ} (hs : σ≤1) {v : ℝ} (hv : v∈Icc (0:ℝ) 144) :
    |firstCurveResidual (value candidate) (correctedValue σ) σ v-(firstPoly σ).eval v|≤23/10^15 := by
  let F := value candidate
  let G := correctedValue σ
  let A := fun x => x*(1-x)*splitJet 2 bridgeCurve F v x
  let B := fun x => x*(1-x)*splitJet 2 (value bridgeCandidate) F v x
  have cF := (smooth_value candidate).continuous
  have cG : Continuous G := by change Continuous (fun t => (correctedPoly σ).eval t); fun_prop
  have L : Continuous (fun x : ℝ => v*x) := continuous_const.mul continuous_id
  have R : Continuous (fun x : ℝ => v*(1-x)) := continuous_const.mul (continuous_const.sub continuous_id)
  have b := (smooth_value bridgeCandidate).continuous.comp L
  have cℓ : Continuous bridgeLogCorrection := by unfold bridgeLogCorrection; fun_prop
  have cM : Continuous (mixedPoly σ v) :=
    ((b.neg.mul (cℓ.comp L)).mul (cF.comp R)).add (b.mul (cG.comp R))
  have cb : Continuous bridgeCurve := by unfold bridgeCurve; fun_prop
  have cb₁ : Continuous bridgeFirst := cb.neg.mul cℓ
  have cm : Continuous (mixedCurve F G v) :=
    ((cb₁.comp L).mul (cF.comp R)).add ((cb.comp L).mul (cG.comp R))
  have mix : |arc (mixedPoly σ v)-arc (mixedCurve F G v)|≤9/10^16 := by
    rw [← arc_sub cM cm]; exact arc_bound _ (fun _ hx => mixed_error hs hv hx)
  have jet : |arc B-arc A|≤(1/4)*(81/10^17) := by
    have smooth : ContDiff ℝ 2 bridgeCurve := by unfold bridgeCurve; fun_prop
    rw [← arc_sub (jet_cont (smooth_value bridgeCandidate) (smooth_value candidate) v)
      (jet_cont smooth (smooth_value candidate) v)]
    apply arc_bound; intro x hx
    have h : 0≤x*(1-x) := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
    have weight : |x*(1-x)|≤1/4 := by rw [abs_of_nonneg h]; nlinarith only [sq_nonneg (x-1/2)]
    change |x*(1-x)*_-x*(1-x)*_|≤_
    rw [← mul_sub]
    exact product_error weight (split_jet_error hv hx)
  have free := product_error (gaussian_inputs (widen hv)).1 (retained_logs hs hv).1
  have plus : |(v/2)*(arc B-arc A)|≤72*((1/4)*(81/10^17)) := by
    apply product_error _ jet
    rw [abs_of_nonneg (by linarith only [hv.1] : 0≤v/2)]; linarith only [hv.2]
  rw [firstPoly_eval,firstCurveResidual]
  change |_-(_-_-v/2*arc B)|≤_
  have eq : -freeCurve v*freeLogCorrection σ v-arc (mixedCurve F G v)-v/2*arc A-
      (-value freeCandidate v*freeLogCorrection σ v-arc (mixedPoly σ v)-v/2*arc B)=
      (value freeCandidate v-freeCurve v)*freeLogCorrection σ v+(arc (mixedPoly σ v)-arc (mixedCurve F G v))+
      (v/2)*(arc B-arc A) := by ring
  rw [eq]
  apply (abs_add_le ..).trans
  apply (add_le_add (abs_add_le ..) plus).trans
  linarith only [free,mix]

end CentralUnimodality.PolynomialTrial
