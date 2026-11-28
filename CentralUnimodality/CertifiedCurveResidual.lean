module

public import CentralUnimodality.BaseResidualBounds
public import CentralUnimodality.CurveTaylorBounds

/-! The exact polynomial identity and the two cubic Gaussian enclosures
give uniform value and Lipschitz bounds for the continuous split residual. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

open Real Set ReturnSplit

private noncomputable def freeError (v : ℝ) := value freeCandidate v-freeCurve v
private noncomputable def bridgeError (v : ℝ) := value bridgeCandidate v-bridgeCurve v
private noncomputable def integrand (v x : ℝ) := bridgeError (v*x)*value candidate (v*(1-x))

theorem value_continuous (a : List ℤ) : Continuous (value a) :=
  continuous_iff_continuousAt.mpr (fun v => (value_hasDerivAt a v).continuousAt)

private theorem integrand_continuous (v : ℝ) : Continuous (integrand v) := by
  have F := value_continuous candidate
  have B := value_continuous bridgeCandidate
  have G : Continuous bridgeCurve := by unfold bridgeCurve; fun_prop
  exact ((B.sub G).comp (continuous_const.mul continuous_id)).mul
    (F.comp (continuous_const.mul (continuous_const.sub continuous_id)))

private theorem residual_identity (v : ℝ) :
    curveResidual (value candidate) v=baseResidual v-freeError v+arc (integrand v) := by
  let p := fun x => value bridgeCandidate (v*x)*value candidate (v*(1-x))
  have F := value_continuous candidate
  have B := value_continuous bridgeCandidate
  have hp : Continuous p := (B.comp (continuous_const.mul continuous_id)).mul
    (F.comp (continuous_const.mul (continuous_const.sub continuous_id)))
  have same : integrand v=fun x => p x-splitCurve (value candidate) v x := by
    funext x; dsimp [integrand,bridgeError,p,splitCurve]; ring
  rw [same,arc_sub hp (splitCurve_continuous F v),← trial_convolution v]
  unfold curveResidual freeError
  dsimp only [p]
  ring

private theorem dom_scaled {v x : ℝ} (hv : v∈Icc (0:ℝ) 256) (hx : x∈Icc (0:ℝ) 1) :
    v*x∈Icc (0:ℝ) 256 :=
  ⟨mul_nonneg hv.1 hx.1,((mul_le_mul_of_nonneg_left hx.2 hv.1).trans_eq (mul_one v)).trans hv.2⟩

private theorem complement {x : ℝ} (h : x∈Icc (0:ℝ) 1) : 1-x∈Icc (0:ℝ) 1 := by
  constructor <;> linarith only [h.1,h.2]

private theorem contract {v w x : ℝ} (hx : x∈Icc (0:ℝ) 1) : |v*x-w*x|≤|v-w| := by
  rw [← sub_mul,abs_mul,abs_of_nonneg hx.1]
  exact (mul_le_mul_of_nonneg_left hx.2 (abs_nonneg _)).trans_eq (mul_one _)

private theorem free_hasDeriv (x : ℝ) : HasDerivAt freeCurve (-(x^2/8)*freeCurve x) x := by
  have inner : HasDerivAt (fun t : ℝ => -(t^3/24)) (-(x^2/8)) x := by
    convert (((hasDerivAt_id x).pow 3).div_const 24).neg using 1
    · rfl
    · simp; ring
  convert inner.exp using 1
  · rfl
  · change -(x^2/8)*exp (-(x^3/24))=_
    ring

private theorem free_lip {v w : ℝ} (hv : v∈Icc (0:ℝ) 256) (hw : w∈Icc (0:ℝ) 256) :
    |freeError v-freeError w|≤(2/10^18)*|v-w| := by
  let d := fun x => deriv (value freeCandidate) x+(x^2/8)*freeCurve x
  have hg (x : ℝ) : HasDerivAt freeError (d x) x := by
    convert (value_hasDerivAt freeCandidate x).differentiableAt.hasDerivAt.sub (free_hasDeriv x) using 1
    · rfl
    · dsimp only [d]; ring
  exact interval_lipschitz hg (convex_Icc ..) (fun _ h => (gaussian_inputs h).2.1) hw hv

private theorem bridge_lip {v w : ℝ} (hv : v∈Icc (0:ℝ) 256) (hw : w∈Icc (0:ℝ) 256) :
    |bridgeError v-bridgeError w|≤(5/10^19)*|v-w| := by
  let d := fun x => deriv (value bridgeCandidate) x+(x^2/32)*bridgeCurve x
  have hg (x : ℝ) : HasDerivAt bridgeError (d x) x := by
    convert (value_hasDerivAt bridgeCandidate x).differentiableAt.hasDerivAt.sub (bridge_hasDeriv x) using 1
    · rfl
    · dsimp only [d]; ring
  exact interval_lipschitz hg (convex_Icc ..) (fun _ h => (gaussian_inputs h).2.2.2) hw hv

private theorem integrand_lip {v w x : ℝ} (hv : v∈Icc (0:ℝ) 256) (hw : w∈Icc (0:ℝ) 256)
    (hx : x∈Icc (0:ℝ) 1) :
    |integrand v x-integrand w x| ≤ (10/10^19+4/10^22)*|v-w| := by
  let B := bridgeError
  let F := value candidate
  let y := 1-x
  have hy := complement hx
  have av := dom_scaled hv hx
  have aw := dom_scaled hw hx
  have bv := dom_scaled hv hy
  have bw := dom_scaled hw hy
  have A : |B (v*x)-B (w*x)|≤(5/10^19)*|v-w| :=
    (bridge_lip av aw).trans (mul_le_mul_of_nonneg_left (contract hx) (by norm_num))
  have C : |F (v*y)-F (w*y)|≤2*|v-w| :=
    (interval_lipschitz trial_hasDeriv (convex_Icc ..) (fun _ h => (candidate_bounds h).2.1) bw bv).trans
      (mul_le_mul_of_nonneg_left (contract hy) (by norm_num))
  have left := mul_le_mul A (candidate_bounds bv).1 (abs_nonneg _) (by positivity)
  have right := mul_le_mul (gaussian_inputs aw).2.2.1 C (abs_nonneg _) (by norm_num)
  have eq : integrand v x-integrand w x=(B (v*x)-B (w*x))*F (v*y)+B (w*x)*(F (v*y)-F (w*y)) := by
    dsimp [integrand,B,F,y]; ring
  rw [eq]
  apply (abs_add_le ..).trans
  rw [abs_mul,abs_mul]
  change |B (v*x)-B (w*x)| * |F (v*y)| + |B (w*x)| * |F (v*y)-F (w*y)| ≤ _
  exact (add_le_add left right).trans_eq (by ring)

theorem curve_value_bound {v : ℝ} (hv : v∈Icc (0:ℝ) 256) :
    |curveResidual (value candidate) v|≤15/10^16 := by
  have ad : |arc (integrand v)|≤4/10^22 := by
    apply arc_bound
    intro x hx
    rw [integrand,abs_mul]
    exact (mul_le_mul (gaussian_inputs (dom_scaled hv hx)).2.2.1
      (candidate_bounds (dom_scaled hv (complement hx))).1 (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  rw [residual_identity]
  apply (abs_add_le ..).trans
  apply (add_le_add ((abs_sub ..).trans (add_le_add (base_bounds hv).1 (gaussian_inputs hv).1)) ad).trans
  norm_num

theorem curve_lipschitz {v w : ℝ} (hv : v∈Icc (0:ℝ) 256) (hw : w∈Icc (0:ℝ) 256) :
    |curveResidual (value candidate) v-curveResidual (value candidate) w|≤(36/10^14)*|v-w| := by
  have a := interval_lipschitz base_hasDeriv (convex_Icc ..) (fun _ h => (base_bounds h).2) hw hv
  have b := free_lip hv hw
  have c : |arc (integrand v)-arc (integrand w)| ≤ (10/10^19+4/10^22)*|v-w| := by
    rw [← arc_sub (integrand_continuous v) (integrand_continuous w)]
    exact arc_bound _ (fun x hx => integrand_lip hv hw hx)
  rw [residual_identity,residual_identity]
  rw [show baseResidual v-freeError v+arc (integrand v)-(baseResidual w-freeError w+arc (integrand w))=
    (baseResidual v-baseResidual w-(freeError v-freeError w))+(arc (integrand v)-arc (integrand w)) by ring]
  apply (abs_add_le ..).trans
  apply (add_le_add ((abs_sub ..).trans (add_le_add a b)) c).trans
  linarith only [abs_nonneg (v-w)]

end CentralUnimodality.PolynomialTrial
