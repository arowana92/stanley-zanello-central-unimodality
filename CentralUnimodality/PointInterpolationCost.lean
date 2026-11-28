module

public import CentralUnimodality.PointFrequencyWindow
public import CentralUnimodality.WitnessSigns

/-! The mean squared products of the ten interpolation factors, evaluated
with all the even and odd moments of the positive-branch half-area. -/
@[expose] public section

namespace CentralUnimodality.Witness
open Laurent Real

def interpolationNodes (d : ℕ) : List ℚ :=
  ([198,277,380,513,672,853,1054,1278,1532,1840] : List ℚ).map (fun a => (a-d)/1000)

noncomputable def nodeProduct (d : ℕ) (x : ℝ) :=
  ((interpolationNodes d).map fun a : ℚ => x-(a:ℝ)).prod

theorem mean_horner (n δ : ℕ) (cs : List ℚ) (r : ℕ) :
    rankMean n δ (fun i => scaledSite n δ i^r*horner (scaledSite n δ i) cs)=
      polyExpectation (pointMoment n δ) r cs := by
  induction cs generalizing r with
  | nil => simp [rankMean,horner,polyExpectation]
  | cons a cs ih =>
    rw [polyExpectation,← rankMean_power,← ih]
    unfold rankMean
    rw [← mul_div_assoc,← add_div,Finset.mul_sum,← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [horner,pow_succ]
    ring

private def nodeCoefficients (d : ℕ) := rootCoeffs (interpolationNodes d++interpolationNodes d)

private def passes (P : Pair) : Bool :=
  upperTest P Wallis.lower Wallis.lowerConstant (-1/1000000000) &&
    upperTest P Wallis.upper Wallis.upperConstant (-1/1000000000)

private def nodeCheck (C : Array Laurent) (d : ℕ) : Bool :=
  let A := pointsFromCells C 21
  let pair := buildPair (fun r => polynomialFromCell (lookup A r) r) 0 (nodeCoefficients d)
  pair.any passes

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem checked_nodes : nodeCheck evenCells 0=true ∧ nodeCheck evenCells 1=true ∧
    nodeCheck oddCells 0=true ∧ nodeCheck oddCells 1=true := by decide +kernel

theorem node_product_cost {n δ d : ℕ} (hδ : δ≤1) (hd : d≤1) (hn : 96≤n+δ) :
    rankMean n δ (fun i => nodeProduct d (scaledSite n δ i)^2) ≤ 1/1000000000 := by
  have check : nodeCheck (sourceCells δ) d=true := by
    rcases (by omega : δ=0 ∨ δ=1) with rfl|rfl <;> rcases (by omega : d=0 ∨ d=1) with rfl|rfl
    · exact checked_nodes.1
    · exact checked_nodes.2.1
    · exact checked_nodes.2.2.1
    · exact checked_nodes.2.2.2
  let A := pointsFromCells (sourceCells δ) 21
  let M := fun r => polynomialFromCell (lookup A r) r
  change (buildPair M 0 (nodeCoefficients d)).any passes=true at check
  cases hp : buildPair M 0 (nodeCoefficients d) with
  | none =>
    simp only [hp,Option.any_none,Bool.false_eq_true] at check
  | some pair =>
    simp only [hp,Option.any_some,passes,Bool.and_eq_true] at check
    have len : (nodeCoefficients d).length=21 := by
      rcases (by omega : d=0 ∨ d=1) with rfl|rfl <;> decide +kernel
    have eq := buildPair_sound (pointMoment n δ) M ((n+δ:ℕ):ℝ)⁻¹ (wallisFactor (n+δ))
      (nodeCoefficients d) 0 hp (fun r _ hr p h => tabulated_point_moment hδ (by omega)
        (by rw [len] at hr; omega) h)
    have h := upperTests_sound hn check.1 check.2
    rw [← eq,← mean_horner] at h
    simpa only [nodeCoefficients,horner_roots,pow_zero,one_mul,List.map_append,List.prod_append,
      ← sq,nodeProduct,Rat.cast_div,Rat.cast_neg,Rat.cast_one,Rat.cast_ofNat,neg_div,neg_neg] using h

end CentralUnimodality.Witness
