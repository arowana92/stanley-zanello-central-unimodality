module

public import CentralUnimodality.PolynomialSecondSplit
public import CentralUnimodality.QuadraticSplitResidual
public import CentralUnimodality.PhysicalCorrectionTrial

/-! The signed coefficient evaluated by the rational certificate is obtained
by replacing the two Gaussian inputs in the true residual by polynomials. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open Polynomial

noncomputable def linearJetMean (A B : ℝ → ℝ) (v : ℝ) :=
  arc (fun x => x*(1-x)*v*splitJet 2 A B v x/2)

noncomputable def quadraticResidualForm (P₂ B₂ B₁ B F G : ℝ → ℝ) (v : ℝ) :=
  P₂ v-arc (splitPair B₂ F v)-arc (splitPair B₁ G v)-
    linearJetMean B₁ F v-linearJetMean B G v-areaSplitSecond B F v

theorem secondCurveResidual_form (F G : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (σ : ℕ) (v : ℝ) :
    secondCurveResidual F G σ v=quadraticResidualForm (freeSecond σ) bridgeSecond bridgeFirst bridgeCurve F G v := by
  have b : ContDiff ℝ 2 bridgeCurve := by unfold bridgeCurve; fun_prop
  have b₁ : ContDiff ℝ 2 bridgeFirst := by unfold bridgeFirst bridgeLogCorrection bridgeCurve; fun_prop
  have b₂ : ContDiff ℝ 2 bridgeSecond := by unfold bridgeSecond bridgeSecondLog bridgeLogCorrection bridgeCurve; fun_prop
  have j₁ := splitJet_continuous b₁ hF v
  have j₂ := splitJet_continuous b hG v
  have sum : v/2*arc (fun x => x*(1-x)*(splitJet 2 bridgeFirst F v x+splitJet 2 bridgeCurve G v x))=
      linearJetMean bridgeFirst F v+linearJetMean bridgeCurve G v := by
    rw [← arc_const_mul,linearJetMean,linearJetMean,← arc_add (by fun_prop) (by fun_prop)]
    apply arc_congr
    intro x _
    ring
  have mixed : arc (secondMixedCurve F G v)=arc (splitPair bridgeSecond F v)+arc (splitPair bridgeFirst G v) :=
    arc_add (splitPair_smooth b₂ hF v).continuous (splitPair_smooth b₁ hG v).continuous
  rw [secondCurveResidual,mixed,sum,quadraticResidualForm]
  ring

noncomputable def secondResidualPoly (P₂ B₂ B₁ B F G : ℝ[X]) :=
  P₂-betaProduct B₂ F-betaProduct B₁ G-splitFirstPoly B₁ F-splitFirstPoly B G-splitSecondPoly B F

theorem secondResidualPoly_eval (P₂ B₂ B₁ B F G : ℝ[X]) (v : ℝ) :
    (secondResidualPoly P₂ B₂ B₁ B F G).eval v=quadraticResidualForm P₂.eval B₂.eval B₁.eval B.eval F.eval G.eval v := by
  simp only [secondResidualPoly,eval_sub,split_first_poly_eval,split_second_poly_eval,← arc_polynomial]
  rfl

/-- A weighted beta product uses the same factorial convolution after multiplying
the two input polynomials by the indicated powers of the variable. -/
theorem weighted_beta_clear (a b : ℕ) (P Q : ℝ[X]) :
    X^(a+b)*weightedBeta a b P Q=betaProduct (X^a*P) (X^b*Q) := by
  apply Polynomial.funext
  intro v
  simp only [eval_mul,eval_pow,eval_X,weighted_beta_eval,← arc_polynomial,← arc_const_mul]
  apply arc_congr
  intro x _
  simp only [splitPair,mul_pow,pow_add]
  ring

end CentralUnimodality.ReturnSplit

namespace CentralUnimodality.PolynomialTrial
open Polynomial ReturnSplit

noncomputable def freeSecondLogPoly (σ : ℕ) : ℝ[X] :=
  C ((12*σ+1:ℝ)/192)*X+C ((2*σ+1:ℝ)/1536)*X^4+C (1/80640:ℝ)*X^7

noncomputable def bridgeSecondLogPoly : ℝ[X] := C (7/184320:ℝ)*X^4+C (1/5160960:ℝ)*X^7

theorem second_log_evals (σ : ℕ) (v : ℝ) :
    (freeSecondLogPoly σ).eval v=freeSecondLog σ v ∧ bridgeSecondLogPoly.eval v=bridgeSecondLog v := by
  simp only [freeSecondLogPoly,bridgeSecondLogPoly,freeSecondLog,bridgeSecondLog,eval_add,eval_mul,eval_C,eval_X,eval_pow]
  constructor <;> ring

noncomputable def secondMultiplier (A B : ℝ[X]) := C (1/2:ℝ)*A^2-B

noncomputable def secondPoly (σ : ℕ) : ℝ[X] :=
  let p := physicalPoly freeCandidate
  let b := physicalPoly bridgeCandidate
  secondResidualPoly (p*secondMultiplier (freeLogPoly σ) (freeSecondLogPoly σ))
    (b*secondMultiplier bridgeLogPoly bridgeSecondLogPoly) (-b*bridgeLogPoly) b
    (physicalPoly candidate) (correctedPoly σ)

theorem secondPoly_form (σ : ℕ) (v : ℝ) :
    (secondPoly σ).eval v=quadraticResidualForm
      (fun t => value freeCandidate t*((freeLogCorrection σ t)^2/2-freeSecondLog σ t))
      (fun t => value bridgeCandidate t*((bridgeLogCorrection t)^2/2-bridgeSecondLog t))
      (fun t => -value bridgeCandidate t*bridgeLogCorrection t) (value bridgeCandidate)
      (value candidate) (correctedValue σ) v := by
  rw [secondPoly,secondResidualPoly_eval,physical_evaluation,physical_evaluation]
  congr 1 <;> funext t <;>
    simp only [secondMultiplier,eval_mul,eval_sub,eval_C,eval_pow,eval_neg,physical_eval,
      (log_evals σ t).1,(log_evals σ t).2,(second_log_evals σ t).1,(second_log_evals σ t).2] <;> ring

end CentralUnimodality.PolynomialTrial
