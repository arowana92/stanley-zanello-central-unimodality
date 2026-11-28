module

public import CentralUnimodality.SplitFirstCorrection
public import CentralUnimodality.DirectCorrectedResidual
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Polynomial residual for the first correction of the binomial split,
including the endpoint at zero. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open Polynomial

noncomputable def firstResidualPoly (P₁ B₁ B F M : ℝ[X]) :=
  P₁-fullDrift (betaProduct B F)-betaProduct (B₁-halfDrift B) F-betaProduct B M

theorem quadraticJet_eq_splitJet (B F : ℝ[X]) (v x : ℝ) :
    splitJet 2 (fun t => B.eval t) (fun t => F.eval t) v x=quadraticJet B F v x := by
  have der (P : ℝ[X]) : deriv (fun t => P.eval t)=fun t => P.derivative.eval t :=
    funext (fun x => (P.hasDerivAt x).deriv)
  simp only [splitJet,Finset.sum_range_succ,Finset.sum_range_zero,quadraticJet,splitFactor]
  norm_num [iteratedDeriv_succ,der]; ring

theorem firstResidualPoly_eval (P₁ B₁ B F M : ℝ[X]) (v : ℝ) :
    (firstResidualPoly P₁ B₁ B F M).eval v=P₁.eval v-
      arc (fun x => splitFactor B₁ F v x+splitFactor B (M+halfDrift F) v x)-
      (v/2)*arc (fun x => x*(1-x)*quadraticJet B F v x) := by
  have cont (P Q : ℝ[X]) : Continuous (splitFactor P Q v) := by unfold splitFactor; fun_prop
  have term : arc (splitFactor (B₁-halfDrift B) F v)=
      arc (splitFactor B₁ F v)-arc (splitFactor (halfDrift B) F v) := by
    rw [← arc_sub (cont _ _) (cont _ _)]
    apply arc_congr; intro x _; simp [splitFactor,sub_mul]
  have term' : arc (splitFactor B (M+halfDrift F) v)=
      arc (splitFactor B M v)+arc (splitFactor B (halfDrift F) v) := by
    rw [← arc_add (cont _ _) (cont _ _)]
    apply arc_congr; intro x _; simp [splitFactor,mul_add]
  have jet := quadratic_jet_correction B F v
  rw [eval_add] at jet
  have beta (A C : ℝ[X]) : (betaProduct A C).eval v=arc (splitFactor A C v) := (arc_polynomial v A C).symm
  simp only [firstResidualPoly,eval_sub,beta] at jet ⊢
  rw [term,arc_add (cont _ _) (cont _ _),term']
  linarith only [jet]

end CentralUnimodality.ReturnSplit
