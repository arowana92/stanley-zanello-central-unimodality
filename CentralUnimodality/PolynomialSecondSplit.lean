module

public import CentralUnimodality.SecondOrderQuadrature
public import CentralUnimodality.CorrectedLocalDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-! Polynomial evaluation of the signed order-two term of the last-return
quadrature. Shifting the two beta exponents preserves the output degree. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit

open Polynomial Finset Set

noncomputable def weightedBeta (a b : ℕ) (P Q : ℝ[X]) : ℝ[X] :=
  ∑ i ∈ P.support, ∑ j ∈ Q.support,
    monomial (i+j) (P.coeff i*Q.coeff j*betaWeight (a+i) (b+j))

theorem weighted_beta_eval (a b : ℕ) (P Q : ℝ[X]) (v : ℝ) :
    (weightedBeta a b P Q).eval v=
      arc (fun x => x^a*(1-x)^b*splitPair P.eval Q.eval v x) := by
  let c (i j : ℕ) := P.coeff i*Q.coeff j*v^(i+j)
  have expand (x : ℝ) : x^a*(1-x)^b*splitPair P.eval Q.eval v x=
      ∑ i ∈ P.support, ∑ j ∈ Q.support, c i j*(x^(a+i)*(1-x)^(b+j)) := by
    rw [splitPair,P.eval_eq_sum,Q.eval_eq_sum]
    simp only [Polynomial.sum_def,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    dsimp only [c]
    simp only [pow_add,mul_pow]; ring
  simp_rw [expand]
  rw [arc_sum _ _ (by intro i _; fun_prop)]
  simp only [weightedBeta,eval_finsetSum,eval_monomial]
  apply sum_congr rfl
  intro i _
  rw [arc_sum _ _ (by intro j _; fun_prop)]
  apply sum_congr rfl
  intro j _
  rw [arc_const_mul,arc_mixed]
  dsimp only [c]; ring

noncomputable def weightedSplitJet (r a b : ℕ) (P Q : ℝ[X]) : ℝ[X] :=
  ∑ i ∈ range (r+1), C ((r.choose i:ℝ)*(-1)^(r-i))*
    weightedBeta a b (derivative^[i] P) (derivative^[r-i] Q)

theorem weighted_split_jet_eval (r a b : ℕ) (P Q : ℝ[X]) (v : ℝ) :
    (weightedSplitJet r a b P Q).eval v=
      arc (fun x => x^a*(1-x)^b*splitJet r P.eval Q.eval v x) := by
  simp only [weightedSplitJet,eval_finsetSum,eval_mul,eval_C,weighted_beta_eval,← arc_const_mul]
  unfold splitJet
  simp_rw [Finset.mul_sum,PolynomialTrial.polynomial_jet]
  rw [arc_sum _ _ (by intro i _; fun_prop)]
  apply sum_congr rfl
  intro i _
  apply arc_congr
  intro x _
  unfold splitPair; ring

noncomputable def splitSecondPoly (P Q : ℝ[X]) : ℝ[X] :=
  C (1/6:ℝ)*X*(weightedSplitJet 3 1 2 P Q-weightedSplitJet 3 2 1 P Q)+
    C (1/8:ℝ)*X^2*weightedSplitJet 4 2 2 P Q

theorem split_second_poly_eval (P Q : ℝ[X]) (v : ℝ) :
    (splitSecondPoly P Q).eval v=arc (fun x =>
      let q := x*(1-x)
      q*(1-2*x)*v*splitJet 3 P.eval Q.eval v x/6+
        q^2*v^2*splitJet 4 P.eval Q.eval v x/8) := by
  have cont (r : ℕ) : Continuous (splitJet r P.eval Q.eval v) := by
    unfold splitJet
    simp_rw [PolynomialTrial.polynomial_jet]
    fun_prop
  simp only [splitSecondPoly,eval_add,eval_mul,eval_sub,eval_C,eval_X,eval_pow,weighted_split_jet_eval]
  rw [← arc_sub (by fun_prop) (by fun_prop),← arc_const_mul,← arc_const_mul,← arc_add (by fun_prop) (by fun_prop)]
  apply arc_congr
  intro x _
  ring

noncomputable def splitFirstPoly (P Q : ℝ[X]) : ℝ[X] :=
  C (1/2:ℝ)*X*weightedSplitJet 2 1 1 P Q

theorem split_first_poly_eval (P Q : ℝ[X]) (v : ℝ) :
    (splitFirstPoly P Q).eval v=arc (fun x => x*(1-x)*v*splitJet 2 P.eval Q.eval v x/2) := by
  simp only [splitFirstPoly,eval_mul,eval_C,eval_X,weighted_split_jet_eval,← arc_const_mul]
  apply arc_congr
  intro x _
  simp only [pow_one]; ring

theorem sample_split_polynomial_second (P Q : ℝ[X]) {j : ℕ} (hj : 0<j)
    {τ v D₄ D₅ D₆ : ℝ} (hτ : 0≤τ) (hv : v=j*τ)
    (b₄ : ∀ x∈Icc (0:ℝ) 1, splitJetBound 4 P.eval Q.eval v x≤D₄)
    (b₅ : ∀ x∈Icc (0:ℝ) 1, splitJetBound 5 P.eval Q.eval v x≤D₅)
    (b₆ : ∀ x∈Icc (0:ℝ) 1, splitJetBound 6 P.eval Q.eval v x≤D₆) :
    |sample j (splitPair P.eval Q.eval v)-((betaProduct P Q).eval v+
      τ*(splitFirstPoly P Q).eval v+τ^2*(splitSecondPoly P Q).eval v)|≤
      τ^3*(v*D₄/96+v^2*D₅/192+v^3*D₆/1440) := by
  have smooth (B : ℝ[X]) : ContDiff ℝ 6 B.eval := by
    simpa using B.contDiff_aeval (𝕜:=ℝ) 6
  have cont (r : ℕ) : Continuous (splitJet r P.eval Q.eval v) := by
    unfold splitJet
    simp_rw [PolynomialTrial.polynomial_jet]
    fun_prop
  have base := (splitPair_smooth (smooth P) (smooth Q) v).continuous
  have H := sample_split_second (smooth P) (smooth Q) hj hτ hv b₄ b₅ b₆
  rw [← arc_polynomial,split_first_poly_eval,split_second_poly_eval,← arc_const_mul,← arc_const_mul,
    ← arc_add (by fun_prop) (by fun_prop),← arc_add (by fun_prop) (by fun_prop)]
  exact H

end CentralUnimodality.ReturnSplit
