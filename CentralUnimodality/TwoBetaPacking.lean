module

public import CentralUnimodality.ExactTrialConvolution

/-! Check a linear combination of two arcsine products by packing each
coefficient row once. The absolute-coefficient bounds prevent carries. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial ReturnSplit

structure BetaPairRows where
  left : List ℤ
  u : List ℤ
  f : List ℤ
  b : List ℤ
  m : List ℤ
  deriving DecidableEq, Repr

def weightedPair (a u f b m : List ℤ) : BetaPairRows :=
  ⟨fullWeighted a,halfWeighted u,halfWeighted f,halfWeighted b,halfWeighted m⟩

def betaPairCheck (bits d : ℕ) (W : BetaPairRows) : Bool := decide (
  coefficientMass W.left<2^bits ∧
  d*(coefficientMass W.u*coefficientMass W.f+7680*(coefficientMass W.b*coefficientMass W.m))<2^bits ∧
  packDense (bits+1) W.left=(d:ℤ)*(packDense (bits+1) W.u*packDense (bits+1) W.f+
    7680*(packDense (bits+1) W.b*packDense (bits+1) W.m)))

private theorem packed_polynomials {bits d : ℕ} (W : BetaPairRows) (h : betaPairCheck bits d W=true) :
    densePoly W.left=C (d:ℤ)*(densePoly W.u*densePoly W.f+C 7680*(densePoly W.b*densePoly W.m)) := by
  obtain ⟨left,right,eq⟩ := of_decide_eq_true h
  apply eq_of_packed_eval bits
  · intro i; exact (dense_coeff_bound ..).trans_lt (by exact_mod_cast left)
  · intro i
    rw [coeff_C_mul,coeff_add,coeff_C_mul,abs_mul,abs_of_nonneg (Int.natCast_nonneg d)]
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_add_le ..) (Int.natCast_nonneg d))
    rw [abs_mul,abs_of_nonneg (by decide : (0:ℤ)≤7680)]
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left
      (add_le_add (dense_product_bound _ _ i) (mul_le_mul_of_nonneg_left (dense_product_bound _ _ i) (by decide)))
      (Int.natCast_nonneg d))
    exact_mod_cast right
  · simpa only [eval_mul,eval_C,eval_add,← packDense_eval] using eq

private theorem full_add (P Q : ℝ[X]) :
    diagonal (fun j => (fullFactor j:ℝ)) (P+Q)=
      diagonal (fun j => (fullFactor j:ℝ)) P+diagonal (fun j => (fullFactor j:ℝ)) Q := by
  ext k; simp [mul_add]

theorem two_betas_of_check (a u f b m : List ℤ) {bits d : ℕ}
    (h : betaPairCheck bits d (weightedPair a u f b m)=true) :
    realDense a=C (d:ℝ)*(betaProduct (realDense u) (realDense f)+C 7680*betaProduct (realDense b) (realDense m)) := by
  have packed := packed_polynomials _ h
  have eq : realDense (fullWeighted a)=C (d:ℝ)*(realDense (halfWeighted u)*realDense (halfWeighted f)+
      C 7680*(realDense (halfWeighted b)*realDense (halfWeighted m))) := by
    change densePoly (fullWeighted a)=C (d:ℤ)*(densePoly (halfWeighted u)*densePoly (halfWeighted f)+
      C 7680*(densePoly (halfWeighted b)*densePoly (halfWeighted m))) at packed
    simp [realDense,packed,show C (7680:ℝ)=(7680:ℝ[X]) from map_ofNat _ _]
  have half (p : List ℤ) : realDense (halfWeighted p)=diagonal (fun k => (halfFactor k:ℝ)) (realDense p) :=
    realDense_weightList _ halfFactor (fun _ => rfl) p
  have full (p : List ℤ) : realDense (fullWeighted p)=diagonal (fun k => (fullFactor k:ℝ)) (realDense p) :=
    realDense_weightList _ fullFactor (fun _ => rfl) p
  apply diagonal_full_injective
  simpa only [diagonal_const_mul,full_add,diagonal_betaProduct,← half,← full] using eq

end CentralUnimodality.PolynomialTrial
