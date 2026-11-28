module

public import CentralUnimodality.FirstPackedCertificate
public import CentralUnimodality.LocalJetTable
public import CentralUnimodality.CorrectionDilation
public meta import CentralUnimodality.FirstPackedCertificate
import Mathlib.Tactic.Eval

/-! Combine the drift with the signed correction before taking interval
bounds. This preserves the cancellation in every derivative through order four. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial ReturnSplit

def combinedPower (m : List ℤ) := linearRows 512 1 m (driftRow 1 rawTrial)
def evenCombinedPower : List ℤ := eval% combinedPower evenRawM
def oddCombinedPower : List ℤ := eval% combinedPower oddRawM
def signedPower (σ : ℕ) := if σ=0 then evenCombinedPower else oddCombinedPower

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem even_combined : combinedPower evenRawM=evenCombinedPower := by decide +kernel
private theorem odd_combined : combinedPower oddRawM=oddCombinedPower := by decide +kernel

theorem combined_rep {σ : ℕ} (hs : σ≤1) (v : ℝ) :
    512*correctedValue σ v=(realDense (signedPower σ)).eval (v/256)/2^120 := by
  let M := if σ=0 then evenRawM else oddRawM
  have sm : dilate256 (physicalPoly (correctionCandidate σ))=C (1/(2:ℝ)^120)*realDense M := by
    have e := dilate_normalized _ _ (first_residual_inputs hs).2.2.2
    change dilate256 (physicalPoly (correctionCandidate σ))=C (1/(2:ℝ)^120)*realDense (correctionPower σ) at e
    rcases (show σ=0 ∨ σ=1 by omega) with rfl|rfl
    · simpa only [M,ite_eq_left rfl,evenRawM_exact] using e
    · simpa only [M,ite_eq_right (by decide : ¬1=0),oddRawM_exact] using e
  have sf : dilate256 (physicalPoly candidate)=C (1/(2:ℝ)^120)*realDense rawTrial := by
    rw [← rawTrial_exact]; exact dilate_normalized _ _ input_pack_bounds.2.2.1
  have ds : dilate256 (correctedPoly σ)=dilate256 (physicalPoly (correctionCandidate σ))+
      dilate256 (halfDrift (physicalPoly candidate)) := by simp [correctedPoly,dilate256]
  rw [sm,(dilate_drifts _).1,sf] at ds
  have scale (P : ℝ[X]) (k : ℝ) : driftOp 1 (C k*P)=C k*driftOp 1 P := by
    simp only [driftOp,derivative_C_mul]; ring
  rw [scale,← driftRow_exact] at ds
  have point := congrArg (Polynomial.eval (v/256)) ds
  simp only [dilate_eval,show 256*(v/256)=v by ring,eval_add,eval_mul,eval_C] at point
  have stored : signedPower σ=combinedPower M := by
    by_cases h : σ=0
    · simp only [signedPower,M,ite_eq_left h,even_combined]
    · simp only [signedPower,M,ite_eq_right h,odd_combined]
  rw [correctedValue,point,stored,combinedPower,dense_linear_eval]
  push_cast; ring

theorem trial_quadratic_jet {i r b : ℕ} (hi : i<288) (hr : r<7)
    (tab : (localJetTable rawTrial i 7)[r]?=some b) {v : ℝ} (hv : v∈halfInterval i) :
    |iteratedDeriv r (value candidate) v|≤(b:ℝ)/10^30 := by
  apply localJetTable_bound rawTrial _ (by decide +kernel) hi hr tab hv
  intro x
  rw [← rawTrial_exact]
  exact normalized_input 1536 _ input_pack_bounds.2.2.1 x

theorem signed_quadratic_jet {σ i r b : ℕ} (hs : σ≤1) (hi : i<288) (hr : r<5)
    (tab : (localJetTable (signedPower σ) i 5)[r]?=some b) {v : ℝ} (hv : v∈halfInterval i) :
    |iteratedDeriv r (correctedValue σ) v|≤(b:ℝ)/(512*10^30) := by
  have cap : coefficientMass (signedPower σ)*1024^(signedPower σ).length<2^5376 := by
    by_cases h : σ=0
    · simp only [signedPower,ite_eq_left h]; decide +kernel
    · simp only [signedPower,ite_eq_right h]; decide +kernel
  have e := localJetTable_bound (signedPower σ) (combined_rep hs) cap hi hr tab hv
  rw [iteratedDeriv_const_mul_field,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<512)] at e
  linarith only [e]

end CentralUnimodality.PolynomialTrial
