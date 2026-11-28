module

public import CentralUnimodality.QuadraticResidualStability
public import CentralUnimodality.ReplacementTrialBounds
public import CentralUnimodality.ReplacementMultiplierBounds
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-! A uniform allowance for replacing the elementary Gaussian curves by
their rational trials in the signed second coefficient. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Set ReturnSplit

set_option maxHeartbeats 600000 in
theorem second_residual_transfer {σ : ℕ} (hs : σ≤1) {v : ℝ} (hv : v∈Icc (0:ℝ) 144) :
    |(secondPoly σ).eval v-secondCurveResidual (value candidate) (correctedValue σ) σ v|≤3/10^7 := by
  let F := value candidate
  let G := correctedValue σ
  let P := fun t => value freeCandidate t*(freeLogCorrection σ t^2/2-freeSecondLog σ t)
  let B₂ := fun t => value bridgeCandidate t*(bridgeLogCorrection t^2/2-bridgeSecondLog t)
  let B₁ := fun t => -value bridgeCandidate t*bridgeLogCorrection t
  let B := value bridgeCandidate
  have smooth (p : List ℤ) (r : ℕ) : ContDiff ℝ r (value p) := by
    rw [← physical_evaluation]; simpa using (physicalPoly p).contDiff_aeval (𝕜:=ℝ) r
  have f := smooth candidate 4
  have g : ContDiff ℝ 2 G := by
    change ContDiff ℝ 2 (correctedPoly σ).eval
    simpa using (correctedPoly σ).contDiff_aeval (𝕜:=ℝ) 2
  have b := smooth bridgeCandidate 4
  have br : ContDiff ℝ 4 bridgeCurve := by unfold bridgeCurve; fun_prop
  have bc := b.continuous
  have b₁ : ContDiff ℝ 2 B₁ := (smooth bridgeCandidate 2).neg.mul (by unfold bridgeLogCorrection; fun_prop)
  have b₂ : Continuous B₂ := by unfold B₂ bridgeLogCorrection bridgeSecondLog; fun_prop
  have a₂ : Continuous bridgeSecond := by unfold bridgeSecond bridgeCurve bridgeLogCorrection bridgeSecondLog; fun_prop
  have a₁ : ContDiff ℝ 2 bridgeFirst := by unfold bridgeFirst bridgeCurve bridgeLogCorrection; fun_prop
  rw [secondPoly_form,secondCurveResidual_form _ _ (f.of_le (by norm_num)) g]
  change |quadraticResidualForm P B₂ B₁ B F G v-
    quadraticResidualForm (freeSecond σ) bridgeSecond bridgeFirst bridgeCurve F G v|≤_
  rw [quadratic_form_sub b₂ a₂ b₁ a₁ b br f g]
  let c₁ := fun r : ℕ => 5/10^16*(1000:ℝ)^r
  let c := fun r : ℕ => 2/10^22*(1000:ℝ)^r
  let d := fun r : ℕ => (trialJetCap r:ℝ)
  let e := fun _ : ℕ => (1024:ℝ)
  have wide {t : ℝ} (ht : t∈Icc 0 v) : t∈Icc (0:ℝ) 144 := ⟨ht.1,ht.2.trans hv.2⟩
  have H := quadratic_form_bound (P:=P-freeSecond σ) (B₂:=B₂-bridgeSecond) (B₁:=B₁-bridgeFirst)
    (B:=B-bridgeCurve) (F:=F) (G:=G) hv.1 c₁ c d e (free_second_replacement hs hv)
    (fun _ ht => bridge_second_replacement (wide ht))
    (fun i hi _ ht => bridge_first_replacement_jets (wide ht) i hi)
    (fun i hi t ht => by
      rw [iteratedDeriv_sub (f:=B) (g:=bridgeCurve) (b.of_le (by exact_mod_cast hi)).contDiffAt
        (br.of_le (by exact_mod_cast hi)).contDiffAt]
      exact bridge_replacement_jets (wide ht) i hi)
    (fun i hi _ ht => trial_replacement_jets hi (wide ht))
    (fun i hi _ ht => correction_replacement_jets hs hi (wide ht))
  apply H.trans
  norm_num [jetMajorant,c₁,c,d,e,trialJetCap,Finset.sum_range_succ,Nat.choose]
  linarith only [hv.2,pow_le_pow_left₀ hv.1 hv.2 2]

end CentralUnimodality.PolynomialTrial
