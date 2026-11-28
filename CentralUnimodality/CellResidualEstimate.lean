module

public import CentralUnimodality.SplitCellMaxima
public import CentralUnimodality.CorrectedAmplitudeCost
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-! Turn the four integer split allowances into a local residual for
the actual parity-dependent signed walk in a closed half-unit cell. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open ReturnSplit Real Set Polynomial

set_option maxRecDepth 12000

private theorem round_cost (i n a b c d : ℕ) :
    (n:ℝ)/10^30+(a:ℝ)/(25000*10^60)+(((i:ℝ)+1)/2)*(b/(4*10^60))/8+
      (((i:ℝ)+1)/2)*(c/10^60)/24+(((i:ℝ)+1)/2)^2*(d/10^60)/128≤
      (ceilQuotient (4800000*n*10^30+192*a+75000*(i+1)*b+100000*(i+1)*c+9375*(i+1)^2*d)
        (4800000*10^30):ℝ)/10^30 := by
  let A := 4800000*n*10^30+192*a+75000*(i+1)*b+100000*(i+1)*c+9375*(i+1)^2*d
  let D : ℕ := 4800000*10^30
  have h : A≤D*ceilQuotient A D := (ceilDiv_le_iff_le_mul (by decide +kernel : 0<D)).mp (le_refl _)
  have e : (A:ℝ)≤(D:ℝ)*(ceilQuotient A D:ℝ) := by exact_mod_cast h
  change _≤(ceilQuotient A D:ℝ)/10^30
  generalize ht : (ceilQuotient A D:ℝ)=t at e ⊢
  dsimp only [A,D] at e
  push_cast at e
  linarith only [e]

private theorem trial_smooth (P : ℝ[X]) (k : ℕ) : ContDiff ℝ k P.eval := by
  simpa only [Polynomial.aeval_def,Algebra.algebraMap_self,Polynomial.eval₂_id] using P.contDiff_aeval (𝕜:=ℝ) k

theorem residual_of_cell_max {i j σ : ℕ} (hs : σ≤1) (hi : i<288) (test : cellMaxTest i=true)
    {ω τ v : ℝ} (hτ : 0≤τ) (ht : τ≤(maxStep:ℝ)) (hω : ω^2=τ^3/32)
    (angle : |ω| *(2*j+σ)≤9/8) (hv : v=j*τ) (cell : v∈halfInterval i) :
    ‖parityResidual ω (correctedSeries σ τ) σ j-
      ((curveResidual (value candidate) v+τ*firstCurveResidual (value candidate) (correctedValue σ) σ v:ℝ):ℂ)‖≤
      τ^2*((costUnits i:ℝ)/10^30) := by
  let m := maxBudget i
  have F : ContDiff ℝ 4 (value candidate) := by rw [← physical_evaluation]; exact trial_smooth _ _
  have G : ContDiff ℝ 2 (correctedValue σ) := trial_smooth (correctedPoly σ) _
  have v0 : 0≤v := hv ▸ mul_nonneg (Nat.cast_nonneg _) hτ
  have ve : v≤((i:ℝ)+1)/2 := by exact_mod_cast cell.2
  have lattice (k : ℕ) (hk : k≤j) :
      let a := (k:ℝ)*τ
      let b := ((j-k:ℕ):ℝ)*τ
      bridgeLocalCost a τ*(|value candidate b|+τ*|correctedValue σ b|)+|bridgeFirst a| *|correctedValue σ b|≤
        (m.lattice:ℝ)/(25000*10^60) := by
    have ab : (k:ℝ)*τ+((j-k:ℕ):ℝ)*τ=v := by rw [hv,Nat.cast_sub hk]; ring
    obtain ⟨p,q,pi,qi,low,ha,hb⟩ := split_half_bins cell (mul_nonneg (Nat.cast_nonneg _) hτ)
      (mul_nonneg (Nat.cast_nonneg _) hτ) ab
    have c := (pair_within_max test pi qi low).1
    apply (split_pair_lattice hs (by omega : p<288) (by omega : q<288) ha hb hτ ht).trans
    gcongr
  have jets (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
      splitJetBound 2 bridgeFirst (value candidate) v x+splitJetBound 2 bridgeCurve (correctedValue σ) v x≤
          (m.second:ℝ)/(4*10^60) ∧
      splitJetBound 3 bridgeCurve (value candidate) v x≤(m.third:ℝ)/10^60 ∧
      splitJetBound 4 bridgeCurve (value candidate) v x≤(m.fourth:ℝ)/10^60 := by
    obtain ⟨p,q,pi,qi,low,ha,hb⟩ := split_half_bins cell (mul_nonneg v0 hx.1)
      (mul_nonneg v0 (sub_nonneg.mpr hx.2)) (show v*x+v*(1-x)=v by ring)
    have c := (pair_within_max test pi qi low).2
    have jet := split_pair_jets hs (by omega : p<288) (by omega : q<288) ha hb
    refine ⟨jet.1.trans ?_,jet.2.1.trans ?_,jet.2.2.trans ?_⟩
    · gcongr; exact_mod_cast c.1
    · gcongr; exact_mod_cast c.2.1
    · gcongr; exact_mod_cast c.2.2
  have e := direct_corrected_residual hs hτ hω angle _ _ F G v hv
    (by positivity : 0≤(m.second:ℝ)/(4*10^60)) (by positivity : 0≤(m.fourth:ℝ)/10^60) lattice
    (fun x hx => (jets x hx).1) (fun x hx => (jets x hx).2.1) (fun x hx => (jets x hx).2.2)
  apply e.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg τ)
  have noise := (cell_noise hi hs cell hτ ht).1
  apply le_trans _ (round_cost i (splitInputs i).freeNoise m.lattice m.second m.third m.fourth)
  gcongr

end CentralUnimodality.PolynomialTrial
