module

public import CentralUnimodality.CubicPairEstimates
public import CentralUnimodality.QuadraticAmplitude
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-! Apply the seven independently maximized bounds to the discrete
last-return residual at the actual split of a retained frequency. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial ReturnSplit Set

set_option maxRecDepth 12000

private theorem round_cubic (i n a b c d e f g : ℕ) :
    let h := ((i:ℝ)+1)/2
    (n:ℝ)/10^30+a/(5000*10^60)+h*(b/10^60)/8+h*(c/10^60)/24+h^2*(d/10^60)/128+
      h*(e/10^60)/96+h^2*(f/10^60)/192+h^3*(g/10^60)/1440≤
    (ceilQuotient (2880000*n*10^30+576*a+180000*(i+1)*b+60000*(i+1)*c+5625*(i+1)^2*d+
      15000*(i+1)*e+3750*(i+1)^2*f+250*(i+1)^3*g) (2880000*10^30):ℝ)/10^30 := by
  let A := 2880000*n*10^30+576*a+180000*(i+1)*b+60000*(i+1)*c+5625*(i+1)^2*d+
    15000*(i+1)*e+3750*(i+1)^2*f+250*(i+1)^3*g
  let D : ℕ := 2880000*10^30
  have h : A≤D*ceilQuotient A D := (ceilDiv_le_iff_le_mul (by decide : 0<D)).mp (le_refl _)
  have hr : (A:ℝ)≤(D:ℝ)*(ceilQuotient A D:ℝ) := by exact_mod_cast h
  change _≤(ceilQuotient A D:ℝ)/10^30
  generalize hx : (ceilQuotient A D:ℝ)=x at hr ⊢
  dsimp only [A,D] at hr
  push_cast at hr
  linarith only [hr]

private theorem poly_smooth (P : ℝ[X]) (k : ℕ) : ContDiff ℝ k P.eval := by
  simpa only [Polynomial.aeval_def,Algebra.algebraMap_self,Polynomial.eval₂_id] using P.contDiff_aeval (𝕜:=ℝ) k

theorem cubic_residual_of_inputs {σ i j N : ℕ} (hs : σ≤1) (hj : j≤N) (hn : 10000≤N)
    {ω τ v : ℝ} (t0 : 0≤τ) (phase : ω^2=τ^3/32) (ht : (N:ℝ)*τ≤114) (hv : v=j*τ) (cell : v∈halfInterval i)
    (ready : ∀ k≤ i, (cubeInput k).Sound k) (row : cubicMaxData[i]?=some (cubicMaxRow i)) :
    ‖parityResidual ω (correctedSeries σ τ) σ j-((curveResidual (value candidate) v+
      τ*firstCurveResidual (value candidate) (correctedValue σ) σ v+
      τ^2*secondCurveResidual (value candidate) (correctedValue σ) σ v:ℝ):ℂ)‖≤τ^3*((cubicUnits i:ℝ)/10^30) := by
  let F := value candidate
  let G := correctedValue σ
  let m := fun r => (cubicMaxNum i r:ℝ)
  have hF : ContDiff ℝ 6 F := by dsimp only [F]; rw [← physical_evaluation]; exact poly_smooth _ _
  have hG : ContDiff ℝ 4 G := poly_smooth (correctedPoly σ) _
  have v0 : 0≤v := hv ▸ mul_nonneg (Nat.cast_nonneg _) t0
  have ve : v≤((i:ℝ)+1)/2 := by exact_mod_cast cell.2
  have nr : (10000:ℝ)≤N := by exact_mod_cast hn
  have step : τ≤57/5000 := by linarith only [mul_le_mul_of_nonneg_right nr t0,ht]
  have lattice (k : ℕ) (hk : k≤j) : let a := (k:ℝ)*τ; let b := ((j-k:ℕ):ℝ)*τ
      bridgeQuadraticCost a τ*(|F b|+τ*|G b|)+|bridgeSecond a| * |G b|≤m 0/(5000*10^60) := by
    have total : (k:ℝ)*τ+((j-k:ℕ):ℝ)*τ=v := by rw [hv,Nat.cast_sub hk]; ring
    obtain ⟨p,q,pi,qi,low,ha,hb⟩ := split_half_bins cell (mul_nonneg (Nat.cast_nonneg _) t0)
      (mul_nonneg (Nat.cast_nonneg _) t0) total
    have bound := cubic_pair_lattice hs (ready _ pi) (ready q (by omega)) ha hb t0 step
    exact bound.trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr (cubic_pair_le pi qi low (by decide : 0<7) row)) (by positivity))
  have jets (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
      (splitJetBound 2 bridgeSecond F v x+splitJetBound 2 bridgeFirst G v x≤m 1/10^60) ∧
      (splitJetBound 3 bridgeFirst F v x+splitJetBound 3 bridgeCurve G v x≤m 2/10^60) ∧
      (splitJetBound 4 bridgeFirst F v x+splitJetBound 4 bridgeCurve G v x≤m 3/10^60) ∧
      (splitJetBound 4 bridgeCurve F v x≤m 4/10^60) ∧ (splitJetBound 5 bridgeCurve F v x≤m 5/10^60) ∧
      (splitJetBound 6 bridgeCurve F v x≤m 6/10^60) := by
    obtain ⟨p,q,pi,qi,low,ha,hb⟩ := split_half_bins cell (mul_nonneg v0 hx.1)
      (mul_nonneg v0 (sub_nonneg.mpr hx.2)) (show v*x+v*(1-x)=v by ring)
    obtain ⟨a,b,c,d,e,f⟩ := cubic_pair_jets hs (ready _ pi) (ready q (by omega)) ha hb
    have cap (r : ℕ) (hr : r<7) :
        (cubicPairEntry (cubeInput p) (cubeInput q) r:ℝ)/10^60≤m r/10^60 :=
      div_le_div_of_nonneg_right (Nat.cast_le.mpr (cubic_pair_le pi qi low hr row)) (by positivity)
    exact ⟨a.trans (cap _ (by decide)),b.trans (cap _ (by decide)),c.trans (cap _ (by decide)),
      d.trans (cap _ (by decide)),e.trans (cap _ (by decide)),f.trans (cap _ (by decide))⟩
  have actual := quadratic_split_residual hs t0 phase hj hn ht F G hF hG v hv lattice
    (fun x hx => (jets x hx).1) (fun x hx => (jets x hx).2.1) (fun x hx => (jets x hx).2.2.1)
    (fun x hx => (jets x hx).2.2.2.1) (fun x hx => (jets x hx).2.2.2.2.1) (fun x hx => (jets x hx).2.2.2.2.2)
  have noise := ((ready i le_rfl).noise hs cell t0 step).1
  apply actual.trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg t0 3)
  apply le_trans _ (round_cubic i (cubeInput i).freeNoise (cubicMaxNum i 0) (cubicMaxNum i 1) (cubicMaxNum i 2)
    (cubicMaxNum i 3) (cubicMaxNum i 4) (cubicMaxNum i 5) (cubicMaxNum i 6))
  dsimp only [m]
  gcongr

end CentralUnimodality.PolynomialTrial
