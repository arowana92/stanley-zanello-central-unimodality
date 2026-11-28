module

public import CentralUnimodality.GaussianInputBins
public import CentralUnimodality.QuadraticLatticeResidual

/-! Exact integer rows for the Gaussian noise and second bridge symbol
at the maximal time step 114/10000. Each coefficient identity is checked
against the signed logarithmic expansion. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open ReturnSplit Real Set Polynomial

def freeCubicNoise : List ℤ := [2480625019141462983841873760103189195591,13432600295772144121660412522835000,7683481030459941592687864043100000000,1455644939600587687099855213500000000000,26865171735144717791250000000000000,1181979314589174806250000000000000000,70252090508458687500000000000000000000,575682187500000000000000000000000,17596279907226562500000000000000000,832489013671875000000000000000000000,0,43835449218750000000000000000000,3044128417968750000000000000000000,0,139160156250000000000000000000,3738403320312500000000000000000]
def freeCubicNoiseDen : ℕ := 158760000000000000000000000000000000000000

def bridgeSecondPolyRow : List ℤ := [0,0,0,0,-322560,0,0,-320,0,0,7]
def bridgeSecondPolyRowDen : ℕ := 13212057600

def bridgeCubicNoise : List ℤ := [768240421178594722324369137,404337064515311622887659845000,88670409175898815048301700000000,5512510370808158809698986494500000000000,682290020896013024538750000000000000,23940001832983598643750000000000000000,462451279067023312500000000000000000000,4029775312500000000000000000000000,92548809814453125000000000000000000,2226379394531250000000000000000000000,0,42617797851562500000000000000000,4606246948242187500000000000000000,0,108718872070312500000000000000,2920627593994140625000000000000]
def bridgeCubicNoiseDen : ℕ := 508032000000000000000000000000000000000000000

private theorem noise_at_max (v : ℝ) :
    freeQuadraticCost 1 v (57/5000)=gaussianPolynomial 24 freeCubicNoise v/freeCubicNoiseDen+1/10^18 ∧
    bridgeQuadraticCost v (57/5000)=gaussianPolynomial 96 bridgeCubicNoise v/bridgeCubicNoiseDen+1/10^18 := by
  constructor <;>
    norm_num [freeQuadraticCost,bridgeQuadraticCost,quadraticSymbolCost,freeCurve,bridgeCurve,freeLogCorrection,
      bridgeLogCorrection,freeSecondLog,bridgeSecondLog,freeThirdLogBound,bridgeThirdLogBound,gaussianPolynomial,
      freeCubicNoise,freeCubicNoiseDen,bridgeCubicNoise,bridgeCubicNoiseDen,realDense,densePoly] <;> ring

private theorem noise_monotone {σ : ℕ} (hs : σ≤1) {v τ : ℝ} (v0 : 0≤v) (t0 : 0≤τ) (ht : τ≤57/5000) :
    freeQuadraticCost σ v τ≤freeQuadraticCost 1 v (57/5000) ∧
      bridgeQuadraticCost v τ≤bridgeQuadraticCost v (57/5000) := by
  have s : (σ:ℝ)≤1 := by exact_mod_cast hs
  constructor <;>
    simp only [freeQuadraticCost,bridgeQuadraticCost,quadraticSymbolCost,freeCurve,bridgeCurve,
      freeLogCorrection,bridgeLogCorrection,freeSecondLog,bridgeSecondLog,freeThirdLogBound,bridgeThirdLogBound,
      Nat.cast_one] <;> gcongr

def noiseCellNum (b d k : ℕ) (p : List ℤ) :=
  gaussianUnits b (gaussianLo k) (gaussianHi k) p d+10^12

private theorem noise_cell {b d i : ℕ} (bp : 0<b) (dp : 0<d) (hi : i<288) {v : ℝ} (hv : v∈halfInterval i)
    (p : List ℤ) :
    gaussianPolynomial b p v/d+1/10^18≤(noiseCellNum b d (gaussianBin i) p:ℝ)/10^30 := by
  have gauss := gaussian_units_bound bp dp (show 0≤gaussianLo (gaussianBin i) by unfold gaussianLo; positivity)
    (gaussian_bin_covers hi hv) p
  have a := div_le_div_of_nonneg_right (le_abs_self (gaussianPolynomial b p v)) (Nat.cast_nonneg (α:=ℝ) d)
  unfold noiseCellNum
  push_cast
  linarith only [gauss,a]

theorem quadratic_gaussian_noise {σ i : ℕ} (hs : σ≤1) (hi : i<228) {v τ : ℝ} (hv : v∈halfInterval i)
    (t0 : 0≤τ) (ht : τ≤57/5000) :
    freeQuadraticCost σ v τ≤(noiseCellNum 24 freeCubicNoiseDen (gaussianBin i) freeCubicNoise:ℝ)/10^30 ∧
    bridgeQuadraticCost v τ≤(noiseCellNum 96 bridgeCubicNoiseDen (gaussianBin i) bridgeCubicNoise:ℝ)/10^30 := by
  have v0 : 0≤v := (show (0:ℝ)≤(i:ℝ)/2 by positivity).trans hv.1
  obtain ⟨f,b⟩ := noise_monotone hs v0 t0 ht
  rw [(noise_at_max v).1] at f
  rw [(noise_at_max v).2] at b
  exact ⟨f.trans (noise_cell (by decide) (by decide) (by omega) hv _),
    b.trans (noise_cell (by decide) (by decide) (by omega) hv _)⟩

theorem second_bridge_jet {i : ℕ} (hi : i<288) {v : ℝ} (hv : v∈halfInterval i) (r : ℕ) :
    |iteratedDeriv r bridgeSecond v|≤(gaussianJetUnits 96 bridgeSecondPolyRowDen (gaussianBin i) bridgeSecondPolyRow r:ℝ)/10^30 := by
  have eq : bridgeSecond=fun t => (1/(bridgeSecondPolyRowDen:ℝ))*gaussianPolynomial 96 bridgeSecondPolyRow t := by
    funext t
    norm_num [bridgeSecond,bridgeCurve,bridgeLogCorrection,bridgeSecondLog,gaussianPolynomial,
      bridgeSecondPolyRow,bridgeSecondPolyRowDen,realDense,densePoly]; ring
  have lp : 0≤gaussianLo (gaussianBin i) := by unfold gaussianLo; positivity
  have u := gaussian_units_bound (by decide : 0<96) (Nat.mul_pos (by decide : 0<bridgeSecondPolyRowDen)
    (pow_pos (by decide : 0<96) r)) lp (gaussian_bin_covers hi hv) ((gaussianDifference 96)^[r] bridgeSecondPolyRow)
  rw [eq,gaussian_polynomial_jet (by decide : 0<96),abs_mul,abs_of_nonneg (by positivity : 0≤1/(bridgeSecondPolyRowDen:ℝ)/((96:ℕ):ℝ)^r)]
  unfold gaussianJetUnits
  apply le_trans _ u
  push_cast; apply le_of_eq; ring

end CentralUnimodality.PolynomialTrial
