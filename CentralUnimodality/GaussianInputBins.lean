module

public import CentralUnimodality.GaussianPolynomialJets

/-! The bridge and its first logarithmic correction have integer
Gaussian derivative rows. All late cells may use the single interval
[32,144], on which all the needed Gaussian monomials decrease. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial Real Set ReturnSplit

def gaussianBin (i : ℕ) := min i 64
def gaussianLo (i : ℕ) : ℚ := i/2
def gaussianHi (i : ℕ) : ℚ := if i<64 then ((i:ℚ)+1)/2 else 144

theorem gaussian_bin_covers {i : ℕ} (hi : i<288) {v : ℝ} (hv : v∈halfInterval i) :
    v∈Icc (gaussianLo (gaussianBin i):ℝ) (gaussianHi (gaussianBin i):ℝ) := by
  obtain ⟨lo,up⟩ := hv
  change (i:ℝ)/2≤v at lo
  change v≤((i+1:ℕ):ℝ)/2 at up
  simp only [Nat.cast_add,Nat.cast_one] at up
  by_cases h : i<64
  · simp [gaussianBin,min_eq_left h.le,gaussianLo,gaussianHi,h,lo,up]
  · have le : (64:ℝ)≤ i := by exact_mod_cast Nat.le_of_not_gt h
    have stop : (i:ℝ)≤287 := by exact_mod_cast (show i≤287 by omega)
    norm_num [gaussianBin,min_eq_right (Nat.le_of_not_gt h),gaussianLo,gaussianHi]
    constructor <;> linarith only [lo,up,le,stop]

def bridgeMainRow : List ℤ := [1]
def bridgeFirstRow : List ℤ := [0,0,-160,0,0,-1]

def gaussianJetUnits (b d k : ℕ) (p : List ℤ) (r : ℕ) : ℕ :=
  gaussianUnits b (gaussianLo k) (gaussianHi k) ((gaussianDifference b)^[r] p) (d*b^r)

private theorem jet_units {b d i : ℕ} (hb : 0<b) (hd : 0<d) (hi : i<288) {v : ℝ}
    (hv : v∈halfInterval i) (p : List ℤ) (r : ℕ) :
    |iteratedDeriv r (fun t => (1/(d:ℝ))*gaussianPolynomial b p t) v|≤
      (gaussianJetUnits b d (gaussianBin i) p r:ℝ)/10^30 := by
  have cover := gaussian_bin_covers hi hv
  have lp : 0≤gaussianLo (gaussianBin i) := by unfold gaussianLo; positivity
  have u := gaussian_units_bound hb (Nat.mul_pos hd (pow_pos hb r)) lp cover ((gaussianDifference b)^[r] p)
  rw [gaussian_polynomial_jet hb,abs_mul,abs_of_nonneg (by positivity : 0≤1/(d:ℝ)/(b:ℝ)^r)]
  unfold gaussianJetUnits
  apply le_trans _ u
  push_cast; apply le_of_eq; ring

theorem bridge_curve_jet {i : ℕ} (hi : i<288) {v : ℝ} (hv : v∈halfInterval i) (r : ℕ) :
    |iteratedDeriv r bridgeCurve v|≤(gaussianJetUnits 96 1 (gaussianBin i) bridgeMainRow r:ℝ)/10^30 := by
  have eq : bridgeCurve=fun t => (1/(1:ℝ))*gaussianPolynomial 96 bridgeMainRow t := by
    funext t; simp [gaussianPolynomial,bridgeMainRow,realDense,densePoly,bridgeCurve]
  rw [eq]; simpa using jet_units (b:=96) (d:=1) (by decide) (by decide) hi hv bridgeMainRow r

theorem bridge_first_jet {i : ℕ} (hi : i<288) {v : ℝ} (hv : v∈halfInterval i) (r : ℕ) :
    |iteratedDeriv r bridgeFirst v|≤(gaussianJetUnits 96 30720 (gaussianBin i) bridgeFirstRow r:ℝ)/10^30 := by
  have eq : bridgeFirst=fun t => (1/(30720:ℝ))*gaussianPolynomial 96 bridgeFirstRow t := by
    funext t
    simp [gaussianPolynomial,bridgeFirstRow,realDense,densePoly,bridgeFirst,bridgeCurve,bridgeLogCorrection]; ring
  rw [eq]; exact jet_units (b:=96) (d:=30720) (by decide) (by decide) hi hv _ _

end CentralUnimodality.PolynomialTrial
