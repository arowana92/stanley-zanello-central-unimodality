module

public import CentralUnimodality.GaussianInputBins

/-! Upper bounds for the lattice remainders in a time cell. The
squared logarithm is kept inside its Gaussian when taking a maximum. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Polynomial Real Set ReturnSplit

def logSquareRow (c : ℕ) : List ℤ := [0,0,0,0,(c:ℤ)^2,0,0,2*c,0,0,1]

private theorem square_eval (b c : ℕ) (v : ℝ) :
    gaussianPolynomial b (logSquareRow c) v=exp (-(v^3/b))*((c:ℝ)*v^2+v^5)^2 := by
  simp [gaussianPolynomial,logSquareRow,realDense,densePoly]; ring

def maxStep : ℚ := 1/1250
def freeRemainderQ (v t : ℚ) := 13*v/192+t/64+(v+t)^4/384+(1/20)*(v+t)^7/1792
def bridgeRemainderQ (v t : ℚ) := (7*v^4+2*t*v^3)/(180*32^2)+(1/1000)*(v+t)^7/1792

def noiseUnits (b c d k : ℕ) (rem : ℚ) : ℕ :=
  let l := gaussianLo k
  let h := gaussianHi k
  ⌈10^30*rem*scaledNegExp (l^3/b)+(gaussianUnits b l h (logSquareRow c) (d^2):ℚ)/2⌉₊

private theorem noise_bound {b c d i : ℕ} (bp : 0<b) (dp : 0<d) (hi : i<288) {v R L : ℝ}
    (hv : v∈halfInterval i) {rem : ℚ} (r0 : 0≤R) (rle : R≤(rem:ℝ)) (l0 : 0≤L)
    (lle : L≤((c:ℝ)*v^2+v^5)/d) :
    exp (-(v^3/b))*R+exp (-(v^3/b))*L^2/2≤(noiseUnits b c d (gaussianBin i) rem:ℝ)/10^30 := by
  let k := gaussianBin i
  let l := gaussianLo k
  let h := gaussianHi k
  let E := exp (-(v^3/b))
  have cover : v∈Icc (l:ℝ) (h:ℝ) := gaussian_bin_covers hi hv
  have lp : 0≤l := by dsimp [l,gaussianLo]; positivity
  have lr : 0≤(l:ℝ) := by exact_mod_cast lp
  have br : 0<(b:ℝ) := by exact_mod_cast bp
  have le : E≤exp (-((l:ℝ)^3/b)) :=
    exp_le_exp.mpr (neg_le_neg (div_le_div_of_nonneg_right (pow_le_pow_left₀ lr cover.1 3) br.le))
  have ex := scaledNegExp_sound (x:=l^3/b) (by positivity)
  push_cast at ex
  have tp := le.trans ex
  have prod := mul_le_mul tp rle r0 ((exp_nonneg _).trans ex)
  have eu := gaussian_units_bound bp (pow_pos dp 2) lp cover (logSquareRow c)
  rw [square_eval,abs_of_nonneg (mul_nonneg (exp_nonneg _) (sq_nonneg _)),Nat.cast_pow] at eu
  have scale : E*(((c:ℝ)*v^2+v^5)/d)^2=E*((c:ℝ)*v^2+v^5)^2/d^2 := by ring
  have log := (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ l0 lle 2) (exp_nonneg (-(v^3/b)))).trans
    (scale.le.trans eu)
  let u := gaussianUnits b l h (logSquareRow c) (d^2)
  have rounded := (Rat.cast_le (K:=ℝ)).mpr (Nat.le_ceil (10^30*rem*scaledNegExp (l^3/b)+(u:ℚ)/2))
  push_cast at rounded
  change E*R+E*L^2/2≤(⌈10^30*rem*scaledNegExp (l^3/b)+(u:ℚ)/2⌉₊:ℕ)/ (10^30:ℝ)
  dsimp only [u] at rounded ⊢
  change E*L^2≤_ at log
  linarith only [rounded,prod,log]

def freeNoiseUnits (k : ℕ) := noiseUnits 24 180 1920 k (freeRemainderQ (gaussianHi k) maxStep)
def bridgeNoiseUnits (k : ℕ) := noiseUnits 96 160 30720 k (bridgeRemainderQ (gaussianHi k) maxStep)

theorem free_noise_bound {i σ : ℕ} (hi : i<288) (hs : σ≤1) {v τ : ℝ} (hv : v∈halfInterval i)
    (t0 : 0≤τ) (step : τ≤(maxStep:ℝ)) : freeLocalCost σ v τ≤(freeNoiseUnits (gaussianBin i):ℝ)/10^30 := by
  have vv := gaussian_bin_covers hi hv
  have v0 : 0≤v := le_trans (by positivity : (0:ℝ)≤(i:ℝ)/2) hv.1
  change _≤(noiseUnits 24 180 1920 _ _:ℝ)/10^30
  apply noise_bound (by decide) (by decide) hi hv
  · unfold freeLogRemainder; positivity
  · unfold freeRemainderQ freeLogRemainder
    push_cast
    gcongr <;> exact vv.2
  · unfold freeLogCorrection; positivity
  · have le : (2*(σ:ℝ)+1)*v^2≤3*v^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have h : (σ:ℝ)≤1 := by exact_mod_cast hs
      linarith
    unfold freeLogCorrection
    push_cast; linarith only [le]

theorem bridge_noise_bound {i : ℕ} (hi : i<288) {v τ : ℝ} (hv : v∈halfInterval i)
    (t0 : 0≤τ) (step : τ≤(maxStep:ℝ)) : bridgeLocalCost v τ≤(bridgeNoiseUnits (gaussianBin i):ℝ)/10^30 := by
  have vv := gaussian_bin_covers hi hv
  have v0 : 0≤v := le_trans (by positivity : (0:ℝ)≤(i:ℝ)/2) hv.1
  change _≤(noiseUnits 96 160 30720 _ _:ℝ)/10^30
  apply noise_bound (by decide) (by decide) hi hv
  · unfold bridgeLogRemainder; positivity
  · unfold bridgeRemainderQ bridgeLogRemainder
    push_cast
    have step0 := t0.trans step
    gcongr <;> exact vv.2
  · unfold bridgeLogCorrection; positivity
  · unfold bridgeLogCorrection; push_cast; apply le_of_eq; ring

end CentralUnimodality.PolynomialTrial
