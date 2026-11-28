module

public import CentralUnimodality.RoundedQuadraticRows
public import CentralUnimodality.SecondResidualTransfer
public import CentralUnimodality.LocalJetTable

/-! A half-unit cell bound for the signed Gaussian residual. It allows a
truncated Chebyshev row and charges the absolute mass of the discarded tail. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open ReturnSplit Set

theorem local_quadratic_residual {σ i k b bits : ℕ} (hs : σ≤1) (hi : i<288)
    (a : List ℤ) (row : quadraticChebRow σ=a)
    (raw : List ℤ) (unpack : unpackCheb bits (a.take k)=raw)
    (small : (coefficientMass (a.take k):ℤ)*7^(a.take k).length<2^bits)
    (cap : coefficientMass raw*1024^raw.length<2^5376)
    (tab : (localJetTable raw i 1)[0]?=some b) {v : ℝ} (hv : v∈halfInterval i) :
    |secondCurveResidual (value candidate) (correctedValue σ) σ v|≤
      (b:ℝ)/10^30+3/10^7+
      (2*((quadraticResidualRow σ).numer.length:ℝ)+1+coefficientMass (a.drop k))/2^120 := by
  have v0 : 0≤v := (show (0:ℝ) ≤ (i:ℝ)/2 by positivity).trans hv.1
  have v144 : v≤144 := by
    have j : ((i+1:ℕ):ℝ)≤288 := by exact_mod_cast (by omega : i+1≤288)
    linarith only [hv.2,j]
  have range : v∈Icc (0:ℝ) 256 := ⟨v0,by linarith only [v144]⟩
  have gaussian := second_residual_transfer hs (show v∈Icc (0:ℝ) 144 from ⟨v0,v144⟩)
  have rounding := quadratic_cheb_row_sound hs range
  rw [row] at rounding
  have tail := take_cheb_value a k range
  have rep (x : ℝ) : value (doubleHead (a.take k)) x=(realDense raw).eval (x/256)/2^120 := by
    rw [← unpack]; exact normalized_input bits _ small x
  have cell := localJetTable_bound raw rep cap hi (by decide : 0<1) tab hv
  simp only [iteratedDeriv_zero] at cell
  have bound := (abs_le.mp gaussian).1
  have low := (abs_le.mp gaussian).2
  rw [abs_le] at rounding tail cell ⊢
  constructor <;> linarith only [bound,low,rounding.1,rounding.2,tail.1,tail.2,cell.1,cell.2]

end CentralUnimodality.PolynomialTrial
