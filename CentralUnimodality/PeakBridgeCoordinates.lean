module

public import CentralUnimodality.PeakGrowthNumbers
public import CentralUnimodality.MarkedHitBound
public import CentralUnimodality.RankBinSetup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Dimensionless coordinates for the marked-point bound on a centered
first-passage excursion. All bounds are uniform over the full time cell. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
open Real

theorem centered_time_coordinates {m d : ℕ} (hm : 0<m) (c : ℝ) :
    let t := 2*(d:ℝ)+1
    let x := t/m
    let δ := 1/(m:ℝ)
    let lam := 2*c*sizeScale m
    c*d = lam*(x-δ)/(4*√m) ∧
      c*t*√((d:ℝ)+1) = lam*x/2*√((x+δ)/2) ∧
      c^2*d*(d+1)*t/6=lam^2*x*(x^2-δ^2)/96 := by
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have ht : (0:ℝ)≤(d:ℝ)+1 := by positivity
  have he : (((2*(d:ℝ)+1)/(m:ℝ)+1/(m:ℝ))/2)=((d:ℝ)+1)/m := by field_simp; ring
  dsimp only [sizeScale]
  rw [he,sqrt_div ht]
  constructor
  · field_simp; ring
  constructor
  · field_simp
  · simp only [mul_pow,sq_sqrt hm'.le]; field_simp; ring

/-- Outward bounds on the two positive exponents and the amount saved by
the hyperbolic-cosine normalizer. Here `w` bounds the square-root factor
in the marked-point displacement and `b` bounds the opposite endpoint. -/
theorem centered_time_bounds {m d : ℕ} (hm : 4096≤m) {c g G v e w : ℝ}
    (hc : 0≤c) (hg : 0≤g) (hlam : g≤2*c*sizeScale m) (hLam : 2*c*sizeScale m≤G)
    (hv : 1/4096≤v) (hl : v*m≤2*(d:ℝ)+1) (hh : 2*(d:ℝ)+1≤e*m)
    (hw : √((e+1/4096)/2)≤w) (hcap : G*e/256≤1) :
    let t := 2*(d:ℝ)+1
    let y := c*t*√((d:ℝ)+1)
    let q := G*e/256
    let Y := G*e*w/2
    let save := g^2*v*(v^2-(1/4096)^2)/96*(1-q^2/6)
    c*d≤q ∧ y≤Y ∧ save≤c^2*d*(d+1)*t/6*(1-(c*d)^2/6) := by
  let t := 2*(d:ℝ)+1
  let x := t/m
  let δ := 1/(m:ℝ)
  let lam := 2*c*sizeScale m
  have hM : (4096:ℝ)≤m := by exact_mod_cast hm
  have hm' : (0:ℝ)<m := by linarith only [hM]
  have hr := sqrt_pos.mpr hm'
  have h64 : 64≤√(m:ℝ) := (le_sqrt (by norm_num) hm'.le).mpr (by linarith only [hM])
  have hδ : δ≤1/4096 := one_div_le_one_div_of_le (by norm_num) hM
  have hδ' : 0≤δ := by dsimp [δ]; positivity
  have hx : v≤x := (le_div_iff₀ hm').mpr hl
  have hx' : x≤e := (div_le_iff₀ hm').mpr hh
  have hv' : 0≤v := by linarith only [hv]
  have hx₀ := hv'.trans hx
  have he := hx₀.trans hx'
  have hG := (hg.trans hlam).trans hLam
  have hLam₀ : 0≤lam := hg.trans hlam
  have ⟨hd,hy,hs⟩ := centered_time_coordinates (d:=d) (by omega : 0<m) c
  change c*d=lam*(x-δ)/(4*√m) at hd
  change c*t*√((d:ℝ)+1)=lam*x/2*√((x+δ)/2) at hy
  change c^2*d*(d+1)*t/6=lam^2*x*(x^2-δ^2)/96 at hs
  have hprod := mul_le_mul hLam hx' hx₀ hG
  have hcd : c*d≤G*e/256 := by
    rw [hd]; apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hprod,mul_nonneg hLam₀ hδ',mul_le_mul_of_nonneg_left h64 (mul_nonneg hG he)]
  have hroot := (sqrt_le_sqrt (show (x+δ)/2≤(e+1/4096)/2 by linarith only [hδ,hx'])).trans hw
  have hy' := mul_le_mul (show lam*x/2≤G*e/2 by linarith only [hprod]) hroot (sqrt_nonneg _) (by positivity)
  have hsq : v^2-(1/4096)^2 ≤ x^2-δ^2 := by
    linarith only [pow_le_pow_left₀ hv' hx 2,pow_le_pow_left₀ hδ' hδ 2]
  have hsq₀ : 0≤v^2-(1/4096)^2 := sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) hv 2)
  have ht₁ := mul_le_mul (pow_le_pow_left₀ hg hlam 2) hx hv' (sq_nonneg _)
  have ht₂ := mul_le_mul ht₁ hsq hsq₀ (mul_nonneg (sq_nonneg lam) hx₀)
  have hq := (show 0≤c*d by positivity).trans hcd
  have hq' : 1-(G*e/256)^2/6≤1-(c*d)^2/6 := by linarith only [pow_le_pow_left₀ (by positivity) hcd 2]
  have hq₀ : 0≤1-(G*e/256)^2/6 := by linarith only [pow_le_pow_left₀ hq hcap 2]
  refine ⟨hcd,by change c*t*√((d:ℝ)+1)≤_; rw [hy]; linarith only [hy'],?_⟩
  change _≤c^2*d*(d+1)*t/6*_
  rw [hs]
  exact mul_le_mul (div_le_div_of_nonneg_right ht₂ (by norm_num)) hq' hq₀
    (div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hx₀) (hsq₀.trans hsq)) (by norm_num))

end CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
