module

public import CentralUnimodality.TiltedWallProducts
public import CentralUnimodality.InnerArcNumbers
public import CentralUnimodality.ArcEnvelope

/-! Rational verification of the one-block exponential rates for the
four outer frequency intervals of the tilted rank transform. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

structure PairArcSpec where
  maxLen : ℕ
  sineSq : ℚ
  narrowRate : ℚ
  wideRate : ℚ

def pairArc : Fin 4 → PairArcSpec
  | 0 => ⟨25, 0.99, 0.013, 0.012⟩
  | 1 => ⟨17, 0.99, 0.019, 0.016⟩
  | 2 => ⟨13, 0.98, 0.022, 0.019⟩
  | 3 => ⟨6, 0.75, 0.028, 0.019⟩

def pairRate (s : Fin 4) (wide : Bool) : ℚ :=
  if wide then (pairArc s).wideRate else (pairArc s).narrowRate

def pairWeight (wide : Bool) : ℚ := if wide then 3/25 else 1/5

private theorem pairParams (s : Fin 4) (wide : Bool) :
    0 ≤ pairRate s wide ∧ 0 ≤ pairWeight wide ∧ 0 ≤ (pairArc s).sineSq ∧ (pairArc s).maxLen ≤ 25 := by
  fin_cases s <;> cases wide <;> decide +kernel

set_option maxRecDepth 10000 in
private theorem pair_rates_checked : ∀ (s : Fin 4) (wide : Bool) (l : Fin 26), l.val ≤ (pairArc s).maxLen →
    let x := pairWeight wide*l.val*(pairArc s).sineSq
    let y := 2*pairRate s wide*l.val
    (1+upperNegExp x)/2 ≤ (1-y/128)^128 ∧ y ≤ 128 := by
  decide +kernel

/-- The specified rate holds for every integer spacing in the arc's range. -/
theorem tilted_pair_rate (s : Fin 4) (wide : Bool) {l : ℕ} {θ : ℝ}
    (hl : l ≤ (pairArc s).maxLen) (hsin : ((pairArc s).sineSq:ℝ) ≤ sin (l*θ/2)^2) :
    (1+exp (-(pairWeight wide:ℝ)*l*sin (l*θ/2)^2))/2 ≤ exp (-2*(pairRate s wide:ℝ)*l) := by
  let w := pairWeight wide
  let η := pairRate s wide
  let x := w*l*(pairArc s).sineSq
  let y := 2*η*l
  obtain ⟨_,hw,hs,hm⟩ := pairParams s wide
  have h := pair_rates_checked s wide ⟨l,by omega⟩ hl
  change (1+upperNegExp x)/2 ≤ (1-y/128)^128 ∧ y ≤ 128 at h
  have hx : 0 ≤ x := mul_nonneg (mul_nonneg hw (Nat.cast_nonneg _)) hs
  have h₁ : (1+exp (-(pairWeight wide:ℝ)*l*sin (l*θ/2)^2))/2 ≤ (1+(upperNegExp x:ℝ))/2 := by
    have hw' : 0 ≤ (w:ℝ) := by exact_mod_cast hw
    have H := mul_le_mul_of_nonneg_left hsin (mul_nonneg hw' (Nat.cast_nonneg (α:=ℝ) l))
    have hh : -(w:ℝ)*l*sin (l*θ/2)^2 ≤ -(x:ℝ) := by dsimp [x]; push_cast; linarith only [H]
    linarith only [(exp_le_exp.mpr hh).trans (upperNegExp_sound hx)]
  have h₂ : (1+(upperNegExp x:ℝ))/2 ≤ (1-(y:ℝ)/128)^128 := by exact_mod_cast h.1
  apply h₁.trans (h₂.trans ((rate_lower_exp y (by exact_mod_cast h.2)).trans_eq _))
  congr 1; dsimp [y,η]; push_cast; ring

end CentralUnimodality.MarkedExcursion
