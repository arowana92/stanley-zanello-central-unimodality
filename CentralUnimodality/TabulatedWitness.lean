module

public import CentralUnimodality.WitnessSigns
public import CentralUnimodality.WitnessTables

/-! Use supplied cell numerators whose size coefficients have been checked
against the partition counts. The endpoint sign tests then operate only
on the two ordinary reciprocal-size polynomials. -/
@[expose] public section

namespace CentralUnimodality.Witness

open Laurent PowerSeries

def suppliedPair (C : Array Laurent) (v : Data) :=
  buildPair (fun r => polynomialFromCell (lookup C r) r) 0 (coefficients v.B v.t v.roots)

def suppliedCheck (C : Array Laurent) (v : Data) (ε : ℚ) : Bool :=
  match suppliedPair C v with
  | none => false
  | some pair => upperTest pair Wallis.lower Wallis.lowerConstant ε &&
      upperTest pair Wallis.upper Wallis.upperConstant ε

theorem suppliedCheck_sound {n δ : ℕ} (hn : 96 ≤ n+δ) (C : Array Laurent) (v : Data)
    (h : ∀ r < (coefficients v.B v.t v.roots).length, coeff (n+δ) (eval (lookup C r)) =
      ((δ:ℚ)+1)*rawCell n δ r)
    {ε : ℚ} (hs : suppliedCheck C v ε = true) :
    polyExpectation (normalizedCell n δ) 0 (coefficients v.B v.t v.roots) ≤ -(ε:ℝ) := by
  cases ht : suppliedPair C v with
  | none => simp [suppliedCheck,ht] at hs
  | some pair =>
    simp only [suppliedCheck,ht,Bool.and_eq_true] at hs
    apply le_trans _ (upperTests_sound hn hs.1 hs.2)
    apply le_of_eq
    apply buildPair_sound _ (fun r => polynomialFromCell (lookup C r) r) _ _ _ 0 ht
    intro r _ hr q hq
    apply normalizedCell_from_numerator (by omega) _ _ hq
    have he := h r (by simpa using hr)
    rw [coeff_eval] at he
    unfold massFactor
    field_simp
    linear_combination -he

set_option maxRecDepth 100000 in
theorem supplied_first_signs :
    suppliedCheck evenCells first (1/10000000000) = true ∧
    suppliedCheck oddCells first (1/10000000000) = true := by decide +kernel

end CentralUnimodality.Witness
