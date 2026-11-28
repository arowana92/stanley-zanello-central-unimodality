module

public import CentralUnimodality.SpatialMarginBounds

/-! Read the even moments of the spatial Taylor polynomial from a shared
table. Odd moments are multiplied by the exact zero of the phase. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

private theorem phase_even : ∀ k, phaseInt k ≠ 0 → k%2=0
  | 0, _ => rfl
  | 1, h => False.elim (h rfl)
  | k+2, h => by
    have z : phaseInt k≠0 := fun hz => h (by simp [phaseInt,hz])
    have := phase_even k z; omega

def tabulatedRow (r D : ℕ) (ms : Array ℤ) : List ℤ :=
  let fact := D.factorial
  (List.range (D+1)).map fun j =>
    let s := phaseInt (r+j)
    if s=0 then 0 else 3*s*(512:ℤ)^(r+j+1)*(fact/j.factorial:ℕ)*ms[(r+j)/2]?.getD 0

theorem tabulated_row_exact {r D : ℕ} {a : List ℤ} (ms : Array ℤ)
    (h : ∀ i≤(r+D)/2, ms[i]?.getD 0=unitNumerator (fun k => momentDivisor (momentTop r D a)/k)
      (quarterWeights a).1 (6*i+2)) : tabulatedRow r D ms=integratedRow r D a := by
  unfold tabulatedRow integratedRow
  apply List.map_congr_left
  intro j hj
  have bound := List.mem_range.mp hj
  simp only [integratedCoeff]
  split_ifs with hz
  · rfl
  · have par := phase_even (r+j) hz
    rw [h _ (by omega), show 6*((r+j)/2)+2=3*(r+j)+2 by omega]

end CentralUnimodality.PolynomialTrial
