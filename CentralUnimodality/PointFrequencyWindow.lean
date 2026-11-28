module

public import CentralUnimodality.PointFromCells
public import CentralUnimodality.EvenCellChecks
public import CentralUnimodality.OddCellChecks
public import CentralUnimodality.PointTaylor

/-! A rational two-variable approximation for the low-frequency amplitude
in both families. The same degree-eighteen polynomial in frequency handles
every half-length N ≥ 196, with rational coefficients in 1/N. -/
@[expose] public section

namespace CentralUnimodality.Witness
open Laurent Real PowerSeries

def sourceCells (δ : ℕ) := if δ=0 then evenCells else oddCells

def pointRow (A : Array Laurent) (j : ℕ) := polynomialFromCell (lookup A (2*j)) (2*j)

private def windowChecks (C : Array Laurent) : Bool :=
  let A := pointsFromCells C 21
  (List.range 11).all (fun j => (pointRow A j).isSome) &&
    (pointRow A 10).any (fun p => positiveSum (1/196) p≤21/200)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem checked_rows : windowChecks evenCells=true ∧ windowChecks oddCells=true := by
  decide +kernel

private theorem checked_source {δ : ℕ} (h : δ≤1) : windowChecks (sourceCells δ)=true := by
  rcases (by omega : δ=0 ∨ δ=1) with rfl|rfl
  · exact checked_rows.1
  · exact checked_rows.2

private theorem source_exact (n δ : ℕ) (hδ : δ≤1) (j : ℕ) (hj : j<21) :
    rawCell n δ j=massFactor n δ*ratioSum (n+δ) (lookup (sourceCells δ) j) := by
  have eq : coeff (n+δ) (eval (lookup (sourceCells δ) j))=((δ:ℚ)+1)*rawCell n δ j := by
    rcases (by omega : δ=0 ∨ δ=1) with rfl|rfl
    · exact evenCells_exact (by omega) n
    · exact oddCells_exact (by omega) n
  rw [coeff_eval] at eq
  unfold massFactor
  field_simp
  linear_combination -eq

theorem tabulated_point_moment {n δ r : ℕ} (hδ : δ≤1) (hn : 0<n+δ) (hr : r≤20)
    {p : List ℚ}
    (h : polynomialFromCell (lookup (pointsFromCells (sourceCells δ) 21) r) r=some p) :
    pointMoment n δ r=(if r%2=0 then 1 else wallisFactor (n+δ))*horner ((n+δ:ℕ):ℝ)⁻¹ p := by
  apply normalized_from_numerator hn _ _ h
  exact recovered_points (sourceCells δ) 21 (source_exact n δ hδ) r (by omega)

/-- Ascending powers of the reciprocal half-length. -/
def pointCoefficients (δ j : ℕ) : List ℚ :=
  (pointRow (pointsFromCells (sourceCells δ) 21) j).getD []

theorem pointCoefficients_exact {n δ j : ℕ} (hδ : δ≤1) (hn : 0<n+δ) (hj : j≤10) :
    pointMoment n δ (2*j)=horner ((n+δ:ℕ):ℝ)⁻¹ (pointCoefficients δ j) := by
  let A := pointsFromCells (sourceCells δ) 21
  have checks := checked_source hδ
  simp only [windowChecks,Bool.and_eq_true] at checks
  have hr := List.all_eq_true.mp checks.1 j (List.mem_range.mpr (by omega : j<11))
  change (pointRow A j).isSome=true at hr
  cases row : pointRow A j with
  | none => simp [row] at hr
  | some p =>
    have eq := tabulated_point_moment hδ hn (by omega : 2*j≤20) row
    change pointMoment n δ (2*j)=horner _ ((pointRow A j).getD [])
    rw [row]
    simpa only [Nat.mul_mod_right,ite_true,one_mul,Option.getD_some] using eq

private theorem twentieth_bound {n δ : ℕ} (hδ : δ≤1) (hn : 196≤n+δ) :
    pointMoment n δ 20≤21/200 := by
  let N := n+δ
  let A := pointsFromCells (sourceCells δ) 21
  have checks := checked_source hδ
  simp only [windowChecks,Bool.and_eq_true] at checks
  have check := checks.2
  change (pointRow A 10).any (fun p => decide (positiveSum (1/196) p≤21/200))=true at check
  have hN : (196:ℝ)≤(N:ℝ) := by exact_mod_cast hn
  have inv : ((N:ℝ)⁻¹)≤((1/196:ℚ):ℝ) := by
    push_cast
    rw [← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hN
  have exactMoment := pointCoefficients_exact (j:=10) hδ (by omega : 0<n+δ) (by decide)
  change pointMoment n δ 20=horner (N:ℝ)⁻¹ ((pointRow A 10).getD []) at exactMoment
  cases row : pointRow A 10 with
  | none => simp [row] at check
  | some p =>
    simp [row] at check exactMoment
    rw [exactMoment]
    have bound : positiveSum (1/196) p≤(21/200:ℚ) := by simpa only [one_div] using check
    have realBound := (Rat.cast_le (K:=ℝ)).mpr bound
    exact (horner_le_positiveSum (by positivity) inv p).trans (by push_cast at realBound; exact realBound)

noncomputable def lowFrequencyPolynomial (δ : ℕ) (x ξ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 10, (cosineCoefficient j:ℝ)*ξ^(2*j)*horner x (pointCoefficients δ j)

theorem low_frequency_error {n δ : ℕ} (hδ : δ≤1) (hn : 196≤n+δ) (ξ : ℝ) :
    |signedAmplitude n δ (ξ/cellScale (n+δ))-lowFrequencyPolynomial δ ((n+δ:ℕ):ℝ)⁻¹ ξ| ≤
      (|ξ|^20/(20:ℕ).factorial)*(21/200) := by
  have eq : momentTaylor n δ 9 ξ=lowFrequencyPolynomial δ ((n+δ:ℕ):ℝ)⁻¹ ξ := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j<10 := Finset.mem_range.mp hj
    rw [pointCoefficients_exact hδ (by omega) (by omega)]
  rw [← eq]
  exact (point_amplitude_remainder n δ 9 hδ ξ).trans
    (mul_le_mul_of_nonneg_left (twentieth_bound hδ hn) (by positivity))

theorem low_frequency_four {n δ : ℕ} (hδ : δ≤1) (hn : 196≤n+δ) {ξ : ℝ} (hξ : |ξ|≤4) :
    |signedAmplitude n δ (ξ/cellScale (n+δ))-lowFrequencyPolynomial δ ((n+δ:ℕ):ℝ)⁻¹ ξ| ≤
      1/20000000 := by
  apply (low_frequency_error hδ hn ξ).trans
  calc
    _ ≤ ((4:ℝ)^20/(20:ℕ).factorial)*(21/200) := by gcongr
    _ ≤ _ := by norm_num [Nat.factorial]

end CentralUnimodality.Witness
