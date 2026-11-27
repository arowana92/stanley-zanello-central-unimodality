module

public import CentralUnimodality.MomentSpans
public import CentralUnimodality.NormalizedCells

/-! For the two explicit witness degrees the exact cell numerators have
known exponent support. This makes direct enumeration at a finite block
of sizes a sufficient test of any proposed numerator within that support. -/
@[expose] public section

namespace CentralUnimodality.Laurent

open PowerSeries

def trueCell (m δ r : ℕ) : Laurent :=
  let T := tables m
  cellNumerator (-(δ:ℚ)/2) (rawNumerator (lookup T.1) (lookup T.2) δ) r

theorem coeff_trueCell {m n δ r : ℕ} (hδ : δ ≤ 1) (hr : r ≤ m) :
    coeff (n+δ) (eval (trueCell m δ r)) = ((δ:ℚ)+1)*Witness.rawCell n δ r := by
  have h : massFactor n δ * ratioSum (n+δ) (trueCell m δ r) = Witness.rawCell n δ r :=
    cellNumerator_exact (fun j hj => rawNumerator_exact m n δ j hδ (hj.trans hr)) (-(δ:ℚ)/2)
  rw [coeff_eval,← h,massFactor]
  field_simp

private def cellBoxes (m δ : ℕ) : List Span :=
  let T := Span.tableBoxes m
  let A := Span.rawBox (Span.boxAt T.1) (Span.boxAt T.2) δ
  let raw := (List.range (m+1)).map A
  (List.range (m+1)).map fun r => Span.cellBox (fun j => raw[j]?.getD .empty) r

private theorem span_congr {A B : ℕ → Span} {r : ℕ} (h : ∀ j ≤ r, A j = B j) :
    Span.cellBox A r = Span.cellBox B r := by
  have hs {F G : ℕ → Span} (n : ℕ) (he : ∀ j < n, F j = G j) : Span.sumBoxes F n = Span.sumBoxes G n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Span.sumBoxes,Span.sumBoxes,ih (fun j hj => he _ (by omega)),he n (by omega)]
  apply hs
  intro j hj
  rw [h j (by omega)]

private theorem trueCell_span {m r : ℕ} (hr : r ≤ m) (δ : ℕ) :
    ((cellBoxes m δ)[r]?.getD .empty).covers (trueCell m δ r) := by
  let T := Span.tableBoxes m
  let A := Span.rawBox (Span.boxAt T.1) (Span.boxAt T.2) δ
  let raw := (List.range (m+1)).map A
  have hr' : r < m+1 := by omega
  have he : (cellBoxes m δ)[r]?.getD .empty = Span.cellBox A r := by
    simp only [cellBoxes,List.getElem?_map,List.getElem?_range hr',Option.map_some,Option.getD_some]
    apply span_congr
    intro j hj
    simp [show j < m+1 by omega,A,T]
  rw [he]
  exact Span.cell_box (fun j => Span.raw_box m δ j) _ _

private def within (a b : ℤ) : Span → Bool
  | .empty => true
  | .interval c d => decide (a ≤ c ∧ d ≤ b)

private theorem within_sound {a b : ℤ} {I : Span} (hw : within a b I = true) {p : Laurent} (h : I.covers p) :
    (Span.interval a b).covers p := by
  apply Span.monotone h
  intro k hk
  cases I <;> simp_all [Span.contains,within]
  omega

set_option maxHeartbeats 2000000 in
private theorem boxes_checked : (cellBoxes 20 0).all (within (-83) 0) = true ∧
    (cellBoxes 20 1).all (within (-83) 0) = true := by decide +kernel

theorem trueCell_span20 {δ r : ℕ} (hδ : δ ≤ 1) (hr : r ≤ 20) :
    (Span.interval (-83) 0).covers (trueCell 20 δ r) := by
  apply within_sound _ (trueCell_span hr δ)
  have hm : (cellBoxes 20 δ)[r]?.getD .empty ∈ cellBoxes 20 δ := by
    have hl : r < (cellBoxes 20 δ).length := by simp [cellBoxes]; omega
    rw [List.getElem?_eq_getElem hl,Option.getD_some]
    exact List.getElem_mem hl
  rcases (by omega : δ = 0 ∨ δ = 1) with rfl|rfl
  · exact List.all_eq_true.mp boxes_checked.1 _ hm
  · exact List.all_eq_true.mp boxes_checked.2 _ hm

/-- At any starting size, 84 consecutive exact unit-cell moments determine
the candidate's agreement with the actual staircase at all subsequent sizes. -/
theorem certify_cell_samples {δ r : ℕ} (hδ : δ ≤ 1) (hr : r ≤ 20) (p : Laurent)
    (hp : (Span.interval (-83) 0).covers p) (N : ℕ)
    (h : ∀ i < 84, coeff (N+i+δ) (eval p) = ((δ:ℚ)+1)*Witness.rawCell (N+i) δ r) :
    ∀ i, coeff (N+i+δ) (eval p) = ((δ:ℚ)+1)*Witness.rawCell (N+i) δ r := by
  have he (i : ℕ) := coeff_trueCell (m := 20) (n := N+i) hδ hr
  have hblock := compare_on_span p (trueCell 20 δ r) hp (trueCell_span20 hδ hr) (N+δ) (by
    intro i hi
    rw [show N+δ+i = N+i+δ by omega,he]
    exact h i hi)
  intro i
  rw [← he,show N+i+δ = N+δ+i by omega]
  exact hblock i

end CentralUnimodality.Laurent
