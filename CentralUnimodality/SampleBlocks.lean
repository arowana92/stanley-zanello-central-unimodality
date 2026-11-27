module

public import CentralUnimodality.CellVerifier

/-! One row of a moment certificate shares a packed rank row and the
84 root coefficients across all 21 orders. Every cell numeral is then
tested against the independent integer endpoint calculation. -/
@[expose] public section

namespace CentralUnimodality.Laurent

open PowerSeries

def coefficientRow (N : ℕ) : Array ℚ :=
  ((List.range 84).map fun i : ℕ => rootCoeffValue (-(i:ℤ)) N).toArray

def memoRoot (row : Array ℚ) (h : ℤ) := row[(-h).toNat]?.getD 0

private theorem memoRoot_valid {h : ℤ} (hn : -83 ≤ h) (hp : h ≤ 0) (N : ℕ) :
    memoRoot (coefficientRow N) h = rootCoeffValue h N := by
  have hk : (-h).toNat < 84 := by omega
  simp only [memoRoot,coefficientRow,List.getElem?_toArray,List.getElem?_map,
    List.getElem?_range hk,Option.map_some,Option.getD_some]
  congr 1
  omega

private theorem evaluate_memo {p : Laurent} (h : (Span.interval (-83) 0).covers p) (N : ℕ) :
    evaluateWith (memoRoot (coefficientRow N)) p = coeff N (eval p) := by
  rw [← evaluateWith_eq]
  induction p with
  | nil => rfl
  | cons t p ih =>
    obtain ⟨k,c⟩ := t
    have ⟨hl,hr⟩ := (h _ List.mem_cons_self : -83 ≤ k ∧ k ≤ 0)
    rw [evaluateWith,evaluateWith,memoRoot_valid hl hr,ih (Span.of_tail h)]

def boundsCheck (p : Laurent) : Bool := p.all fun t => decide (-83 ≤ t.1 ∧ t.1 ≤ 0)

theorem boundsCheck_sound {p : Laurent} (h : boundsCheck p = true) : (Span.interval (-83) 0).covers p :=
  fun t ht => (show -83 ≤ t.1 ∧ t.1 ≤ 0 from of_decide_eq_true (List.all_eq_true.mp h t ht))

def rowCheck (C : Array Laurent) (n δ : ℕ) : Bool :=
  let f := memoRoot (coefficientRow (n+δ))
  let pts := rankCells n δ
  (List.range 21).all fun r => decide (evaluateWith f (lookup C r)*(momentDen r:ℚ) =
    ((δ:ℚ)+1)*(momentInt pts r:ℚ))

def boundsAll (C : Array Laurent) := (List.range 21).all fun r => boundsCheck (lookup C r)

theorem rowCheck_sound {C : Array Laurent} {n δ : ℕ} (hc : boundsAll C = true) (h : rowCheck C n δ = true)
    {r : ℕ} (hr : r ≤ 20) :
    coeff (n+δ) (eval (lookup C r)) = ((δ:ℚ)+1)*Witness.rawCell n δ r := by
  have hm : r ∈ List.range 21 := List.mem_range.mpr (by omega)
  have hb := boundsCheck_sound (List.all_eq_true.mp hc r hm)
  have he := of_decide_eq_true (List.all_eq_true.mp h r hm)
  change evaluateWith (memoRoot (coefficientRow (n+δ))) _*_ = _ at he
  rw [evaluate_memo hb,momentInt_eq] at he
  apply mul_right_cancel₀ (by unfold momentDen; positivity : (momentDen r:ℚ) ≠ 0)
  linear_combination he

theorem rows_certify {C : Array Laurent} {δ : ℕ} (hδ : δ ≤ 1) (hc : boundsAll C = true)
    (hs : ∀ n < 84, rowCheck C n δ = true) {r : ℕ} (hr : r ≤ 20) (n : ℕ) :
    coeff (n+δ) (eval (lookup C r)) = ((δ:ℚ)+1)*Witness.rawCell n δ r := by
  have hb := boundsCheck_sound (List.all_eq_true.mp hc r (List.mem_range.mpr (by omega)))
  simpa only [Nat.zero_add] using certify_cell_samples hδ hr (lookup C r) hb 0
    (fun i hi => by simpa only [Nat.zero_add] using rowCheck_sound hc (hs i hi) hr) n

end CentralUnimodality.Laurent
