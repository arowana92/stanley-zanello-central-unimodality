module

public import CentralUnimodality.TaylorSamples
public import CentralUnimodality.WitnessTables
import Mathlib.Tactic.Eval
meta import CentralUnimodality.TaylorSamples

/-! Cache all 168 packed Taylor values and 85 Catalan-root rows. Incremental
recurrences certify the quoted naturals and rationals once. Each moment
sample then uses only the relevant two rows. -/
@[expose] public section

namespace CentralUnimodality.Laurent

def taylorHistory : ℕ → List ℕ × List ℕ
  | 0 => ([1%sampleMod],[1%sampleMod])
  | m+1 =>
    let (layer, history) := taylorHistory m
    let nxt := nextMod (sampleBase+1) sampleMod (m+1) layer
    (nxt,(nxt.sum % sampleMod)::history)

private theorem taylorHistory_eq (m : ℕ) :
    (taylorHistory m).1 = modularLayers (sampleBase+1) sampleMod m ∧
    (taylorHistory m).2.reverse = (List.range (m+1)).map packedBinomials := by
  induction m with
  | zero => decide +kernel
  | succ m ih =>
    obtain ⟨row,hist⟩ := ih
    simp only [taylorHistory,modularLayers,List.reverse_cons,row,hist,List.range_succ (n := m+1),
      List.map_append,List.map_singleton,true_and]
    rfl

def allTaylor : Array ℕ := eval% (taylorHistory 167).2.reverse.toArray

set_option maxRecDepth 100000 in
private theorem checkTaylor : allTaylor = (taylorHistory 167).2.reverse.toArray := by decide +kernel

theorem allTaylor_get {m : ℕ} (hm : m < 168) : allTaylor[m]?.getD 0 = packedBinomials m := by
  rw [checkTaylor,(taylorHistory_eq 167).2]
  simp [List.getElem?_map,List.getElem?_range hm]

def nextRoots (N : ℕ) (xs : Array ℚ) : Array ℚ :=
  ((List.range 84).map fun (i : ℕ) =>
    (4*(N:ℚ)+2*i)*xs[i]?.getD 0/((N:ℚ)+1)).toArray

def rootHistory : ℕ → Array ℚ × List (Array ℚ)
  | 0 => (coefficientRow 0,[coefficientRow 0])
  | N+1 =>
    let (row,hist) := rootHistory N
    let nxt := nextRoots N row
    (nxt,nxt::hist)

set_option maxRecDepth 100000 in
def rootNumerals : Array (Array ℕ) :=
  eval% (((rootHistory 84).2.reverse.map fun row => row.map fun x => x.num.toNat).toArray)

def rootEntry (N i : ℕ) := ((rootNumerals[N]?.getD #[])[i]?).getD 0

private theorem rootBase : (List.range 84).all (fun i => decide (rootEntry 0 i = 1)) = true := by
  decide +kernel

private def stepOK (N : ℕ) := (List.range 84).all fun i =>
  decide ((N+1)*rootEntry (N+1) i = (4*N+2*i)*rootEntry N i)

set_option maxRecDepth 50000 in
private theorem rootSteps : (List.range 84).all stepOK = true := by decide +kernel

private theorem rootEntry_eq {N i : ℕ} (hN : N < 85) (hi : i < 84) :
    (rootEntry N i:ℚ) = rootCoeffValue (-(i:ℤ)) N := by
  induction N with
  | zero =>
    have h := of_decide_eq_true (List.all_eq_true.mp rootBase i (List.mem_range.mpr hi))
    simp [rootCoeffValue,h]
  | succ N ih =>
    have hs := List.all_eq_true.mp rootSteps N (List.mem_range.mpr (by omega))
    have he := of_decide_eq_true (List.all_eq_true.mp hs i (List.mem_range.mpr hi))
    have hq : ((N:ℚ)+1)*rootEntry (N+1) i = (4*(N:ℚ)+2*i)*rootEntry N i := by exact_mod_cast he
    rw [rootCoeffValue,← ih (by omega)]
    push_cast
    apply (eq_div_iff (by positivity)).mpr
    linear_combination hq

def cachedRoots (N : ℕ) : Array ℚ :=
  ((List.range 84).map fun (i : ℕ) => (rootEntry N i:ℚ)).toArray

theorem cachedRoots_eq {N : ℕ} (hN : N < 85) : cachedRoots N = coefficientRow N := by
  unfold cachedRoots coefficientRow
  congr 1
  apply List.map_congr_left
  exact fun i hi => rootEntry_eq hN (List.mem_range.mp hi)

def cachedRow (C : Array Laurent) (n δ : ℕ) : Bool :=
  let f := memoRoot (cachedRoots (n+δ))
  let w := allTaylor[2*n+δ]?.getD 0
  (List.range 21).all fun r => decide (evaluateWith f (lookup C r)*(momentDen r:ℚ) =
    ((δ:ℚ)+1)*(foldedCell w (cellTop n δ) r:ℚ))

theorem cachedRow_eq {n δ : ℕ} (hn : n < 84) (hδ : δ ≤ 1) (C : Array Laurent) :
    cachedRow C n δ = rowCheck C n δ := by
  rw [← foldedRow_eq hn hδ,cachedRow,foldedRow,cachedRoots_eq (by omega : n+δ < 85),
    allTaylor_get (by omega : 2*n+δ < 168)]

def cachedBlock (C : Array Laurent) (δ b : ℕ) :=
  (List.range 6).all fun i => cachedRow C (6*b+i) δ

theorem rows_from_cached {C : Array Laurent} {δ : ℕ} (hδ : δ ≤ 1)
    (h : ∀ b < 14, cachedBlock C δ b = true) (n : ℕ) (hn : n < 84) : rowCheck C n δ = true := by
  rw [← cachedRow_eq hn hδ]
  have he := List.all_eq_true.mp (h (n/6) (by omega)) (n%6) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  rwa [show 6*(n/6)+n%6 = n by omega] at he

end CentralUnimodality.Laurent
