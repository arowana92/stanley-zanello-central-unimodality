module

public import CentralUnimodality.PairedDyckColumn

/-! A checked chunk certifies its final literal state and all intervening
Dyck comparisons. Chunks compose without retaining the reduction of
the entire transfer in one kernel conversion. -/
@[expose] public section

namespace CentralUnimodality.HeightBlock

def checkTo (b e H : ℕ) (target : List ℕ) : ℕ → ℕ → List ℕ → Bool
  | 0, _, row => row==target
  | k+1, n, row => (decide (dyckCut n≤e) && checkReflection b (dyckCut n) (entry row 0)) &&
      checkTo b e H target k (n+1) (pairedNext b (2^(b*(e+1))) H row)

private theorem checkTo_result {b e H n k : ℕ} {target : List ℕ}
    (ok : checkTo b e H target k n (pairedRows b (2^(b*(e+1))) H n)=true) :
    pairedRows b (2^(b*(e+1))) H (n+k)=target ∧
      checkPairedDycks b e H k n (pairedRows b (2^(b*(e+1))) H n)=true := by
  induction k generalizing n with
  | zero => simpa [checkTo,checkPairedDycks] using ok
  | succ k ih =>
    simp only [checkTo,Bool.and_eq_true] at ok
    obtain ⟨eq,tests⟩ := ih (n:=n+1) ok.2
    rw [show n+(k+1)=n+1+k by omega]
    rw [pairedRows] at tests
    exact ⟨eq,by simpa only [checkPairedDycks,Bool.and_eq_true] using And.intro ok.1 tests⟩

structure CheckedDycks (b e H n : ℕ) (r : List ℕ) : Prop where
  state : pairedRows b (2^(b*(e+1))) H n=r
  tested : ∀ l<n, ReflectedCoeffs (dyckPoly l) (⌈dyckLower l⌉₊:ℕ)

theorem CheckedDycks.start (b e H : ℕ) : CheckedDycks b e H 0 [1] :=
  ⟨rfl,by omega⟩

theorem CheckedDycks.extend {b e H n k : ℕ} {r target : List ℕ} (start : CheckedDycks b e H n r)
    (height : e+1≤H*(H-1)) (bits : 2*(n+k-1)<b) (ok : checkTo b e H target k n r=true) :
    CheckedDycks b e H (n+k) target := by
  rw [← start.state] at ok
  obtain ⟨eq,tests⟩ := checkTo_result ok
  refine ⟨eq,?_⟩
  intro l hl
  by_cases prev : l<n
  · exact start.tested l prev
  · exact checkPairedDycks_sound height bits tests (by omega) hl

end CentralUnimodality.HeightBlock
