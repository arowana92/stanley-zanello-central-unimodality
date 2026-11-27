module

public import CentralUnimodality.NewtonCells
public import CentralUnimodality.SampleBlocks

/-! A bounded-integer sample verifier for the degree-twenty certificate.
At every required size the binomial moments through order 21 fit in 448 bits. -/
@[expose] public section

namespace CentralUnimodality.Laurent

def sampleBase : ℕ := 2^448
def sampleMod : ℕ := sampleBase^22

def packedBinomials (m : ℕ) := modularWeight (sampleBase+1) sampleMod m

private theorem rank_bound {n δ : ℕ} (hn : n < 84) (hδ : δ ≤ 1) :
    ∀ l ∈ allPartitions (2*n+δ), l.sum ≤ 8192 := by
  intro l hl
  have hd := sum_le_staircase_area hδ ((fits_iff_inside_reverse n δ hδ l).mp (mem_allPartitions.mp hl))
  have h := Nat.mul_le_mul (by omega : n ≤ 83) (by omega : n+δ ≤ 84)
  simpa only [List.sum_reverse] using hd.trans (h.trans (by decide : 83*84 ≤ 8192))

private theorem binomial_fits {m k : ℕ} (hm : m ≤ 167) (hk : k ≤ 21)
    (hd : ∀ l ∈ allPartitions m, l.sum ≤ 8192) : binomialMoment m k < sampleBase := by
  calc
    binomialMoment m k ≤ ∑ _l ∈ allPartitions m, 8192^21 := by
      apply Finset.sum_le_sum
      intro l hl
      exact (Nat.choose_le_pow ..).trans ((Nat.pow_le_pow_left (hd l hl) k).trans
        (Nat.pow_le_pow_right (by decide) hk))
    _ = (allPartitions m).card*8192^21 := by simp
    _ ≤ 2^167*8192^21 := Nat.mul_le_mul_right _ ((card_allPartitions_le m).trans (Nat.pow_le_pow_right (by decide) hm))
    _ < sampleBase := by decide +kernel

set_option exponentiation.threshold 512 in
theorem packedBinomials_digit {n δ k : ℕ} (hn : n < 84) (hδ : δ ≤ 1) (hk : k ≤ 21) :
    (packedBinomials (2*n+δ) / sampleBase^k) % sampleBase = binomialMoment (2*n+δ) k := by
  have hd := rank_bound hn hδ
  rw [packedBinomials,modularWeight_eq,sampleMod,digit_mod_weight (by omega : k < 22),
    taylor_weight sampleBase hd]
  apply taylor_digit (Nat.pow_pos (by decide : 0 < 2)) (by omega)
  exact fun i hi => binomial_fits (by omega) (hi.trans hk) hd

def sumList {R : Type*} [AddMonoid R] (m : ℕ) (f : ℕ → R) := ((List.range m).map f).sum

private theorem sumList_eq {R : Type*} [AddCommMonoid R] (m : ℕ) (f : ℕ → R) :
    sumList m f = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => simp [sumList]
  | succ m ih => simpa [sumList,List.range_succ,Finset.sum_range_succ] using congrArg (·+f m) ih

def fastDiff (f : ℕ → ℤ) (k : ℕ) := sumList (k+1) fun i =>
  (-1:ℤ)^(k-i)*(Nat.fast_choose k i)*f i

private theorem fastDiff_eq (f : ℕ → ℤ) (k : ℕ) : fastDiff f k = diffAtZero f k := by
  simp only [fastDiff,sumList_eq,diffAtZero,Nat.choose_eq_fast_choose]

def foldedCell (w top r : ℕ) : ℤ :=
  sumList (r+2) fun k => ((w / sampleBase^k % sampleBase:ℕ):ℤ)*fastDiff (endpointValue top r) k

theorem foldedCell_eq {n δ r : ℕ} (hn : n < 84) (hδ : δ ≤ 1) (hr : r ≤ 20) :
    foldedCell (packedBinomials (2*n+δ)) (cellTop n δ) r = (momentInt (rankCells n δ) r:ℤ) := by
  rw [binomial_cell n δ r hδ,foldedCell,sumList_eq]
  apply Finset.sum_congr rfl
  intro k hk
  rw [packedBinomials_digit hn hδ (by have := Finset.mem_range.mp hk; omega),fastDiff_eq]

def foldedRow (C : Array Laurent) (n δ w : ℕ) : Bool :=
  let f := memoRoot (coefficientRow (n+δ))
  (List.range 21).all fun r => decide (evaluateWith f (lookup C r)*(momentDen r:ℚ) =
    ((δ:ℚ)+1)*(foldedCell w (cellTop n δ) r:ℚ))

theorem foldedRow_eq {n δ : ℕ} (hn : n < 84) (hδ : δ ≤ 1) (C : Array Laurent) :
    foldedRow C n δ (packedBinomials (2*n+δ)) = rowCheck C n δ := by
  apply Bool.eq_iff_iff.mpr
  simp only [foldedRow,rowCheck,List.all_eq_true]
  constructor <;> intro h r hr
  all_goals
    have hh := foldedCell_eq hn hδ (by have := List.mem_range.mp hr; omega : r ≤ 20)
    simpa only [hh,Int.cast_natCast] using h r hr

end CentralUnimodality.Laurent
