module

public import CentralUnimodality.PackedComparisons

/-! Locate a candidate peak by its last strict rise. Two independent
packed comparisons verify the entire row on either side of that index. -/
@[expose] public section

namespace CentralUnimodality.PackedComparisons

def highestLane (b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k+1, v =>
    let step := 2^k
    let top := v >>> (b*step)
    if top=0 then highestLane b k v else step+highestLane b k top

def peakGuess (w d v : ℕ) : ℕ :=
  let G := guards w d
  let lower := segment w d v
  let upper := segment w d (v >>> (w+1))
  let rises := (G-(G >>> w)+upper-lower) &&& G
  if rises=0 then 0 else min d (highestLane (w+1) (d.log2+1) rises+1)

def checkPeak (w d v : ℕ) : Bool :=
  let p := peakGuess w d v
  ordered w p v (v >>> (w+1)) &&
    ordered w (d-p) (v >>> ((w+1)*(p+1))) (v >>> ((w+1)*p))

private theorem digit_shift (b v s i : ℕ) :
    digit b (v >>> (b*s)) i = digit b v (s+i) := by
  simp only [digit,Nat.shiftRight_add,Nat.mul_add]

theorem checkPeak_sound {w d v : ℕ} (hb : ∀ i, digit (w+1) v i < 2^w) (H : checkPeak w d v=true) :
    UnimodalOn (digit (w+1) v) 0 d := by
  let p := peakGuess w d v
  have hp : p≤d := by dsimp only [p,peakGuess]; split <;> omega
  simp only [checkPeak,Bool.and_eq_true] at H
  obtain ⟨hup,hdown⟩ := H
  have small (s i : ℕ) : digit (w+1) (v >>> ((w+1)*s)) i < 2^w := by rw [digit_shift]; exact hb _
  have U := ordered_sound (fun i _ => hb i) (fun i _ => by simpa only [Nat.mul_one] using small 1 i) hup
  have V := ordered_sound (fun i _ => small (p+1) i) (fun i _ => small p i) hdown
  refine ⟨p,Nat.zero_le _,hp,?_,?_⟩
  · intro i _ hi
    simpa only [digit_succ] using U i hi
  · intro i hpi hi
    have h := V (i-p) (by omega)
    rw [digit_shift,digit_shift,show p+1+(i-p)=i+1 by omega,show p+(i-p)=i by omega] at h
    exact h

theorem checkPeak_rank {w m d : ℕ} (hm : m<w) (hc : checkPeak w d (packedRow (w+1) m)=true) :
    UnimodalOn (rankCount m) 0 d := by
  have he : digit (w+1) (packedRow (w+1) m)=rankCount m := funext fun j => packedRow_digit _ _ _ (by omega)
  rw [← he]
  apply checkPeak_sound _ hc
  intro i; rw [he,rankCount_eq_card]
  exact (Finset.card_filter_le ..).trans_lt ((card_allPartitions_le m).trans_lt (Nat.pow_lt_pow_right (by decide) hm))

/-- Continue from a known ballot layer. A block computes each successor
layer once, sharing it between the peak test and the following step. -/
def checkLayers (w : ℕ) : ℕ → ℕ → List ℕ → Bool
  | 0, _, _ => true
  | count+1, m, layer =>
    checkPeak w (m*m/4) layer.sum && checkLayers w count (m+1) (nextLayer (w+1) (m+1) layer)

theorem checkLayers_sound {w count m : ℕ} (hm : m+count≤w)
    (H : checkLayers w count m (packedLayers (w+1) m)=true) :
    ∀ j<count, UnimodalOn (rankCount (m+j)) 0 ((m+j)*(m+j)/4) := by
  induction count generalizing m with
  | zero => omega
  | succ count IH =>
    simp only [checkLayers,Bool.and_eq_true] at H
    obtain ⟨h₀,h₁⟩ := H
    intro j hj
    cases j with
    | zero => simpa only [Nat.add_zero] using checkPeak_rank (by omega : m<w) h₀
    | succ j =>
      have hh := IH (m:=m+1) (by omega) h₁ j (by omega)
      simpa only [show m+1+j=m+(j+1) by omega] using hh

end CentralUnimodality.PackedComparisons
