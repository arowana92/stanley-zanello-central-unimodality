module

public import CentralUnimodality.PackedRoundedRanks
public import CentralUnimodality.PackedComparisons

/-! Compare a whole interval of rounded coefficients at once, reserving the
proved integer error at every adjacent pair. -/
@[expose] public section

namespace CentralUnimodality.EndpointDeficit
open PackedComparisons

def orderedGap (w len gap x y : ℕ) : Bool :=
  ordered w len (x+repeatDigit (w+1) len gap) y

theorem orderedGap_sound {w len gap x y u : ℕ}
    (hu : u+gap<2^w) (hx : ∀ i<len, digit (w+1) x i≤u)
    (hy : ∀ i<len, digit (w+1) y i≤u) (hc : orderedGap w len gap x y=true) :
    ∀ i<len, digit (w+1) x i + gap ≤ digit (w+1) y i := by
  have hg : gap<2^(w+1) := by rw [pow_succ]; omega
  have added (i : ℕ) (hi : i<len) :
      digit (w+1) (x+repeatDigit (w+1) len gap) i = digit (w+1) x i + gap := by
    rw [digit_add,digit_repeat (by omega) hg,ite_eq_left hi]
    intro j hj
    have h := hx j (by omega)
    rw [digit_repeat (by omega) hg,ite_eq_left (by omega : j<len),pow_succ]
    omega
  intro i hi
  rw [← added i hi]
  apply ordered_sound _ _ hc i hi
  · intro j hj; rw [added j hj]; have := hx j hj; omega
  · intro j hj; have := hy j hj; omega

def rankReserve (m : ℕ) := ((m/2+1)*m)/2+1

/-- Check the two strict slopes on the proposed interval of actual coranks. -/
def checkCorankPeak (w m lo peak hi v : ℕ) : Bool :=
  let gap := rankReserve m
  let atCorank := fun k => v >>> ((w+1)*k)
  orderedGap w (peak-lo) gap (atCorank lo) (atCorank (lo+1)) &&
    orderedGap w (hi-peak) gap (atCorank (peak+1)) (atCorank peak)

theorem checkCorankPeak_sound {w n m u lo p hi : ℕ}
    (hu : u+rankReserve m<2^w) (hl : lo≤p) (hp : p≤hi) (hn : hi<n) (hD : hi≤m*m/4)
    (hc : checkCorankPeak w m lo p hi (combine w n m (m*m/4) (roundedLayers w n u m))=true) :
    UnimodalOn (fun k => rankCount m (m*m/4-k)) lo hi := by
  let D := m*m/4
  let v := combine w n m D (roundedLayers w n u m)
  let gap := rankReserve m
  have digitAt (k i : ℕ) (h : k+i≤hi) :
      digit (w+1) (v >>> ((w+1)*k)) i = roundedRank u m (D-(k+i)) := by
    rw [digit_right]; exact combine_digit (by omega) (by omega) (by omega)
  have small (k len : ℕ) (h : ∀ i<len, k+i≤hi) (i : ℕ) (hi' : i<len) :
      digit (w+1) (v >>> ((w+1)*k)) i≤u :=
    (digitAt k i (h i hi')).trans_le (roundedRank_le ..)
  have transfer (a b : ℕ) (h : roundedRank u m a + gap ≤ roundedRank u m b) :
      rankCount m a ≤ rankCount m b := by
    apply (rank_lt_of_separated (unit:=u) ?_).le
    dsimp only [gap,rankReserve] at h
    omega
  rw [checkCorankPeak,Bool.and_eq_true] at hc
  obtain ⟨h₁,h₂⟩ := hc
  refine ⟨p,hl,hp,?_,?_⟩
  · intro k hk hkp
    have H := orderedGap_sound hu (small lo (p-lo) (by omega))
      (small (lo+1) (p-lo) (by omega)) h₁ (k-lo) (by omega)
    rw [digitAt _ _ (by omega),digitAt _ _ (by omega)] at H
    exact transfer _ _ (by simpa only [show lo+(k-lo)=k by omega,
      show lo+1+(k-lo)=k+1 by omega] using H)
  · intro k hk hkh
    have H := orderedGap_sound hu (small (p+1) (hi-p) (by omega))
      (small p (hi-p) (by omega)) h₂ (k-p) (by omega)
    rw [digitAt _ _ (by omega),digitAt _ _ (by omega)] at H
    exact transfer _ _ (by simpa only [show p+(k-p)=k by omega,
      show p+1+(k-p)=k+1 by omega] using H)

end CentralUnimodality.EndpointDeficit
