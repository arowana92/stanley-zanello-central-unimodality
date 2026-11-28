module

public import CentralUnimodality.PackedDigitArithmetic

/-! Extract adjacent groups of digits by halving. This avoids forming
a separate full-length shifted integer for every comparison. -/
@[expose] public section

namespace CentralUnimodality.HeightBlock

def splitDigits (b : ℕ) : ℕ → ℕ → List ℕ
  | 0, v => [v%2^b]
  | k+1, v =>
    let cut := b*2^k
    splitDigits b k (v%2^cut) ++ splitDigits b k (v >>> cut)

private theorem split_length (b k v : ℕ) : (splitDigits b k v).length=2^k := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => simp only [splitDigits,List.length_append,ih,pow_succ]; omega

private theorem digit_clip {b i n : ℕ} (hi : i<n) (v : ℕ) :
    digit b (v%2^(b*n)) i=digit b v i := by
  have dv : 2^(b*i)*2^b ∣ 2^(b*n) := by
    rw [← Nat.pow_add,← Nat.mul_succ]
    exact pow_dvd_pow _ (Nat.mul_le_mul_left b hi)
  simp only [digit,Nat.shiftRight_eq_div_pow,← Nat.mod_mul_right_div_self,Nat.mod_mod_of_dvd _ dv]

private theorem split_get (b k v i : ℕ) (hi : i<(splitDigits b k v).length) :
    (splitDigits b k v)[i]=digit b v i := by
  induction k generalizing v i with
  | zero =>
    have hz : i=0 := by simpa [splitDigits] using hi
    subst i; simp [splitDigits,digit_zero]
  | succ k ih =>
    have hs := hi
    rw [split_length,pow_succ] at hs
    simp only [splitDigits]
    by_cases low : i<2^k
    · rw [List.getElem_append_left (by rw [split_length]; omega),ih,digit_clip low]
    · rw [List.getElem_append_right (by rw [split_length]; omega),ih,split_length,
        EndpointDeficit.digit_right,show 2^k+(i-2^k)=i by omega]

def compareLists : List ℕ → List ℕ → Bool
  | a::as, b::bs => decide (a≤b) && compareLists as bs
  | _, _ => true

private theorem comparison_at {a c : List ℕ} {i : ℕ} (ok : compareLists a c=true)
    (ha : i<a.length) (hc : i<c.length) : a[i]≤c[i] := by
  induction a generalizing c i with
  | nil => simp at ha
  | cons x xs ih =>
    cases c with
    | nil => simp at hc
    | cons y ys =>
      simp only [compareLists,Bool.and_eq_true,decide_eq_true_eq] at ok
      cases i with
      | zero => exact ok.1
      | succ i => exact ih ok.2 (by simpa using ha) (by simpa using hc)

def checkReflection (b e v : ℕ) : Bool :=
  let d := (splitDigits b (e.log2+1) v).take (e+1)
  let half := d.take (e/2+1)
  compareLists half half.tail && compareLists half d.reverse

theorem checkReflection_pairs {b e v : ℕ} (ok : checkReflection b e v=true) (i : ℕ) (hi : i≤e/2) :
    (i<e/2 → digit b v i≤digit b v (i+1)) ∧ digit b v i≤digit b v (e-i) := by
  let full := splitDigits b (e.log2+1) v
  let d := full.take (e+1)
  let half := d.take (e/2+1)
  have width : e<full.length := by
    dsimp only [full]
    rw [split_length]
    exact Nat.lt_log2_self
  have ld : d.length=e+1 := by simp [d,List.length_take,Nat.min_eq_left (by omega : e+1≤full.length)]
  have lh : half.length=e/2+1 := by simp [half,List.length_take,ld,Nat.min_eq_left (by omega : e/2+1≤e+1)]
  have hd (j : ℕ) (hj : j<d.length) : d[j]=digit b v j := by
    dsimp only [d]; rw [List.getElem_take]; apply split_get
  have hh (j : ℕ) (hj : j<half.length) : half[j]=digit b v j := by
    dsimp only [half]; rw [List.getElem_take]; apply hd
  change compareLists half half.tail && compareLists half d.reverse=true at ok
  simp only [Bool.and_eq_true] at ok
  obtain ⟨ha,hc⟩ := ok
  constructor
  · intro h
    have H := comparison_at (i:=i) ha (by omega) (by rw [List.length_tail,lh]; omega)
    rw [List.getElem_tail,hh,hh] at H
    exact H
  · have H := comparison_at (i:=i) hc (by omega) (by rw [List.length_reverse,ld]; omega)
    rw [List.getElem_reverse,hh,hd] at H
    simpa only [ld,show e+1-1-i=e-i by omega] using H

end CentralUnimodality.HeightBlock
