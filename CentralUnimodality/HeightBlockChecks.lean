module

public import CentralUnimodality.PackedHeightBlock
public import CentralUnimodality.ReflectedDigitLists

/-! Compare each digit through the middle with its successor and
its reflected digit. Together these checks cover all index pairs. -/
@[expose] public section

namespace CentralUnimodality.HeightBlock

theorem checkReflection_sound {b e v : ℕ} (ok : checkReflection b e v=true)
    {i j : ℕ} (hij : i<j) (hcut : i+j≤e) : digit b v i≤digit b v j := by
  have tests := checkReflection_pairs ok
  have rising (s t : ℕ) (hst : s≤t) (ht : t≤e/2) : digit b v s≤digit b v t := by
    induction t with
    | zero => simp [show s=0 by omega]
    | succ t ih =>
      by_cases he : s=t+1
      · simp [he]
      · exact (ih (by omega) (by omega)).trans ((tests t (by omega)).1 (by omega))
  by_cases h : j≤e/2
  · exact rising i j hij.le h
  · have H := (tests (e-j) (by omega)).2
    rw [show e-(e-j)=j by omega] at H
    exact (rising i (e-j) (by omega) (by omega)).trans H

private theorem prefix_floor (h s : ℕ) (w : List Bool) (hs : s≤w.length) :
    s*((h-s)/2)≤cost h w := by
  induction s generalizing h w with
  | zero => simp
  | succ s ih =>
    cases w with
    | nil => simp at hs
    | cons b w =>
      have hb : h-1≤nextHeight h b := by cases b <;> simp [nextHeight]; omega
      have H := ih (nextHeight h b) w (by simpa using hs)
      rw [cost,Nat.succ_mul]
      have ht : (h-(s+1))/2≤(nextHeight h b-s)/2 := by omega
      have := Nat.mul_le_mul_left s ht
      omega

private theorem suffix_floor (h s : ℕ) (w : List Bool) (hs : s≤w.length) :
    s*((finish h w-s)/2)≤cost h w := by
  induction w generalizing h s with
  | nil => simp at hs; simp [hs]
  | cons b w ih =>
    rw [finish,cost]
    by_cases short : s≤w.length
    · exact (ih (nextHeight h b) s short).trans (Nat.le_add_left ..)
    · have eq : s=w.length+1 := by simp only [List.length_cons] at hs; omega
      rw [eq,Nat.succ_mul]
      have H := ih (nextHeight h b) w.length (by omega)
      have hb := finish_le (nextHeight h b) w
      have ht : (finish (nextHeight h b) w-(w.length+1))/2≤(finish (nextHeight h b) w-w.length)/2 := by omega
      have := Nat.mul_le_mul_left w.length ht
      omega

def checkBlockColumns (m H e first num : ℕ) : Bool :=
  let b := m+1
  let size := H+m
  let modulus := 2^(b*(e+1))
  (List.range num).all fun i =>
    let row := column b modulus (first+i) size m
    (List.range H).all fun h => checkReflection b e (entry row h)

theorem checkBlock_sound {m H e p : ℕ} (hp : p≤m) (high : e≤2*(p*((H-p)/2)))
    (tested : ∀ t<H, ∃ a k, a≤t ∧ t<a+k ∧ checkBlockColumns m H e a k=true)
    (h t : ℕ) : ReflectedCoeffs (kernel m h t) e := by
  by_cases bounds : h<H ∧ t<H
  · obtain ⟨a,k,ha,hk,ok⟩ := tested t bounds.2
    simp only [checkBlockColumns,List.all_eq_true,List.mem_range] at ok
    have test := ok (t-a) (by omega) h bounds.1
    rw [show a+(t-a)=t by omega] at test
    intro i j hij hsum
    have hb := checkReflection_sound test hij (by omega)
    rwa [column_digit (by omega) (by omega) (by omega),
      column_digit (by omega) (by omega) (by omega)] at hb
  · intro i j hij hsum
    suffices (kernel m h t).coeff i=0 by omega
    rw [kernel,transfer_sum,Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro w hw
    have hl := mem_words.mp hw
    by_cases a : BallotFrom h w
    · by_cases b : finish h w=t
      · have hi : i≠cost h w := by
          by_cases hh : H≤h
          · have hb := prefix_floor h p w (by omega)
            have hc := Nat.mul_le_mul_left p (show (H-p)/2≤(h-p)/2 by omega)
            omega
          · have hb := suffix_floor h p w (by omega)
            rw [b] at hb
            have hc := Nat.mul_le_mul_left p (show (H-p)/2≤(t-p)/2 by omega)
            omega
        simp [a,b,Polynomial.coeff_X_pow,hi]
      · simp [a,b]
    · simp [a]

end CentralUnimodality.HeightBlock
