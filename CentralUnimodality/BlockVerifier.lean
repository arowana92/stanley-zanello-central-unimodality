module

public import CentralUnimodality.ArcEnvelope

/-! Reduce an entire continuous outer frequency arc to a finite rational
table of free-block bounds and one check for each possible starting distance. -/
@[expose] public section

namespace CentralUnimodality

def hitNumber (a j : ℕ) : ℕ :=
  if a ≤ j ∧ (j-a)%2 = 0 then a*Nat.fast_choose j ((j-a)/2)/j else 0

theorem hitNumber_exact {a : ℕ} (ha : 0 < a) (j : ℕ) : hitNumber a j = (hitWords a j).card := by
  obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  cases j with
  | zero =>
    have h : hitWords (b+1) 0 = ∅ := by ext w; simp +contextual [hitWords,words,FirstHitPath]
    simp [h,hitNumber]
  | succ m =>
    rw [hitNumber]
    split
    next h =>
      let d := (m+1-(b+1))/2
      have he : m=b+2*d := by dsimp [d]; omega
      change (b+1)*Nat.fast_choose (m+1) d/(m+1) = _
      rw [← Nat.choose_eq_fast_choose,← first_hit_count b m d he,Nat.mul_div_right _ (by omega)]
    next h =>
      rw [first_hit_incompatible b m (by rintro ⟨d,he⟩; omega),Finset.card_empty]

def freeUnit (T : Array ℕ) (j : ℕ) : ℚ := (T[j]?.getD 0:ℕ)/4096

def hitProb (a j : ℕ) : ℚ := (hitNumber a j:ℚ)/2^j

def blockBound (T : Array ℕ) (a n : ℕ) : ℚ :=
  min (1-((List.range (n+1)).map (hitProb a)).sum)
    (freeUnit T n + ((List.range (n+1)).map fun j => hitProb a j * freeUnit T (n-j)).sum)

def envelopeOK (t : ℚ) (T : Array ℕ) (n : ℕ) : Bool :=
  (List.range (n+1)).all fun j => decide (envelopeUnits t j ≤ T[j]?.getD 0)

def blockOK (T : Array ℕ) (n : ℕ) (u : ℚ) : Bool :=
  (List.range (n+1)).all fun k => decide (blockBound T (k+1) n ≤ u)

private theorem sum_list_cast (f : ℕ → ℚ) (n : ℕ) :
    (((List.range n).map f).sum:ℝ) = ∑ j ∈ Finset.range n, (f j:ℝ) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,Finset.sum_range_succ,ih]

private theorem beyond_block {n a : ℕ} (ha : n < a) (T : Array ℕ) : blockBound T a n = blockBound T (n+1) n := by
  have hf (j : ℕ) (hj : j ∈ List.range (n+1)) : hitProb a j = hitProb (n+1) j := by
    have := List.mem_range.mp hj
    simp [hitProb,hitNumber,show ¬a≤j by omega,show ¬n+1≤j by omega]
  unfold blockBound
  rw [List.map_congr_left hf,List.map_congr_left (fun j hj => congrArg (·*freeUnit T (n-j)) (hf j hj))]

theorem blockOK_sound {t u : ℚ} {T : Array ℕ} {n : ℕ} (ht : 0 ≤ t)
    (he : envelopeOK t T n = true) (hb : blockOK T n u = true)
    {θ : ℝ} (hlo : (t:ℝ) ≤ θ) (hhi : θ ≤ Real.pi) {a : ℕ} (ha : 0 < a) (s : Finset ℤ) :
    (∑ z ∈ s, ‖killedAt (θ/2) a n z‖)/(2:ℝ)^n ≤ u := by
  have hρ (j : ℕ) (hj : j ≤ n) : pairFactor (θ/2) (j/2) ≤ (freeUnit T j:ℝ) := by
    have h := of_decide_eq_true (List.all_eq_true.mp he j (List.mem_range.mpr (by omega)))
    apply (envelope_bound ht hlo hhi j).trans
    unfold freeUnit
    push_cast
    exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num)
  have hkernel := killed_block_bound _ ha n s (fun j => (freeUnit T j:ℝ)) hρ
  have hz : (blockBound T a n:ℝ) = _ := (show (blockBound T a n:ℝ) =
      min (1-∑ j ∈ Finset.range (n+1), (hitWords a j).card/(2:ℝ)^j)
        ((freeUnit T n:ℝ)+∑ j ∈ Finset.range (n+1), (hitWords a j).card/(2:ℝ)^j*(freeUnit T (n-j):ℝ)) by
    simp only [blockBound,Rat.cast_min,Rat.cast_sub,Rat.cast_one,Rat.cast_add,sum_list_cast,Rat.cast_mul,
      hitProb,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat,hitNumber_exact ha])
  rw [← hz] at hkernel
  apply hkernel.trans
  suffices h : blockBound T a n ≤ u by exact_mod_cast h
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  by_cases hk : k ≤ n
  · exact of_decide_eq_true (List.all_eq_true.mp hb k (List.mem_range.mpr (by omega)))
  · rw [beyond_block (by omega : n < k+1)]
    exact of_decide_eq_true (List.all_eq_true.mp hb n (List.mem_range.mpr (by omega)))

end CentralUnimodality
