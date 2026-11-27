module

public import CentralUnimodality.KilledRenewal

/-! An exact mass balance for a walk started above the boundary. At every
step a surviving path either survives again or hits zero for the first time. -/
@[expose] public section

namespace CentralUnimodality

def survivors (a n : ℕ) := (words n).filter (PositiveVertices a)

private theorem filter_count {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card = ∑ x ∈ s, if p x then 1 else 0 := by
  rw [← Finset.sum_filter]
  simp

private theorem snoc_count (a : ℕ) (w : List Bool) (b : Bool) :
    (if PositiveVertices a (w++[b]) then 1 else 0) + (if FirstHitPath a (w++[b]) then 1 else 0) =
      if PositiveVertices a w then (1:ℕ) else 0 := by
  have hv : vertices a (w++[b]) = vertices a w ++ [(a:ℤ)+displacement w+step b] := by
    simp [vertices,heights_append,heights]
  have hs : PositiveVertices a (w++[b]) ↔ PositiveVertices a w ∧ 0 < (a:ℤ)+displacement w+step b := by
    simp only [PositiveVertices,hv,List.forall_mem_append,List.forall_mem_singleton]
  have hh : FirstHitPath a (w++[b]) ↔ PositiveVertices a w ∧ (a:ℤ)+displacement w+step b = 0 := by
    simp [FirstHitPath,displacement_snoc,add_assoc,and_comm]
  by_cases hp : PositiveVertices a w
  · have ht := hp _ (endpoint_mem_vertices _ w)
    have he : 0 ≤ (a:ℤ)+displacement w+step b := by cases b <;> dsimp [step] <;> omega
    by_cases hx : 0 < (a:ℤ)+displacement w+step b
    · simp [hs,hh,hp,hx,hx.ne']
    · simp [hs,hh,hp,show (a:ℤ)+displacement w+step b = 0 by omega]
  · simp [hs,hh,hp]

theorem survivor_hit_step (a n : ℕ) :
    (survivors a (n+1)).card+(hitWords a (n+1)).card = 2*(survivors a n).card := by
  simp only [survivors,hitWords,filter_count,← Finset.sum_add_distrib]
  rw [sum_snoc_words]
  simp only [snoc_count,two_mul]

theorem survivor_hit_total {a : ℕ} (ha : 0 < a) (n : ℕ) :
    (survivors a n).card + ∑ t ∈ Finset.range (n+1), (hitWords a t).card*2^(n-t) = 2^n := by
  induction n with
  | zero =>
    have he : hitWords a 0 = ∅ := by ext w; simp +contextual [hitWords,words,FirstHitPath]
    have hp : PositiveVertices (a:ℤ) [] := by simp [PositiveVertices,vertices,heights,ha]
    have hs : survivors a 0 = {[]} := by
      ext w
      simp +contextual [survivors,words,hp]
    simp [he,hs]
  | succ n ih =>
    rw [Finset.sum_range_succ,Nat.sub_self,pow_zero,mul_one,pow_succ,← ih,add_mul,Finset.sum_mul]
    have h : ∀ t ∈ Finset.range (n+1), (hitWords a t).card*2^(n+1-t) = (hitWords a t).card*2^(n-t)*2 := by
      intro t ht
      have := Finset.mem_range.mp ht
      rw [show n+1-t = (n-t)+1 by omega,pow_succ,mul_assoc]
    rw [Finset.sum_congr rfl h]
    have := survivor_hit_step a n
    omega

theorem killed_norm_le_survivors (ω : ℝ) (a n : ℕ) (s : Finset ℤ) :
    ∑ z ∈ s, ‖killedAt ω a n z‖ ≤ (survivors a n).card := by
  have per (z : ℤ) : ‖killedAt ω a n z‖ ≤
      ∑ w ∈ words n, if PositiveVertices a w ∧ (a:ℤ)+displacement w=z then (1:ℝ) else 0 := by
    apply (norm_sum_le ..).trans
    apply Finset.sum_le_sum
    intro w _
    by_cases hw : PositiveVertices a w ∧ (a:ℤ)+displacement w=z <;> simp [hw,norm_areaCharacter]
  refine (Finset.sum_le_sum (fun z _ => per z)).trans ?_
  rw [Finset.sum_comm,survivors,filter_count,Nat.cast_sum]
  apply Finset.sum_le_sum
  intro w _
  by_cases hp : PositiveVertices a w
  · simp [hp,eq_comm (a := (a:ℤ)+displacement w)]
    split <;> norm_num
  · simp [hp]

end CentralUnimodality
