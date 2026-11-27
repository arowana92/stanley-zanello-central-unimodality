module

public import CentralUnimodality.PairedFourier
public import CentralUnimodality.FirstHitCount

/-! The unrestricted and positive walk kernels in absolute coordinates.
The endpoint-zero loss on each step is precisely the first-hit transform. -/
@[expose] public section

namespace CentralUnimodality

instance (a : ℤ) (w : List Bool) : Decidable (PositiveVertices a w) :=
  inferInstanceAs (Decidable (∀ x ∈ vertices a w, 0 < x))

noncomputable def freeAt (ω : ℝ) (a : ℤ) (n : ℕ) (z : ℤ) : ℂ :=
  areaCharacter ω (a*n) * endpointTransform ω n (z-a)

noncomputable def killedAt (ω : ℝ) (a : ℤ) (n : ℕ) (z : ℤ) : ℂ :=
  ∑ w ∈ words n, if PositiveVertices a w ∧ a+displacement w = z
    then areaCharacter ω ((heights a w).sum) else 0

noncomputable def hitAt (ω : ℝ) (a n : ℕ) : ℂ :=
  ∑ w ∈ hitWords a n, areaCharacter ω ((heights (a:ℤ) w).sum)

theorem freeAt_zero (ω : ℝ) (a z : ℤ) : freeAt ω a 0 z = if z=a then 1 else 0 := by
  simp [freeAt,endpointTransform,words,displacement,walkArea,heights,areaCharacter_zero,eq_comm (a := (0:ℤ)),sub_eq_zero]

theorem freeAt_step (ω : ℝ) (a : ℤ) (n : ℕ) (z : ℤ) : freeAt ω a (n+1) z =
    areaCharacter ω z*(freeAt ω a n (z-1)+freeAt ω a n (z+1)) := by
  rw [freeAt,endpoint_append,freeAt,freeAt,
    show z-a-1 = z-1-a by omega,show z-a+1 = z+1-a by omega,← mul_add]
  simp only [← mul_assoc,← areaCharacter_add]
  push_cast
  ring_nf

theorem killedAt_zero (ω : ℝ) {a : ℤ} (ha : 0 < a) (z : ℤ) : killedAt ω a 0 z = if z=a then 1 else 0 := by
  simp [killedAt,words,PositiveVertices,vertices,heights,displacement,ha,areaCharacter_zero,eq_comm]

private theorem pos_snoc (a : ℤ) (w : List Bool) (b : Bool) :
    PositiveVertices a (w++[b]) ↔ PositiveVertices a w ∧ 0 < a+displacement w+step b := by
  have he : vertices a (w++[b]) = vertices a w ++ [a+displacement w+step b] := by
    simp [vertices,heights_append,heights]
  simp only [PositiveVertices,he,List.forall_mem_append,List.forall_mem_singleton]

theorem killedAt_nonpos (ω : ℝ) (a : ℤ) (n : ℕ) {z : ℤ} (hz : z ≤ 0) : killedAt ω a n z = 0 := by
  apply Finset.sum_eq_zero
  intro w _
  rw [ite_eq_right]
  rintro ⟨hw,rfl⟩
  exact hz.not_gt (hw _ (endpoint_mem_vertices a w))

private theorem killLast (ω : ℝ) (a z : ℤ) (w : List Bool) (b : Bool) (hz : 0 < z) :
    (if PositiveVertices a (w++[b]) ∧ a+displacement (w++[b]) = z
      then areaCharacter ω ((heights a (w++[b])).sum) else 0) =
      areaCharacter ω z*(if PositiveVertices a w ∧ a+displacement w = z-step b
      then areaCharacter ω ((heights a w).sum) else 0) := by
  have hiff : PositiveVertices a (w++[b]) ∧ a+displacement (w++[b]) = z ↔
      PositiveVertices a w ∧ a+displacement w = z-step b := by
    rw [pos_snoc,displacement_snoc]
    constructor
    · rintro ⟨⟨hp,_⟩,h⟩
      exact ⟨hp,by omega⟩
    · rintro ⟨hp,h⟩
      exact ⟨⟨hp,by omega⟩,by omega⟩
  by_cases hw : PositiveVertices a w ∧ a+displacement w = z-step b
  · rw [ite_eq_left (hiff.mpr hw),ite_eq_left hw,heights_append,List.sum_append,areaCharacter_add,mul_comm]
    simp [heights,show a+displacement w+step b = z by have := hw.2; omega]
  · rw [ite_eq_right (fun h => hw (hiff.mp h)),ite_eq_right hw,mul_zero]

theorem killedAt_step (ω : ℝ) (a : ℤ) (n : ℕ) {z : ℤ} (hz : 0 < z) : killedAt ω a (n+1) z =
    areaCharacter ω z*(killedAt ω a n (z-1)+killedAt ω a n (z+1)) := by
  rw [killedAt,sum_snoc_words]
  simp_rw [killLast ω a z _ _ hz]
  simp only [step,sub_neg_eq_add,killedAt,Finset.mul_sum,mul_add]
  congr 1

theorem hitAt_zero (ω : ℝ) (a : ℕ) : hitAt ω a 0 = 0 := by
  have he : hitWords a 0 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hm := mem_words.mp (Finset.mem_filter.mp hw).1
    exact (Finset.mem_filter.mp hw).2.1 (List.length_eq_zero_iff.mp hm)
  simp [hitAt,he]

theorem hitAt_succ (ω : ℝ) (a n : ℕ) : hitAt ω a (n+1) = killedAt ω (a:ℤ) n 1 := by
  rw [hitAt,hitWords,Finset.sum_filter,sum_snoc_words,killedAt]
  have hu (w : List Bool) : ¬ FirstHitPath a (w++[false]) := by
    intro h
    have hp : PositiveVertices a w := by simpa using h.2.2
    have ht := hp _ (endpoint_mem_vertices _ w)
    have hd := h.2.1
    rw [displacement_snoc] at hd
    dsimp [step] at hd
    omega
  simp only [ite_eq_right (hu _),Finset.sum_const_zero,zero_add]
  apply Finset.sum_congr rfl
  intro w _
  have he : FirstHitPath a (w++[true]) ↔ PositiveVertices a w ∧ (a:ℤ)+displacement w = 1 := by
    simp [FirstHitPath,displacement_snoc,step,and_comm]
    omega
  by_cases h : PositiveVertices a w ∧ (a:ℤ)+displacement w = 1
  · rw [ite_eq_left (he.mpr h),ite_eq_left h]
    rw [heights_append,List.sum_append]
    simp [heights,step,h.2]
  · rw [ite_eq_right (fun h₁ => h (he.mp h₁)),ite_eq_right h]

end CentralUnimodality
