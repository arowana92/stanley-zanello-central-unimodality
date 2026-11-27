module

public import CentralUnimodality.FourierInputs

/-! Cutting an unrestricted walk at its two ends gives two recurrences for
its area transform at a fixed endpoint. The final area increment is exactly
the endpoint itself. -/
@[expose] public section

namespace CentralUnimodality

theorem sum_cons_words {R : Type*} [AddCommMonoid R] (f : List Bool → R) (n : ℕ) :
    (∑ w ∈ words (n+1), f w) =
      (∑ w ∈ words n, f (false::w)) + ∑ w ∈ words n, f (true::w) := by
  have dis : Disjoint ((words n).image (false :: ·)) ((words n).image (true :: ·)) := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp h₁
    obtain ⟨v, _, h⟩ := Finset.mem_image.mp h₂
    exact Bool.noConfusion (List.cons.inj h).1
  have inj (b : Bool) : Function.Injective (b :: · : List Bool → List Bool) := fun _ _ h => (List.cons.inj h).2
  rw [words,Finset.sum_union dis,Finset.sum_image (inj false).injOn,Finset.sum_image (inj true).injOn]

private theorem reverse_sum_words {R : Type*} [AddCommMonoid R] (f : List Bool → R) (n : ℕ) :
    (∑ w ∈ words n, f w.reverse) = ∑ w ∈ words n, f w := by
  apply Finset.sum_bij' (fun w _ => w.reverse) (fun w _ => w.reverse)
  all_goals simp [mem_words]

theorem sum_snoc_words {R : Type*} [AddCommMonoid R] (f : List Bool → R) (n : ℕ) :
    (∑ w ∈ words (n+1), f w) =
      (∑ w ∈ words n, f (w++[false])) + ∑ w ∈ words n, f (w++[true]) := by
  rw [← reverse_sum_words f (n+1),sum_cons_words]
  simp only [List.reverse_cons]
  exact congrArg₂ (·+·) (reverse_sum_words (fun w => f (w++[false])) n)
    (reverse_sum_words (fun w => f (w++[true])) n)

noncomputable def endpointTransform (ω : ℝ) (n : ℕ) (z : ℤ) : ℂ :=
  ∑ w ∈ words n, if displacement w = z then areaCharacter ω (walkArea w) else 0

theorem endpoint_prepend (ω : ℝ) (n : ℕ) (z : ℤ) :
    endpointTransform ω (n+1) z =
      areaCharacter ω (n+1) * endpointTransform ω n (z-1) +
      areaCharacter ω (-(n+1:ℤ)) * endpointTransform ω n (z+1) := by
  rw [endpointTransform,sum_cons_words]
  simp only [endpointTransform,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro w hw
  · have hd : displacement (false::w) = z ↔ displacement w = z-1 := by
      change 1+displacement w = z ↔ _
      omega
    by_cases h : displacement w = z-1 <;> simp [hd,h,walkArea_cons,step,mem_words.mp hw,areaCharacter_add,mul_comm]
  · have hd : displacement (true::w) = z ↔ displacement w = z+1 := by
      change -1+displacement w = z ↔ _
      omega
    by_cases h : displacement w = z+1 <;> simp [hd,h,walkArea_cons,step,mem_words.mp hw,areaCharacter_add,mul_comm]

theorem endpoint_append (ω : ℝ) (n : ℕ) (z : ℤ) :
    endpointTransform ω (n+1) z = areaCharacter ω z *
      (endpointTransform ω n (z-1) + endpointTransform ω n (z+1)) := by
  rw [endpointTransform,sum_snoc_words,mul_add]
  simp only [endpointTransform,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro w _
  all_goals
    simp only [displacement_snoc,step,walkArea_append,List.length_singleton,Nat.cast_one,mul_one]
    have hf : walkArea [false] = 1 := rfl
    have ht : walkArea [true] = -1 := rfl
    simp only [hf,ht]
    split <;> split
    all_goals first
      | omega
      | rename_i ha hb; rw [show walkArea w + _ + displacement w = z + walkArea w by omega,areaCharacter_add]
      | exact (mul_zero _).symm

theorem fair_bridge_endpoint (ω : ℝ) (n : ℕ) :
    PowerSeries.coeff n (fairSeries (areaCharacter ω) bridges) =
      (2:ℂ)⁻¹^n * endpointTransform ω n 0 := by
  simp only [coeff_walkSeries,bridges,Finset.sum_filter,endpointTransform]

end CentralUnimodality
