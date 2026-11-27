module

public import CentralUnimodality.MarkedExcursionTail
public import Mathlib.Analysis.Complex.Trigonometric

/-! Exponential tilting of the independent signs on a first-hit path.
The natural parameter starts at u and decreases by c per step. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion

open Real

noncomputable def signMass (c u : ℝ) : List Bool → ℝ
  | [] => 1
  | b::w => exp (u*step b)/(2*cosh u) * signMass c (u-c) w

noncomputable def coshProduct (c u : ℝ) (t : ℕ) : ℝ :=
  ∏ i ∈ Finset.range t, cosh (u-c*i)

private theorem product_succ (c u : ℝ) (t : ℕ) :
    coshProduct c u (t+1) = cosh u * coshProduct c (u-c) t := by
  rw [coshProduct,Finset.prod_range_succ',coshProduct,Nat.cast_zero,mul_zero,sub_zero,mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [Nat.cast_succ]; congr 1; ring

theorem signMass_total (c u : ℝ) (t : ℕ) : ∑ w ∈ words t, signMass c u w = 1 := by
  induction t generalizing u with
  | zero => simp [words,signMass]
  | succ t ih =>
    have dis : Disjoint ((words t).image (false :: ·)) ((words t).image (true :: ·)) := by
      apply Finset.disjoint_left.mpr
      intro w ha hb
      obtain ⟨_,_,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨_,_,h⟩ := Finset.mem_image.mp hb
      cases h
    have inj (b : Bool) : Function.Injective (b :: · : List Bool → List Bool) :=
      fun _ _ h => (List.cons.inj h).2
    rw [words,Finset.sum_union dis,Finset.sum_image (inj false).injOn,Finset.sum_image (inj true).injOn]
    simp only [signMass,step,Int.cast_one,Int.cast_neg,mul_one,mul_neg,← Finset.mul_sum,ih]
    rw [← add_div,cosh_eq]
    field_simp

theorem signMass_density (c u : ℝ) (w : List Bool) :
    signMass c u w * ((2:ℝ)^w.length * coshProduct c u w.length) =
      exp ((u-c*w.length)*displacement w+c*walkArea w) := by
  induction w generalizing u with
  | nil => simp [signMass,coshProduct,displacement,walkArea,heights]
  | cons b w ih =>
    rw [signMass,List.length_cons,product_succ,pow_succ,walkArea_cons]
    have ht : displacement (b::w) = step b + displacement w := rfl
    rw [ht]
    push_cast
    rw [show (u-c*(w.length+1))*(step b+displacement w)+c*(walkArea w+step b*(w.length+1)) =
        u*step b+(((u-c)-c*w.length)*displacement w+c*walkArea w) by ring,
      exp_add,← ih (u-c)]
    field_simp [(cosh_pos u).ne']

private def endHit (w : List Bool) := w++[true]

private theorem hits_as_excursions (d : ℕ) :
    hitWords 1 (2*d+1) = (dycks d).image endHit := by
  ext w
  rw [Finset.mem_image]
  induction w using List.reverseRecOn with
  | nil => simp [hitWords,mem_words,endHit]
  | append_singleton w b _ =>
    constructor
    · intro hw
      obtain ⟨hl,_,hz,hb⟩ := Finset.mem_filter.mp hw
      have hl' := mem_words.mp hl
      simp only [List.length_append,List.length_singleton] at hl'
      simp only [List.dropLast_append_of_ne_nil (by simp : [b] ≠ []),List.dropLast_singleton,List.append_nil] at hb
      have hball := (positive_one_iff w).mp hb
      have hn := ballot_endpoint_nonneg hball
      rw [displacement_snoc] at hz
      cases b with
      | false => dsimp [step] at hz; omega
      | true => exact ⟨w,mem_dycks.mpr ⟨⟨by omega,hball⟩,by dsimp [step] at hz; omega⟩,rfl⟩
    · rintro ⟨v,hv,he⟩
      have he' : v++[true] = w++[b] := he
      have hvw : v=w := by simpa using congrArg List.dropLast he'
      subst v
      obtain rfl : b=true := (List.cons.inj ((List.append_right_inj w).mp he')).1.symm
      obtain ⟨⟨hl,hb⟩,hz⟩ := mem_dycks.mp hv
      exact Finset.mem_filter.mpr ⟨mem_words.mpr (by simp [hl]),by
        simp [FirstHitPath,displacement_snoc,hz,step,(positive_one_iff w).mpr hb]⟩

theorem card_first_hits (d : ℕ) : (hitWords 1 (2*d+1)).card = (dycks d).card := by
  rw [hits_as_excursions,Finset.card_image_of_injective _ (show Function.Injective endHit from
    fun _ _ h => (List.append_left_inj [true]).mp h)]

/-- Removing the last down-step leaves an ordinary Dyck excursion. The
centered tilt on the first-hit event weights its area and a fixed shift. -/
theorem hit_mass_identity (c : ℝ) (d : ℕ) :
    (∑ w ∈ hitWords 1 (2*d+1), signMass c (c*d) w) *
        ((2:ℝ)^(2*d+1) * coshProduct c (c*d) (2*d+1)) =
      exp (c*d) * ∑ v ∈ dycks d, exp (c*walkArea v) := by
  rw [hits_as_excursions,Finset.sum_image (show Function.Injective endHit from
    fun _ _ h => (List.append_left_inj [true]).mp h).injOn,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  obtain ⟨⟨hl,_⟩,hz⟩ := mem_dycks.mp hv
  have h := signMass_density c (c*d) (endHit v)
  rw [show (endHit v).length = 2*d+1 by simp [endHit,hl]] at h
  have hd : displacement (endHit v) = -1 := by rw [endHit,displacement_snoc,hz]; rfl
  have ha : walkArea (endHit v) = walkArea v-1 := by
    rw [endHit,walkArea_append,hz,zero_mul,add_zero,show walkArea [true] = -1 by rfl]; omega
  rw [h,hd,ha,← exp_add]
  push_cast
  congr 1
  ring

end CentralUnimodality.MarkedExcursion
