module

public import CentralUnimodality.MarkedExcursion
public import Mathlib.Analysis.Complex.Exponential

/-! Gaussian decay of the marked height and its use in a finite
exponential-moment bound for the area of an ordinary excursion. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion

/-- Exact probability with the path and its mark both uniform. -/
noncomputable def heightTail (d b : ℕ) : ℝ := (tail d b).card / ((marks d).card:ℝ)

theorem heightTail_eq {d b : ℕ} (hb : b ≤ d) :
    heightTail d b = ((2*d+1).choose (d-b):ℝ) / ((2*d+1).choose d:ℝ) := by
  rw [heightTail,card_tail hb,card_marks]

private theorem heightTail_succ {d b : ℕ} (hb : b < d) :
    heightTail d (b+1) = heightTail d b * (((d:ℝ)-b)/(d+b+2)) := by
  rw [heightTail_eq (by omega : b+1 ≤ d),heightTail_eq hb.le]
  have h := Nat.choose_succ_right_eq (2*d+1) (d-(b+1))
  rw [show d-(b+1)+1 = d-b by omega,show 2*d+1-(d-(b+1)) = d+b+2 by omega] at h
  have he : ((2*d+1).choose (d-b):ℝ) * (d-b:ℕ) = ((2*d+1).choose (d-(b+1)):ℝ)*(d+b+2) := by
    exact_mod_cast h
  rw [Nat.cast_sub hb.le] at he
  have hp : (0:ℝ) < (2*d+1).choose d := by exact_mod_cast Nat.choose_pos (by omega)
  field_simp
  linarith only [he]

private theorem gaussian_ratio {d b : ℕ} (hb : b < d) :
    ((d:ℝ)-b)/(d+b+2) ≤ Real.exp (-(2*((b:ℝ)+1)/(d+1))) := by
  have hbd : (b:ℝ) < d := by exact_mod_cast hb
  let x := 2*((b:ℝ)+1)/(d+1)
  have hx : x < 2 := by dsimp [x]; apply (div_lt_iff₀ (by positivity)).mpr; linarith
  have h := Real.exp_le_two_add_div_two_sub (x := x) (by dsimp [x]; positivity) hx
  have hr : (2+x)/(2-x) = ((d:ℝ)+b+2)/(d-b) := by
    dsimp [x]
    field_simp [(sub_pos.mpr hbd).ne']
    ring
  rw [hr] at h
  rw [Real.exp_neg,← one_div,(le_div_iff₀ (Real.exp_pos _)),div_mul_eq_mul_div,
    div_le_iff₀ (by positivity),one_mul,mul_comm]
  exact (le_div_iff₀ (sub_pos.mpr hbd)).mp h

theorem heightTail_gaussian (d b : ℕ) :
    heightTail d b ≤ Real.exp (-((b:ℝ)*(b+1)/(d+1))) := by
  induction b with
  | zero =>
    have hp : (0:ℝ) < (2*d+1).choose d := by exact_mod_cast Nat.choose_pos (by omega)
    simp [heightTail_eq (Nat.zero_le d),hp.ne']
  | succ b ih =>
    by_cases hb : b < d
    · have hp : 0 ≤ ((d:ℝ)-b)/(d+b+2) := div_nonneg (sub_nonneg.mpr (by exact_mod_cast hb.le)) (by positivity)
      rw [heightTail_succ hb]
      apply (mul_le_mul ih (gaussian_ratio hb) hp (Real.exp_pos _).le).trans
      rw [← Real.exp_add,Nat.cast_succ]
      apply Real.exp_le_exp.mpr
      apply le_of_eq
      ring
    · simp [heightTail,tail_empty (by omega : d < b+1),(Real.exp_pos _).le]

/-- Summation by parts against the exact binomial tail. -/
theorem sum_height (d : ℕ) (f : ℕ → ℝ) :
    (∑ p ∈ marks d, f (height p).toNat) = (marks d).card*f 0 +
      ∑ i ∈ Finset.range d, (tail d (i+1)).card*(f (i+1)-f i) := by
  have cut (h r : ℕ) : f (min h r) = f 0 +
      ∑ i ∈ Finset.range r, if i < h then f (i+1)-f i else 0 := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [Finset.sum_range_succ,← add_assoc,← ih]
      by_cases hr : r < h
      · simp [hr,Nat.min_eq_right hr.le]
      · simp [hr,Nat.min_eq_left (by omega : h ≤ r),Nat.min_eq_left (by omega : h ≤ r+1)]
  have term (p : List Bool × ℕ) (hp : p ∈ marks d) :
      f (height p).toNat = f 0 + ∑ i ∈ Finset.range d,
        if ((i+1:ℕ):ℤ) ≤ height p then f (i+1)-f i else 0 := by
    have hb := height_bounds hp
    have h := cut (height p).toNat d
    rw [Nat.min_eq_left (by omega)] at h
    rw [h]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [show i < (height p).toNat ↔ ((i+1:ℕ):ℤ) ≤ height p by omega]
  rw [Finset.sum_congr rfl term,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  rfl

private theorem path_area (w : List Bool) :
    ∑ i ∈ Finset.range (w.length+1), height (w,i) = walkArea w := by
  induction w using List.reverseRecOn with
  | nil => simp [height,displacement,walkArea,heights]
  | append_singleton w a ih =>
    rw [List.length_append,List.length_singleton,Finset.sum_range_succ]
    have he : ∀ i ∈ Finset.range (w.length+1), height (w++[a],i) = height (w,i) := by
      intro i hi
      exact congrArg displacement (List.take_append_of_le_length (by simpa using hi : i ≤ w.length))
    rw [Finset.sum_congr rfl he,ih,walkArea_append]
    have hf : height (w++[a],w.length+1) = displacement w + step a := by
      change displacement ((w++[a]).take (w.length+1)) = _
      rw [List.take_of_length_le (by simp),displacement_snoc]
    simp [hf,walkArea,heights,add_assoc,add_comm]

private theorem path_jensen (c : ℝ) (w : List Bool) :
    ((w.length:ℝ)+1)*Real.exp (c*walkArea w/(w.length+1)) ≤
      ∑ i ∈ Finset.range (w.length+1), Real.exp (c*height (w,i)) := by
  let t := (w.length:ℝ)+1
  let a := c*walkArea w / t
  have ht : t ≠ 0 := by dsimp [t]; positivity
  have ha : t*a = c*walkArea w := by dsimp [a]; field_simp
  have he (x : ℝ) : Real.exp a*(x-a+1) ≤ Real.exp x := by
    apply (mul_le_mul_of_nonneg_left (Real.add_one_le_exp (x-a)) (Real.exp_pos a).le).trans
    rw [← Real.exp_add,add_sub_cancel]
  have h := Finset.sum_le_sum (s := Finset.range (w.length+1))
    (fun i _ => he (c*height (w,i)))
  rw [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum] at h
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,mul_one] at h
  have hs : (∑ i ∈ Finset.range (w.length+1), (height (w,i):ℝ)) = walkArea w := by exact_mod_cast path_area w
  rw [hs,← ha] at h
  change Real.exp a*(t*a-t*a+t) ≤ _ at h
  simpa only [sub_self,zero_add,mul_comm (Real.exp a) t] using h

/-- The exponential moment of area per vertex is at most the marked-height
moment. This finite Gaussian bound holds at every semilength and every
nonnegative real tilt, including zero. -/
theorem area_exp_bound (d : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    ∑ w ∈ dycks d, Real.exp (c*walkArea w/(2*d+1)) ≤
      (dycks d).card * (1 + ∑ i ∈ Finset.range d,
        (Real.exp (c*(i+1))-Real.exp (c*i)) * Real.exp (-(((i:ℝ)+1)*(i+2)/(d+1)))) := by
  let t := 2*(d:ℝ)+1
  have ht : 0 < t := by dsimp [t]; positivity
  let f := fun i : ℕ => Real.exp (c*i)
  have hsum := sum_height d f
  have hcount : (0:ℝ) < (marks d).card := by rw [card_marks]; exact_mod_cast Nat.choose_pos (by omega)
  have hm : ((marks d).card:ℝ) = (dycks d).card*t := by simp [marks,t]
  have norm (i : ℕ) : ((tail d i).card:ℝ) = (marks d).card * heightTail d i := by
    unfold heightTail
    field_simp
  have hex : (∑ p ∈ marks d, f (height p).toNat) =
      (marks d).card * (1+∑ i ∈ Finset.range d, heightTail d (i+1)*(f (i+1)-f i)) := by
    simp only [f,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] at hsum
    rw [hsum,mul_add,mul_one,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [norm,mul_assoc]
  have hj : t*(∑ w ∈ dycks d, Real.exp (c*walkArea w/(2*d+1))) ≤
      ∑ p ∈ marks d, f (height p).toNat := by
    rw [Finset.mul_sum,marks,Finset.sum_product]
    apply Finset.sum_le_sum
    intro w hw
    have hl := (mem_dycks.mp hw).1.1
    have h := path_jensen c w
    rw [hl] at h
    push_cast at h
    apply h.trans
    apply Finset.sum_le_sum
    intro i hi
    have hb := (height_bounds (Finset.mem_product.mpr ⟨hw,hi⟩ : (w,i) ∈ marks d)).1
    change Real.exp _ ≤ Real.exp (c*((height (w,i)).toNat:ℝ))
    rw [← Int.cast_natCast (R := ℝ) (height (w,i)).toNat,Int.toNat_of_nonneg hb]
  rw [hex,hm,mul_right_comm] at hj
  apply (mul_le_mul_iff_right₀ ht).mp
  apply hj.trans
  rw [mul_comm _ t]
  apply mul_le_mul_of_nonneg_left _ ht.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i _
  have hpos : 0 ≤ f (i+1)-f i := sub_nonneg.mpr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ i) hc))
  have h := mul_le_mul_of_nonneg_right (heightTail_gaussian d (i+1)) hpos
  simpa [f,add_assoc,mul_comm,show (1:ℝ)+1 = 2 by norm_num] using h

end CentralUnimodality.MarkedExcursion
