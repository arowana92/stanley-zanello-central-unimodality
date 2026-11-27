module

public import CentralUnimodality.DyadicAngle

/-! Outward integer bounds for the nonnegative products and quotients in
the small-angle free and bridge recurrences. All numbers share scale d. -/
@[expose] public section

namespace CentralUnimodality.PositiveEnclosure

def Holds (d : ℕ) (a : ℕ × ℕ) (x : ℝ) : Prop :=
  (a.1:ℝ) ≤ d*x ∧ d*x ≤ (a.2:ℝ)

def one (d : ℕ) := (d,d)
def sum (a b : ℕ × ℕ) := (a.1+b.1,a.2+b.2)
def difference (a b : ℕ × ℕ) := (a.1-b.2,a.2-b.1)
def product (d : ℕ) (a b : ℕ × ℕ) := (a.1*b.1/d,a.2*b.2/d+1)
def halfQuotient (d : ℕ) (a b : ℕ × ℕ) := (d*a.1/(2*b.2),d*a.2/(2*b.1)+1)

theorem holds_one (d : ℕ) : Holds d (one d) 1 := by simp [Holds,one]

theorem holds_sum {d : ℕ} {a b : ℕ × ℕ} {x y : ℝ} (ha : Holds d a x) (hb : Holds d b y) :
    Holds d (sum a b) (x+y) := by
  simpa only [Holds,sum,Nat.cast_add,mul_add] using And.intro (add_le_add ha.1 hb.1) (add_le_add ha.2 hb.2)

theorem holds_difference {d : ℕ} {a b : ℕ × ℕ} {x y : ℝ} (ha : Holds d a x) (hb : Holds d b y)
    (hyx : y ≤ x) : Holds d (difference a b) (x-y) := by
  have hd : 0 ≤ (d:ℝ)*(x-y) := mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hyx)
  have hr := (sub_le_sub ha.2 hb.1)
  have ht : b.1 ≤ a.2 := by
    exact_mod_cast (hb.1.trans ((mul_le_mul_of_nonneg_left hyx (Nat.cast_nonneg d)).trans ha.2))
  refine ⟨?_,by simpa only [difference,Nat.cast_sub ht,mul_sub] using hr⟩
  by_cases hl : b.2 ≤ a.1
  · simpa only [difference,Nat.cast_sub hl,mul_sub] using sub_le_sub ha.1 hb.2
  · simpa only [difference,Nat.sub_eq_zero_of_le (by omega : a.1 ≤ b.2),Nat.cast_zero] using hd

private theorem floor_bounds (x : ℕ) {y : ℕ} (hy : 0 < y) :
    (x/y:ℕ)*(y:ℝ) ≤ x ∧ (x:ℝ) ≤ ((x/y:ℕ)+1)*(y:ℝ) := by
  constructor
  · exact_mod_cast Nat.div_mul_le_self x y
  · exact_mod_cast (Nat.lt_mul_div_succ x hy).le.trans_eq (Nat.mul_comm y (x/y+1))

private theorem pos_value {d : ℕ} (hd : 0 < d) {a : ℕ × ℕ} {x : ℝ} (h : Holds d a x) : 0 ≤ x := by
  exact nonneg_of_mul_nonneg_right ((Nat.cast_nonneg a.1).trans h.1) (by exact_mod_cast hd : (0:ℝ)<d)

theorem holds_product {d : ℕ} (hd : 0 < d) {a b : ℕ × ℕ} {x y : ℝ}
    (ha : Holds d a x) (hb : Holds d b y) : Holds d (product d a b) (x*y) := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have lo := mul_le_mul ha.1 hb.1 (Nat.cast_nonneg _) (mul_nonneg hd'.le (pos_value hd ha))
  have hi := mul_le_mul ha.2 hb.2 (mul_nonneg hd'.le (pos_value hd hb)) (Nat.cast_nonneg _)
  have h₁ := (floor_bounds (a.1*b.1) hd).1
  have h₂ := (floor_bounds (a.2*b.2) hd).2
  push_cast at h₁ h₂
  change ((a.1*b.1/d:ℕ):ℝ) ≤ d*(x*y) ∧ d*(x*y) ≤ ((a.2*b.2/d+1:ℕ):ℝ)
  push_cast
  constructor
  · apply le_of_mul_le_mul_right (a := (d:ℝ)) _ hd'
    nlinarith only [lo,h₁]
  · apply le_of_mul_le_mul_right (a := (d:ℝ)) _ hd'
    nlinarith only [hi,h₂]

theorem holds_halfQuotient {d : ℕ} (hd : 0 < d) {a b : ℕ × ℕ} {x y : ℝ}
    (ha : Holds d a x) (hb : Holds d b y) (hn : 0 < b.1) :
    Holds d (halfQuotient d a b) (x/(2*y)) := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hn' : (0:ℝ) < b.1 := by exact_mod_cast hn
  have hy : 0 < y := pos_of_mul_pos_right (hn'.trans_le hb.1) hd'.le
  have hbu : 0 < b.2 := by exact_mod_cast hn'.trans_le (hb.1.trans hb.2)
  have h₁ := (floor_bounds (d*a.1) (Nat.mul_pos (by decide : 0<2) hbu)).1
  have h₂ := (floor_bounds (d*a.2) (Nat.mul_pos (by decide : 0<2) hn)).2
  let l : ℝ := (d*a.1/(2*b.2):ℕ)
  let u : ℝ := (d*a.2/(2*b.1):ℕ)+1
  have hl : 0 ≤ l := by dsimp [l]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  change l*(2*b.2:ℕ) ≤ (d*a.1:ℕ) at h₁
  change ((d*a.2:ℕ):ℝ) ≤ u*(2*b.1:ℕ) at h₂
  push_cast at h₁ h₂
  have lo := mul_le_mul_of_nonneg_left hb.2 (mul_nonneg (by norm_num : (0:ℝ)≤2) hl)
  have hi := mul_le_mul_of_nonneg_left hb.1 (mul_nonneg (by norm_num : (0:ℝ)≤2) hu)
  have ha₁ := mul_le_mul_of_nonneg_left ha.1 hd'.le
  have ha₂ := mul_le_mul_of_nonneg_left ha.2 hd'.le
  change l ≤ d*(x/(2*y)) ∧ d*(x/(2*y)) ≤ _
  rw [← mul_div_assoc]
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 2*y)).mpr
    apply le_of_mul_le_mul_left (a := (d:ℝ)) _ hd'
    nlinarith only [h₁,lo,ha₁]
  · simp only [halfQuotient,Nat.cast_add,Nat.cast_one]
    change (d:ℝ)*x/(2*y) ≤ u
    apply (div_le_iff₀ (by positivity : 0 < 2*y)).mpr
    apply le_of_mul_le_mul_left (a := (d:ℝ)) _ hd'
    nlinarith only [h₂,hi,ha₂]

end CentralUnimodality.PositiveEnclosure
