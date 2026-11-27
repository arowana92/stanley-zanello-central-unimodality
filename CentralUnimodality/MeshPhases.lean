module

public import CentralUnimodality.DyadicAngle
public import CentralUnimodality.SpatialDerivatives

/-! Rounded cosine samples at every point of a complete dyadic period.
Reflection and periodicity handle all derivative phase shifts. -/
@[expose] public section

namespace CentralUnimodality.MeshPhase

def foldTick (k j : ℕ) : ℕ :=
  let t := j % (2^(k+1))
  min t (2^(k+1)-t)

private theorem folded_cos (k j : ℕ) :
    foldTick k j ≤ 2^k ∧ Real.cos (2*Real.pi*j/2^(k+1)) =
      Real.cos ((foldTick k j:ℝ)*Real.pi/2^k) := by
  let H := 2^(k+1)
  let t := j%H
  have hH : 0 < H := by dsimp [H]; positivity
  have ht : t < H := Nat.mod_lt _ hH
  have hd : j = t + H*(j/H) := (Nat.mod_add_div j H).symm
  have hc : Real.cos (2*Real.pi*j/2^(k+1)) = Real.cos ((t:ℝ)*Real.pi/2^k) := by
    have h : (j:ℝ) = t+(2:ℝ)^(k+1)*(j/H:ℕ) := by exact_mod_cast hd
    have he : 2*Real.pi*j/2^(k+1) = (t:ℝ)*Real.pi/2^k+(j/H:ℕ)*(2*Real.pi) := by
      rw [h,pow_succ]
      field_simp
    rw [he,Real.cos_add_nat_mul_two_pi]
  have hpow : H = 2^k*2 := pow_succ ..
  by_cases hh : t ≤ 2^k
  · have he : foldTick k j = t := min_eq_left (by omega : t ≤ H-t)
    rw [he]
    exact ⟨hh,hc⟩
  · have he : foldTick k j = H-t := min_eq_right (by omega : H-t ≤ t)
    refine ⟨by rw [he]; omega,hc.trans ?_⟩
    have hx : ((H-t:ℕ):ℝ)*Real.pi/2^k = 2*Real.pi-(t:ℝ)*Real.pi/2^k := by
      rw [Nat.cast_sub ht.le,hpow,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      field_simp
    rw [he,hx,Real.cos_two_pi_sub]

def midpoint (bounds : ℕ × ℕ) := (bounds.1+bounds.2)/2
def radius (bounds : ℕ × ℕ) := bounds.2-midpoint bounds
def sample (d k j : ℕ) : ℤ := (midpoint (DyadicAngle.bounds d k (foldTick k j)):ℤ)-d

theorem sample_error {d k j : ℕ} (hd : 0 < d) :
    |Real.cos (2*Real.pi*j/2^(k+1))-(sample d k j:ℝ)/d| ≤
      (radius (DyadicAngle.bounds d k (foldTick k j)):ℝ)/d := by
  obtain ⟨ht,hcos⟩ := folded_cos k j
  let v := DyadicAngle.bounds d k (foldTick k j)
  have hh := DyadicAngle.bounds_sound d k _ ht
  change (v.1:ℝ) ≤ _ ∧ _ ≤ (v.2:ℝ) at hh
  have hle : v.1 ≤ v.2 := by exact_mod_cast hh.1.trans hh.2
  have hmid : midpoint v ≤ v.2 := by dsimp [midpoint]; omega
  have hl : midpoint v ≤ v.1+radius v := by dsimp [midpoint,radius] at *; omega
  have hl' : (midpoint v:ℝ) ≤ v.1+(radius v:ℝ) := by exact_mod_cast hl
  have hu : (radius v:ℝ) = (v.2:ℝ)-midpoint v := Nat.cast_sub hmid
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  rw [hcos,sample,Int.cast_sub,Int.cast_natCast,Int.cast_natCast,sub_div' hd'.ne',abs_div,abs_of_pos hd',
    div_le_div_iff_of_pos_right hd',abs_le]
  change -(radius v:ℝ) ≤ _ - ((midpoint v:ℝ)-d) ∧ _ - ((midpoint v:ℝ)-d) ≤ radius v
  constructor <;> nlinarith only [hh.1,hh.2,hl',hu]

def radiusCheck (d k e : ℕ) := (List.range (2^k+1)).all fun t => decide (radius (DyadicAngle.bounds d k t) ≤ e)

theorem uniform_sample_error {d k e : ℕ} (hd : 0 < d) (h : radiusCheck d k e = true) (j : ℕ) :
    |Real.cos (2*Real.pi*j/2^(k+1))-(sample d k j:ℝ)/d| ≤ (e:ℝ)/d := by
  have ht := (folded_cos k j).1
  have hh := List.all_eq_true.mp h (foldTick k j) (List.mem_range.mpr (by omega))
  apply (sample_error hd).trans
  exact div_le_div_of_nonneg_right (by exact_mod_cast of_decide_eq_true hh) (Nat.cast_nonneg _)

end CentralUnimodality.MeshPhase
