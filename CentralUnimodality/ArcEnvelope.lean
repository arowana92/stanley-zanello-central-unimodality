module

public import CentralUnimodality.KilledBlock

/-! An executable dyadic upper bound for the unrestricted paired kernel
on an entire real-frequency arc. -/
@[expose] public section

namespace CentralUnimodality

def arcExponent (t : ℚ) (l : ℕ) : ℚ :=
  let a := min t (3/(2*(l:ℚ)))
  let S := ∑ i ∈ Finset.range l, let v := a/2*(2*(i:ℚ)+1); (v*(1-v^2/6))^2
  min ((l:ℚ)/4) S / 4

theorem arcExponent_cast (t : ℚ) (l : ℕ) :
    (arcExponent t l:ℝ) = min ((l:ℝ)/4) (cubicArcSum t l)/4 := by
  unfold arcExponent cubicArcSum
  push_cast
  rfl

private theorem arc_nonneg (t : ℚ) (l : ℕ) : 0 ≤ arcExponent t l := by
  unfold arcExponent
  dsimp only
  positivity

def envelopeUnits (t : ℚ) (m : ℕ) : ℕ := ⌈4096/(1+arcExponent t (m/2)/64)^64⌉₊

theorem envelope_bound {t : ℚ} {θ : ℝ} (ht : 0 ≤ t) (htθ : (t:ℝ) ≤ θ) (hπ : θ ≤ Real.pi) (m : ℕ) :
    pairFactor (θ/2) (m/2) ≤ (envelopeUnits t m:ℝ)/4096 := by
  let l := m/2
  let x := arcExponent t l
  have hx : 0 ≤ x := arc_nonneg ..
  have h₁ : pairFactor (θ/2) l ≤ Real.exp (-(x:ℝ)) := by
    by_cases hl : l = 0
    · simp [x,hl,arcExponent,pairFactor]
    · have h := pairFactor_arc (Nat.pos_of_ne_zero hl) (by exact_mod_cast ht : (0:ℝ) ≤ t) htθ hπ
      rw [neg_div,← arcExponent_cast] at h
      exact h
  have hx' : (0:ℝ) ≤ x := by exact_mod_cast hx
  have h₂ : (1+(x:ℝ)/64)^64 ≤ Real.exp x := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1+(x:ℝ)/64)
      (by linarith only [Real.add_one_le_exp ((x:ℝ)/64)] : 1+(x:ℝ)/64 ≤ Real.exp ((x:ℝ)/64)) 64
    rw [← Real.exp_nat_mul] at h
    norm_num only [Nat.cast_ofNat] at h
    rwa [show (64:ℝ)*((x:ℝ)/64) = x by ring] at h
  have hp : 0 < (1+(x:ℝ)/64)^64 := by positivity
  have hu : 4096/(1+(x:ℝ)/64)^64 ≤ envelopeUnits t m := by
    have huq : (4096/(1+x/64)^(64:ℕ):ℚ) ≤ (envelopeUnits t m:ℚ) := Nat.le_ceil _
    exact_mod_cast huq
  apply h₁.trans
  rw [Real.exp_neg]
  apply (inv_anti₀ hp h₂).trans
  apply (le_div_iff₀ (by norm_num)).mpr
  simpa only [div_eq_mul_inv,mul_comm] using hu

theorem rate_lower_exp (x : ℝ) (hx : x ≤ 128) :
    (1-x/128)^128 ≤ Real.exp (-x) := by
  have h := pow_le_pow_left₀ (by linarith : 0 ≤ 1-x/128)
    (by linarith only [Real.add_one_le_exp (-x/128)] : 1-x/128 ≤ Real.exp (-x/128)) 128
  rw [← Real.exp_nat_mul] at h
  norm_num only [Nat.cast_ofNat] at h
  rwa [show (128:ℝ)*(-x/128) = -x by ring] at h

end CentralUnimodality
