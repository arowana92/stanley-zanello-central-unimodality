module

public import CentralUnimodality.ScaledKilledBlock

/-! Exact rational bounds for the two finite upper sums. A positive
14th-degree Taylor sum bounds each exponential reciprocal. Rounding each
bin upwards at 24 bits keeps the total denominator small. -/
@[expose] public section

namespace CentralUnimodality

def upperNegExp (x : ℚ) : ℚ := (∑ i ∈ Finset.range 15, x^i/i.factorial)⁻¹

theorem upperNegExp_sound {x : ℚ} (hx : 0 ≤ x) : Real.exp (-(x:ℝ)) ≤ (upperNegExp x:ℝ) := by
  have hxr : (0:ℝ) ≤ x := by exact_mod_cast hx
  have hp : 0 < ∑ i ∈ Finset.range 15, (x:ℝ)^i/i.factorial := by
    apply Finset.sum_pos' (fun _ _ => by positivity)
    exact ⟨0,by decide,by norm_num⟩
  unfold upperNegExp
  push_cast
  rw [Real.exp_neg]
  exact inv_anti₀ hp (Real.sum_le_exp_of_nonneg hxr 15)

def numericBin (c : ℚ) (M low i : ℕ) : ℚ :=
  if low ≤ i then
    let u := max 0 (1-((i:ℚ)+1)/400-2/(M:ℚ))
    upperNegExp (c*u^3)/(4*i)
  else 0

def chargeUnits (c : ℚ) (M low i : ℕ) := ⌈16777216*numericBin c M low i⌉₊

theorem chargeUnits_sound {c : ℚ} (hc : 0 ≤ c) (M low i : ℕ) :
    binCharge c M low i ≤ (chargeUnits c M low i:ℝ)/16777216 := by
  have hb : binCharge c M low i ≤ (numericBin c M low i:ℝ) := by
    unfold binCharge numericBin
    split
    next _ =>
      simp only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast]
      apply div_le_div_of_nonneg_right _ (by positivity)
      let u := max 0 (1-((i:ℚ)+1)/400-2/(M:ℚ))
      have he := upperNegExp_sound (mul_nonneg hc (pow_nonneg (le_max_left 0 _) 3) : 0 ≤ c*u^3)
      simpa [u,binRemainder] using he
    next _ => simp
  apply hb.trans
  apply (le_div_iff₀ (by norm_num)).mpr
  have hu := Nat.le_ceil (16777216*numericBin c M low i)
  unfold chargeUnits
  exact_mod_cast (by simpa only [mul_comm] using hu : numericBin c M low i*16777216 ≤ _)

def innerSumCap (c : ℚ) (M low : ℕ) : ℚ :=
  upperNegExp c + upperNegExp (c*(9/10)^3) +
    (∑ i ∈ Finset.range 400, chargeUnits c M low i:ℕ)/ (16777216:ℚ)

theorem innerSumCap_sound {c : ℚ} (hc : 0 ≤ c) (M low : ℕ) :
    Real.exp (-(c:ℝ)) + Real.exp (-(c*(9/10:ℝ)^3)) +
      ∑ i ∈ Finset.range 400, binCharge c M low i ≤ (innerSumCap c M low:ℝ) := by
  unfold innerSumCap
  push_cast
  apply add_le_add (add_le_add (upperNegExp_sound hc) _) _
  · simpa using upperNegExp_sound (mul_nonneg hc (by norm_num) : 0 ≤ c*(9/10)^3)
  · simp only [div_eq_mul_inv,Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => chargeUnits_sound hc M low i)

def innerLowerExp (x : ℚ) := (1-x/2048)^2048

theorem innerLowerExp_sound {x : ℚ} (hx : x ≤ 2048) :
    (innerLowerExp x:ℝ) ≤ Real.exp (-(x:ℝ)) := by
  have hx' : (x:ℝ) ≤ 2048 := by exact_mod_cast hx
  have h := pow_le_pow_left₀ (by linarith : 0 ≤ 1-(x:ℝ)/2048)
    (by linarith only [Real.add_one_le_exp (-(x:ℝ)/2048)] :
      1-(x:ℝ)/2048 ≤ Real.exp (-(x:ℝ)/2048)) 2048
  rw [← Real.exp_nat_mul] at h
  unfold innerLowerExp
  push_cast
  convert h using 2
  push_cast
  ring

set_option maxRecDepth 50000 in
theorem two_inner_caps :
    innerSumCap (0.93*9^3/96) 900 39 ≤ innerLowerExp (9.01*0.1^4/96+0.1895*9.01) ∧
    innerSumCap (0.74*9^3/96) 225 36 ≤ innerLowerExp (9.04*0.2^4/96+0.16*9.04) := by
  decide +kernel

end CentralUnimodality
