module

public import CentralUnimodality.InnerArcNumbers

/-! Rational upper bound for a negative exponential. Each step of
0.693147181 in the exponent pays for a factor of two. The remainder
uses the positive Taylor sum already verified for the inner arc. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Real

def expStep : ℚ := 693147181/1000000000

def scaledNegExp (x : ℚ) : ℚ :=
  let y := min x 300
  let k := ⌊y/expStep⌋₊
  upperNegExp (y-k*expStep)/2^k

private theorem step_exp : 2≤exp (expStep:ℝ) := by
  have h := upperNegExp_sound (show 0≤expStep by norm_num [expStep])
  have b : upperNegExp expStep≤1/2 := by decide +kernel
  have s : (upperNegExp expStep:ℝ)≤1/2 := by simpa using (Rat.cast_le (K:=ℝ)).mpr b
  have v := h.trans s
  rw [exp_neg,inv_eq_one_div,div_le_div_iff₀ (exp_pos _) (by norm_num)] at v
  linarith only [v]

theorem scaledNegExp_sound {x : ℚ} (hx : 0≤x) : exp (-(x:ℝ))≤(scaledNegExp x:ℝ) := by
  let y := min x 300
  let k := ⌊y/expStep⌋₊
  have yp : 0≤y := le_min hx (by norm_num)
  have st : 0<expStep := by norm_num [expStep]
  have rem : 0≤y-k*expStep := sub_nonneg.mpr ((le_div_iff₀ st).mp (Nat.floor_le (div_nonneg yp st.le)))
  have ey : exp (-(x:ℝ))≤exp (-(y:ℝ)) :=
    exp_le_exp.mpr (neg_le_neg (by exact_mod_cast min_le_left x (300:ℚ)))
  have decomp : exp (-(y:ℝ))=exp (-((y-k*expStep:ℚ):ℝ))/(exp (expStep:ℝ))^k := by
    rw [← exp_nat_mul,← exp_sub]
    push_cast; congr 1; ring
  apply ey.trans
  rw [decomp]
  change _≤((upperNegExp (y-k*expStep)/2^k:ℚ):ℝ)
  push_cast
  have upper := upperNegExp_sound rem
  push_cast at upper
  exact div_le_div₀ ((exp_nonneg _).trans upper) upper (by positivity) (pow_le_pow_left₀ (by norm_num) step_exp k)

end CentralUnimodality.PolynomialTrial
