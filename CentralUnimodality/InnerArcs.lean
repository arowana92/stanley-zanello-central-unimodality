module

public import CentralUnimodality.InnerArcNumbers

/-! For frequency θ = z³ take the block length ceil(9/z²). The two
rational certificates apply uniformly down to arbitrarily small z. -/
@[expose] public section

namespace CentralUnimodality

noncomputable def innerLength (z : ℝ) : ℕ := ⌈9/z^2⌉₊

theorem innerLength_bounds {z : ℝ} (hz : 0 < z) :
    9 ≤ z^2*innerLength z ∧ z^2*innerLength z ≤ 9+z^2 := by
  have hp : 0 < z^2 := by positivity
  have h₁ := (div_le_iff₀ hp).mp (Nat.le_ceil (9/z^2))
  have h₂ := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (by positivity : 0 ≤ 9/z^2)).le hp.le
  unfold innerLength
  rw [add_mul,div_mul_cancel₀ _ hp.ne',one_mul] at h₂
  constructor <;> linarith only [h₁,h₂]

private theorem inner_rate {z : ℝ} {Z S v γ : ℚ} {M low : ℕ} (hz : 0 < z) (hZ : z ≤ (Z:ℝ))
    (hM : 20 ≤ M) (hML : (M:ℚ)*Z^2 ≤ 9) (hS : 9+Z^2 ≤ S)
    (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hγ : 0 ≤ γ) (hH : (S*Z/2)^2 ≤ 6) (hv : v ≤ (1-(S*Z/2)^2/6)^2)
    (hlow : 0 < low) (hlo : (low:ℚ)/400+2/(M:ℚ) ≤ 1/10)
    (hx : S*Z^4/96+γ*S ≤ 2048)
    (hcap : innerSumCap (v*9^3/96) M low ≤ innerLowerExp (S*Z^4/96+γ*S)) :
    KilledBound (z^3/2) (innerLength z)
      (Real.exp (-((γ:ℝ)*z^2)*(innerLength z))) := by
  let L := innerLength z
  let c := v*9^3/96
  let e := S*Z^4/96
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hSr : 9+(Z:ℝ)^2 ≤ S := by exact_mod_cast hS
  have hvr : (0:ℝ) ≤ v := by exact_mod_cast hv₀
  have hvr' : (v:ℝ) ≤ 1 := by exact_mod_cast hv₁
  have hγr : (0:ℝ) ≤ γ := by exact_mod_cast hγ
  have hZr : (0:ℝ) < Z := hz.trans_le hZ
  obtain ⟨hl,hu⟩ := innerLength_bounds hz
  change 9 ≤ z^2*(L:ℝ) at hl
  change z^2*(L:ℝ) ≤ 9+z^2 at hu
  have hlen := hu.trans ((add_le_add_right (pow_le_pow_left₀ hz.le hZ 2) 9).trans hSr)
  have hm : M ≤ L := by
    have hmr : (M:ℝ)*(Z:ℝ)^2 ≤ 9 := by exact_mod_cast hML
    have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz.le hZ 2) (Nat.cast_nonneg (α := ℝ) M)
    have hr : (M:ℝ) ≤ (L:ℝ) := le_of_mul_le_mul_right ((h.trans hmr).trans (by simpa only [mul_comm] using hl)) (by positivity : 0 < z^2)
    exact_mod_cast hr
  have hupper : z^3/2*L ≤ (S:ℝ)*Z/2 := by
    have hs := mul_le_mul hlen hZ hz.le (by linarith only [hSr,sq_nonneg (Z:ℝ)] : (0:ℝ) ≤ S)
    linarith only [hs]
  have hcubic : (c:ℝ) ≤ v*(z^3)^2*(L:ℝ)^3/96 := by
    have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 9) hl 3) hvr
    dsimp [c]
    push_cast
    nlinarith only [h]
  have hlinear : (v:ℝ)*(z^3)^2*L/96 ≤ e := by
    have h := mul_le_mul hlen (pow_le_pow_left₀ hz.le hZ 4) (pow_nonneg hz.le 4)
      (by linarith only [hSr,sq_nonneg (Z:ℝ)] : (0:ℝ) ≤ S)
    have hh := mul_le_mul_of_nonneg_right hvr' (by positivity : 0 ≤ (z^3)^2*(L:ℝ))
    dsimp [e]
    push_cast
    nlinarith only [h,hh]
  have hb := scaled_killed_cubic hvr (pow_nonneg hz.le 3) hM hm hlow (by simpa using (Rat.cast_le (K := ℝ)).mpr hlo)
    hupper (by exact_mod_cast hH) (by exact_mod_cast hv) (by exact_mod_cast hc : (0:ℝ) ≤ c) hcubic hlinear
  have hsum := (innerSumCap_sound hc M low).trans
    ((by exact_mod_cast hcap : (innerSumCap c M low:ℝ) ≤ (innerLowerExp (e+γ*S):ℝ)).trans (innerLowerExp_sound hx))
  have hsc : Real.exp (e:ℝ)*Real.exp (-((e+γ*S:ℚ):ℝ)) ≤ Real.exp (-((γ:ℝ)*z^2)*(L:ℝ)) := by
    rw [← Real.exp_add,Real.exp_le_exp]
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left hlen hγr]
  intro a ha s
  apply (hb a ha s).trans
  exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le).trans hsc) (by positivity)

theorem killed_inner_001 {z : ℝ} (hz : 0 < z) (hZ : z ≤ 0.1) :
    KilledBound (z^3/2) (innerLength z) (Real.exp (-(0.1895*z^2)*innerLength z)) := by
  apply inner_rate (Z := 0.1) (S := 9.01) (v := 0.93) (γ := 0.1895) (M := 900) (low := 39) hz
  all_goals first | exact_mod_cast hZ | exact two_inner_caps.1 | norm_num

theorem killed_inner_008 {z : ℝ} (hz : 0 < z) (hZ : z ≤ 0.2) :
    KilledBound (z^3/2) (innerLength z) (Real.exp (-(0.16*z^2)*innerLength z)) := by
  apply inner_rate (Z := 0.2) (S := 9.04) (v := 0.74) (γ := 0.16) (M := 225) (low := 36) hz
  all_goals first | exact_mod_cast hZ | exact two_inner_caps.2 | norm_num

end CentralUnimodality
