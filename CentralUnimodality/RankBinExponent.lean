module

public import CentralUnimodality.RankBinSetup

/-! Bound the true quadratic label cost and the cubic drift over a full
saddle bin, including the outward rounding in the exponential. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic
open Real

theorem bin_energy {m : ℕ} (hm : 4096 ≤ m) :
    labelSquares m/(m:ℝ)^3 ≤ (energy:ℝ) := by
  have hM : (4096:ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0<(m:ℝ) := by linarith
  have hi : 1/(m:ℝ) ≤ 1/4096 := one_div_le_one_div_of_le (by norm_num) hM
  have hh := mul_le_mul (add_le_add_left hi 1) (add_le_add_left hi 2)
    (by positivity) (by norm_num)
  have he : labelSquares m/(m:ℝ)^3=(1+1/(m:ℝ))*(2+1/(m:ℝ))/6 := by
    unfold labelSquares; field_simp
  rw [he]
  norm_num [energy,epsilon] at *
  linarith only [hh]

theorem bin_cubic_drift {M g γ : ℝ} (hM : 4096 ≤ M) (hg : 0 ≤ g) (hgγ : g ≤ γ) (hγ : γ ≤ 25) :
    g*(1-g^2/(6*4096)) ≤ γ*(1-γ^2/(6*M)) := by
  have hp : 0<M := by linarith
  have hγ₀ := hg.trans hgγ
  have hg' := hgγ.trans hγ
  have hs : g^2+g*γ+γ^2 ≤ 3*25^2 := by
    nlinarith only [pow_le_pow_left₀ hg hg' 2,mul_le_mul hg' hγ hγ₀ (by norm_num),
      pow_le_pow_left₀ hγ₀ hγ 2]
  have h₁ := mul_le_mul_of_nonneg_right hs (sub_nonneg.mpr hgγ)
  have h₂ := div_le_div_of_nonneg_left (pow_nonneg hγ₀ 3) (by norm_num : (0:ℝ)<6*4096)
    (show 6*4096 ≤ 6*M by linarith)
  have form : γ*(1-γ^2/(6*M))=γ-γ^3/(6*M) := by ring
  rw [form]
  linarith only [h₁,h₂,hgγ]

theorem late_bin_exponential {m : ℕ} (hm : 4096 ≤ m) {d a x : ℚ}
    (hx : x=d^2*energy/8-a^2/2) (hn : x ≤ 0) :
    exp ((d:ℝ)^2*(labelSquares m/(m:ℝ)^3)/8-(a:ℝ)^2/2) ≤ (decay (-x):ℝ) := by
  have H := mul_le_mul_of_nonneg_left (bin_energy hm) (sq_nonneg (d:ℝ))
  have eq := congrArg (fun y : ℚ => (y:ℝ)) hx
  push_cast at eq
  apply le_trans (exp_le_exp.mpr (show _ ≤ (x:ℝ) by linarith only [H,eq]))
  simpa using decay_upper (neg_nonneg.mpr hn)

theorem first_bin_exponential {m : ℕ} (hm : 4096 ≤ m) {g d v e x : ℚ} {γ : ℝ}
    (hg : 0 ≤ g) (hgγ : (g:ℝ) ≤ γ) (hγ : γ ≤ 25) (hd : 0 ≤ d) (hv : 0 ≤ v)
    (hx : x=d^2*energy/8-v*(1-e/2)^2*(g+d)*(g*(1-g^2*epsilon/6)+d)/8) (hn : x ≤ 0) :
    exp ((d:ℝ)^2*(labelSquares m/(m:ℝ)^3)/8-(v:ℝ)*(1-(e:ℝ)/2)^2*
      (γ+d)*(γ*(1-γ^2/(6*m))+d)/8) ≤ (decay (-x):ℝ) := by
  have hM : (4096:ℝ) ≤ m := by exact_mod_cast hm
  have hg₀ : 0 ≤ (g:ℝ) := by exact_mod_cast hg
  have hd₀ : 0 ≤ (d:ℝ) := by exact_mod_cast hd
  have hv₀ : 0 ≤ (v:ℝ) := by exact_mod_cast hv
  have hgc := bin_cubic_drift hM hg₀ hgγ hγ
  have hsq := pow_le_pow_left₀ hg₀ (hgγ.trans hγ) 2
  have hgp : 0 ≤ (g:ℝ)*(1-(g:ℝ)^2/(6*4096)) := mul_nonneg hg₀ (by linarith only [hsq])
  have hprod := mul_le_mul (add_le_add_right hgγ (d:ℝ)) (add_le_add_right hgc (d:ℝ))
    (add_nonneg hd₀ hgp) (add_nonneg hd₀ (hg₀.trans hgγ))
  have hcost := mul_le_mul_of_nonneg_left hprod (mul_nonneg hv₀ (sq_nonneg (1-(e:ℝ)/2)))
  have H := mul_le_mul_of_nonneg_left (bin_energy hm) (sq_nonneg (d:ℝ))
  have eq := congrArg (fun y : ℚ => (y:ℝ)) hx
  dsimp [epsilon] at eq; push_cast at eq
  apply le_trans (exp_le_exp.mpr (show _ ≤ (x:ℝ) by linarith only [H,eq,hcost]))
  simpa using decay_upper (neg_nonneg.mpr hn)

end CentralUnimodality.MarkedExcursion.BinArithmetic
