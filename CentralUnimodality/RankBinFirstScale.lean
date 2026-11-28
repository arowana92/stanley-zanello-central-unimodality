module

public import CentralUnimodality.RankBinExponent

/-! Uniform comparison for the three-block first-hit envelope. The
factor m cancels against the number of admissible hit times per bin. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic
open Real

theorem first_scale_to_bin {m k : ℕ} {c z γ σ P : ℝ} {g G shift v e chunk root β F zhi lo den x : ℚ}
    (hm : 4096 ≤ m) (hg : 0 ≤ g) (hgγ : (g:ℝ) ≤ γ) (hγG : γ ≤ (G:ℝ)) (hG : G ≤ 25)
    (hd : 0 ≤ shift) (hv : 0 ≤ v) (he : 0 ≤ e)
    (hchunk : chunk=v/3-2*epsilon) (hroot : root=rootLo chunk) (hrp : 0<root) (hx₀ : 0 ≤ chunk)
    (hb : β=(G+shift)*e/4) (hF : F=2*β+(4/5)/root)
    (hx : x=shift^2*energy/8-v*(1-e/2)^2*(g+shift)*(g*(1-g^2*epsilon/6)+shift)/8) (hxn : x≤0)
    (hden : 0<den) (hP : (den:ℝ) ≤ P*√m) (hlo : 0<lo) (hσ : 0 ≤ σ)
    (hσhi : σ ≤ sizeScale m*zhi) (hσlo : sizeScale m*lo ≤ √(suffixVariance (c+z) (m-(2*k+1))))
    (r : Fin 3) :
    σ^(r.val+1)/(P/m)*pinnedRankAllowance m k c z γ shift v e r ≤
      ((decay (-x)*(1/2+β/128)*F^2/(root*den):ℚ):ℝ)*
        (shortSuffixLimit r*((zhi/lo:ℚ):ℝ)^(r.val+1)) := by
  have hM : (4096:ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0<(m:ℝ) := by linarith
  have hs : 0<sizeScale m := mul_pos hp (sqrt_pos.mpr hp)
  have hdl : 0<(den:ℝ) := by exact_mod_cast hden
  have hpr : 0<P := pos_of_mul_pos_left (hdl.trans_le hP) (sqrt_nonneg _)
  have hr : 0<(root:ℝ) := by exact_mod_cast hrp
  have hz0 : 0<(lo:ℝ) := by exact_mod_cast hlo
  have he₀ : 0 ≤ (e:ℝ) := by exact_mod_cast he
  have hd₀ : 0 ≤ (shift:ℝ) := by exact_mod_cast hd
  have hγ₀ := (show 0 ≤ (g:ℝ) by exact_mod_cast hg).trans hgγ
  let b := (γ+(shift:ℝ))*(e:ℝ)/4
  let t := √((v:ℝ)/3-2/4096)
  let σ' := √(suffixVariance (c+z) (m-(2*k+1)))
  have hb₀ : 0 ≤ b := by dsimp [b]; positivity
  have hβ : b ≤ (β:ℝ) := by
    rw [hb]; push_cast; dsimp [b]; linarith only [mul_le_mul_of_nonneg_right hγG he₀]
  have hrt : (root:ℝ) ≤ t := by
    have H := (root_enclosure hx₀).1
    rw [hroot]; apply H.trans_eq
    rw [hchunk]; dsimp [t,epsilon]; push_cast; norm_num
  have ht : 0<t := hr.trans_le hrt
  have hσ' : 0<σ' := (mul_pos hs hz0).trans_le hσlo
  have hz' : 0 ≤ (zhi:ℝ) := nonneg_of_mul_nonneg_right (hσ.trans hσhi) hs
  have hratio : σ/σ' ≤ (zhi:ℝ)/lo := by
    apply (div_le_div_iff₀ hσ' hz0).mpr
    linarith only [mul_le_mul_of_nonneg_right hσhi hz0.le,mul_le_mul_of_nonneg_right hσlo hz']
  have hpeak : 2*b+(4/5)/t ≤ (F:ℝ) := by
    rw [hF]; push_cast
    linarith only [hβ,div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤4/5) hr hrt]
  have hW := mul_le_mul (show 1/2+b/128 ≤ 1/2+(β:ℝ)/128 by linarith only [hβ])
    (pow_le_pow_left₀ (by positivity) hpeak 2) (sq_nonneg _) (by linarith only [hb₀,hβ])
  have he' := first_bin_exponential hm hg hgγ (hγG.trans (by exact_mod_cast hG)) hd hv hx hxn
  have hfull := mul_le_mul he' hW (by positivity) ((exp_pos _).le.trans he')
  have hden' := mul_le_mul hrt hP hdl.le ht.le
  have hnum := div_le_div₀ (le_trans (by positivity) hfull) hfull (mul_pos hr hdl) hden'
  have hlim : 0 ≤ shortSuffixLimit r := by fin_cases r <;> norm_num [shortSuffixLimit]
  have hpows := pow_le_pow_left₀ (div_nonneg hσ hσ'.le) hratio (r.val+1)
  have hfinal := mul_le_mul hnum (mul_le_mul_of_nonneg_left hpows hlim) (by positivity)
    (by exact div_nonneg (le_trans (by positivity) hfull) (mul_nonneg hr.le hdl.le))
  apply le_trans _ (le_trans hfinal (le_of_eq ?_))
  · apply le_of_eq
    have cancelM (E W p S M R t D K : ℝ) (n : ℕ) (hM : M≠0) :
        S^n/(p/M)*(E*(W/(t*(M*R)))*(K/D^n)) = E*W/(t*(p*R))*(K*(S/D)^n) := by
      rw [div_pow]
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
      linear_combination E*W*t⁻¹*p⁻¹*R⁻¹*K*S^n*(D^n)⁻¹*(inv_mul_cancel₀ hM)
    dsimp only [pinnedRankAllowance]
    apply cancelM _ _ _ _ _ _ _ _ _ _ hp.ne'
  · push_cast; ring

end CentralUnimodality.MarkedExcursion.BinArithmetic
