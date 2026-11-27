module

public import CentralUnimodality.PrefixBounds

/-! Check the overlap between the analytic lower endpoint of each central
window and the increasing prefix, uniformly in the row count. -/
@[expose] public section

namespace CentralUnimodality

private theorem window_bound {n m N b q w c : ℝ}
    (hN : 0 < N) (hn : N ≤ n) (hm' : m ≤ 2*n+1)
    (hb : 2 ≤ b) (hbn : 1 ≤ (b-2)*N) (hq : 0 ≤ q) (hqb : b ≤ q^2)
    (hw : 0 ≤ w) (hwN : w^2 ≤ N) (hc : 0 ≤ c)
    (hgap : 0 ≤ (prefixConstant:ℝ)-2*c*b*q)
    (hbase : 1+2/N ≤ ((prefixConstant:ℝ)-2*c*b*q)*w) :
    2*c*m*Real.sqrt m+1 ≤ (prefixConstant:ℝ)*n*Real.sqrt n-n-1 := by
  have hn₀ := hN.le.trans hn
  have hs : m ≤ b*n := by
    nlinarith only [hm',hbn,mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hn)]
  have hroot : Real.sqrt m ≤ q*Real.sqrt n := by
    apply (Real.sqrt_le_iff).mpr
    rw [mul_pow,Real.sq_sqrt hn₀]
    exact ⟨mul_nonneg hq (Real.sqrt_nonneg _),hs.trans (mul_le_mul_of_nonneg_right hqb hn₀)⟩
  have hw' : w ≤ Real.sqrt n := by
    apply (sq_le_sq₀ hw (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hn₀]
    exact hwN.trans hn
  have hmain := mul_le_mul_of_nonneg_left (mul_le_mul hs hroot (Real.sqrt_nonneg _) (by positivity)) (by positivity : 0 ≤ 2*c)
  have hgap' := mul_le_mul_of_nonneg_right (hbase.trans (mul_le_mul_of_nonneg_left hw' hgap)) hn₀
  have hdiv : 1 ≤ n/N := (le_div_iff₀ hN).mpr (by simpa using hn)
  simp only [div_eq_mul_inv] at hgap' hdiv
  linarith only [hmain,hgap',hdiv]

theorem prefix_window_64 {n m : ℕ} (hn : 64 ≤ n) (hm : m ≤ 2*n+1) :
    2*0.1*(m:ℝ)*Real.sqrt m+1 ≤ (prefixConstant:ℝ)*n*Real.sqrt n-n-1 := by
  apply window_bound (N := 64) (b := 129/64) (q := 1.42) (w := 8)
  all_goals first | exact_mod_cast hn | exact_mod_cast hm | positivity | norm_num [prefixConstant]

theorem prefix_window_2049 {n m : ℕ} (hn : 2049 ≤ n) (hm : m ≤ 2*n+1) :
    2*0.1366*(m:ℝ)*Real.sqrt m+1 ≤ (prefixConstant:ℝ)*n*Real.sqrt n-n-1 := by
  apply window_bound (N := 2049) (b := 4099/2049) (q := 1.4144) (w := 45.26)
  all_goals first | exact_mod_cast hn | exact_mod_cast hm | positivity | norm_num [prefixConstant]

theorem prefix_window_4096 {n m : ℕ} (hn : 4096 ≤ n) (hm : m ≤ 2*n+1) :
    2*0.1378*(m:ℝ)*Real.sqrt m+1 ≤ (prefixConstant:ℝ)*n*Real.sqrt n-n-1 := by
  apply window_bound (N := 4096) (b := 8193/4096) (q := 1.4143) (w := 64)
  all_goals first | exact_mod_cast hn | exact_mod_cast hm | positivity | norm_num [prefixConstant]

end CentralUnimodality
