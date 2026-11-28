module

public import CentralUnimodality.SymbolLogBounds
public import CentralUnimodality.SurvivalBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp

/-! Exact real logarithms of the free and normalized bridge symbols on a
small arc. The Gaussian terms can then be compared coefficient by coefficient. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open PowerSeries Real

noncomputable def freeLog (ω : ℝ) (t : ℕ) :=
  ∑ k ∈ Finset.range t, log (cos (ω*(k+1)))

noncomputable def bridgeLog (ω : ℝ) (j : ℕ) :=
  ∑ k ∈ Finset.range j, (log (cos (ω*(k+1))) + log (sinc (ω*(2*k+1))) -
    log (sinc (ω*(k+1))))

theorem cos_pos_nine_eighths {x : ℝ} (hx : |x|≤9/8) : 0<cos x :=
  cos_pos_of_mem_Ioo ⟨by linarith only [(abs_le.mp hx).1,pi_gt_three],by linarith only [(abs_le.mp hx).2,pi_gt_three]⟩

theorem sinc_pos_nine_eighths {x : ℝ} (hx : |x|≤9/8) : 0<sinc x :=
  (cos_pos_nine_eighths hx).trans_le (cos_le_sinc (by linarith only [hx,pi_gt_three]))

private theorem sin_eq_mul_sinc (x : ℝ) : sin x=x*sinc x := by
  by_cases h : x=0
  · simp [h]
  · rw [sinc_of_ne_zero h]; field_simp

theorem freeSymbol_log_wide (ω : ℝ) {t : ℕ} (ha : |ω| * t≤9/8) :
    coeff t (fairSeries (areaCharacter ω) words) = (exp (freeLog ω t):ℂ) := by
  rw [fourier_free_product,freeLog,exp_sum,Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro k hk
  have hkt : (k:ℝ)+1≤t := by exact_mod_cast Finset.mem_range.mp hk
  have hangle : |ω*((k:ℝ)+1)|≤9/8 := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤(k:ℝ)+1)]
    exact (mul_le_mul_of_nonneg_left hkt (abs_nonneg _)).trans ha
  rw [exp_log (cos_pos_nine_eighths hangle)]

theorem bridgeSymbol_log_wide {ω : ℝ} (hω : ω≠0) {j : ℕ} (ha : |ω| * (2*j:ℝ)≤9/8) :
    coeff (2*j) (fairSeries (areaCharacter ω) bridges) =
      ((survival j*exp (bridgeLog ω j):ℝ):ℂ) := by
  induction j with
  | zero =>
    have emp : bridges 0={[]} := by decide
    simp [coeff_walkSeries,bridgeLog,survival,emp,walkArea,heights,areaCharacter]
  | succ j ih =>
    push_cast at ha
    have weak {x : ℝ} (hx : 0≤x) (hx' : x≤2*(j+1:ℝ)) : |ω*x|≤9/8 := by
      rw [abs_mul,abs_of_nonneg hx]
      exact (mul_le_mul_of_nonneg_left hx' (abs_nonneg _)).trans ha
    have hprev : |ω| * (2*j:ℝ)≤9/8 :=
      (mul_le_mul_of_nonneg_left (by linarith : (2*j:ℝ)≤2*(j+1)) (abs_nonneg _)).trans ha
    let b := ω*((j:ℝ)+1)
    let c := ω*(2*j+1)
    have hb : |b|≤9/8 := weak (by positivity) (by linarith [Nat.cast_nonneg (α:=ℝ) j])
    have hc : |c|≤9/8 := weak (by positivity) (by linarith)
    have hs := sinc_pos_nine_eighths hb
    have bne : b≠0 := mul_ne_zero hω (by positivity)
    have hsin : sin b≠0 := by rw [sin_eq_mul_sinc]; exact mul_ne_zero bne hs.ne'
    have next : exp (bridgeLog ω (j+1)) =
        exp (bridgeLog ω j) * (cos b*sinc c/sinc b) := by
      rw [bridgeLog,Finset.sum_range_succ,exp_add,exp_sub,exp_add,
        exp_log (cos_pos_nine_eighths hb),exp_log (sinc_pos_nine_eighths hc),exp_log hs]
      rfl
    rw [next,show 2*(j+1)=2*j+2 by omega]
    apply mul_left_cancel₀ (a:=2*(sin b:ℂ)) (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hsin))
    rw [fair_bridge_sine_step,ih hprev]
    change (cos b:ℂ)*(sin c:ℂ)*_ = (2:ℂ)*(sin b:ℂ)*_
    norm_cast
    rw [sin_eq_mul_sinc c,sin_eq_mul_sinc b,survival_succ]
    field_simp [hs.ne']
    dsimp only [b,c]
    ring

theorem freeSymbol_log (ω : ℝ) {t : ℕ} (ha : |ω| * t≤1) :
    coeff t (fairSeries (areaCharacter ω) words) = (exp (freeLog ω t):ℂ) :=
  freeSymbol_log_wide ω (by linarith only [ha])

theorem bridgeSymbol_log {ω : ℝ} (hω : ω≠0) {j : ℕ} (ha : |ω| * (2*j:ℝ)≤1) :
    coeff (2*j) (fairSeries (areaCharacter ω) bridges) =
      ((survival j*exp (bridgeLog ω j):ℝ):ℂ) :=
  bridgeSymbol_log_wide hω (by linarith only [ha])

end CentralUnimodality.ReturnSplit
