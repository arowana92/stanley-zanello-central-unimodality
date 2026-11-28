module

public import CentralUnimodality.LogarithmicSymbols

/-! Gaussian exponents and explicit fourth-order errors for the two
characteristic functions that enter the last-return convolution. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open Real PowerSeries

noncomputable def fourthSum (t : ℕ) : ℝ := ∑ k ∈ Finset.range t, ((k:ℝ)+1)^4

theorem fourthSum_closed (t : ℕ) :
    fourthSum t = t*(t+1:ℝ)*(2*t+1)*(3*(t:ℝ)^2+3*t-1)/30 := by
  induction t with
  | zero => simp [fourthSum]
  | succ k ih =>
    rw [fourthSum,Finset.sum_range_succ,← fourthSum,ih,Nat.cast_succ]
    ring

noncomputable def freeExponent (ω : ℝ) (t : ℕ) : ℝ :=
  ω^2*t*(t+1:ℝ)*(2*t+1)/12

noncomputable def bridgeExponent (ω : ℝ) (j : ℕ) : ℝ :=
  ω^2*(j:ℝ)^2*(2*j+1)/6

private theorem weak_angle {ω t x : ℝ} (ha : |ω| *t≤1) (hx : 0≤x) (ht : x≤t) :
    |ω*x|≤1 := by
  rw [abs_mul,abs_of_nonneg hx]
  exact (mul_le_mul_of_nonneg_left ht (abs_nonneg _)).trans ha

theorem freeLog_error (ω : ℝ) {t : ℕ} (ha : |ω| *t≤1) :
    |freeLog ω t+freeExponent ω t| ≤ 3/4*ω^4*fourthSum t := by
  induction t with
  | zero => simp [freeLog,freeExponent,fourthSum]
  | succ t ih =>
    rw [Nat.cast_succ] at ha
    have prev : |ω| *(t:ℝ)≤1 := (mul_le_mul_of_nonneg_left
      (by linarith : (t:ℝ)≤t+1) (abs_nonneg _)).trans ha
    let x := ω*((t:ℝ)+1)
    have addErr := log_cos_quadratic (weak_angle ha (by positivity) le_rfl)
    have next : freeExponent ω (t+1)=freeExponent ω t+x^2/2 := by
      simp only [freeExponent,Nat.cast_succ,x]; ring
    rw [freeLog,Finset.sum_range_succ,← freeLog,next,fourthSum,Finset.sum_range_succ,← fourthSum]
    change |(freeLog ω t+log (cos x))+(freeExponent ω t+x^2/2)|≤_
    rw [show (freeLog ω t+log (cos x))+(freeExponent ω t+x^2/2)=
      (freeLog ω t+freeExponent ω t)+(log (cos x)+x^2/2) by ring]
    apply (abs_add_le ..).trans
    apply (add_le_add (ih prev) addErr).trans_eq
    ring

private theorem bridge_increment {b c : ℝ} (hb : |b|≤1) (hc : |c|≤1) :
    |log (cos b)+log (sinc c)-log (sinc b)+(b^2/3+c^2/6)| ≤ 4/5*b^4+c^4/20 := by
  rw [show log (cos b)+log (sinc c)-log (sinc b)+(b^2/3+c^2/6)=
    ((log (cos b)+b^2/2)+(log (sinc c)+c^2/6))-(log (sinc b)+b^2/6) by ring]
  apply (abs_sub ..).trans
  apply (add_le_add_left (abs_add_le (log (cos b)+b^2/2) (log (sinc c)+c^2/6)) _).trans
  linarith only [log_cos_quadratic hb,log_sinc_quadratic hc,log_sinc_quadratic hb]

theorem bridgeLog_error (ω : ℝ) {j : ℕ} (ha : |ω| *(2*j:ℝ)≤1) :
    |bridgeLog ω j+bridgeExponent ω j| ≤ 8/5*ω^4*fourthSum j := by
  induction j with
  | zero => simp [bridgeLog,bridgeExponent,fourthSum]
  | succ j ih =>
    rw [Nat.cast_succ] at ha
    have prev : |ω| *(2*j:ℝ)≤1 := (mul_le_mul_of_nonneg_left
      (by linarith : (2*j:ℝ)≤2*(j+1)) (abs_nonneg _)).trans ha
    let b := ω*((j:ℝ)+1)
    let c := ω*(2*(j:ℝ)+1)
    have hb : |b|≤1 := weak_angle ha (by positivity) (by linarith [Nat.cast_nonneg (α:=ℝ) j])
    have hc : |c|≤1 := weak_angle ha (by positivity) (by linarith)
    have pow4 : (2*(j:ℝ)+1)^4 ≤ (2*((j:ℝ)+1))^4 := by
      gcongr; linarith
    have cost : 4/5*b^4+c^4/20 ≤ 8/5*ω^4*((j:ℝ)+1)^4 := by
      dsimp [b,c]
      nlinarith only [mul_le_mul_of_nonneg_left pow4 (show 0≤ω^4 by positivity)]
    have next : bridgeExponent ω (j+1)=bridgeExponent ω j+(b^2/3+c^2/6) := by
      simp only [bridgeExponent,Nat.cast_succ,b,c]; ring
    rw [bridgeLog,Finset.sum_range_succ,← bridgeLog,next,fourthSum,Finset.sum_range_succ,← fourthSum]
    let inc := log (cos b)+log (sinc c)-log (sinc b)
    change |(bridgeLog ω j+inc)+(bridgeExponent ω j+(b^2/3+c^2/6))|≤_
    rw [show (bridgeLog ω j+inc)+(bridgeExponent ω j+(b^2/3+c^2/6))=
      (bridgeLog ω j+bridgeExponent ω j)+(inc+(b^2/3+c^2/6)) by ring]
    apply (abs_add_le ..).trans
    exact (add_le_add (ih prev) ((bridge_increment hb hc).trans cost)).trans_eq (by ring)

end CentralUnimodality.ReturnSplit
