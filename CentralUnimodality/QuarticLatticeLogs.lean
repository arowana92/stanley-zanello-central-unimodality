module

public import CentralUnimodality.QuarticLogLosses
public import CentralUnimodality.GaussianLogError

/-! Quartic log expansions with an explicit one-sided sixth-order error
for the free and bridge lattice symbols. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open Real Set

noncomputable def sixthSum (t : ℕ) : ℝ := ∑ k ∈ Finset.range t, ((k:ℝ)+1)^6
noncomputable def freeQuartic (ω : ℝ) (t : ℕ) := ω^4*fourthSum t/12
noncomputable def bridgeQuartic (ω : ℝ) (j : ℕ) := ω^4*(fourthSum (2*j)-2*fourthSum j)/180

private theorem cosLoss_abs (x : ℝ) : cosLoss |x|=cosLoss x := by
  rcases le_total 0 x with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h]; simp [cosLoss]; ring

private theorem sincLoss_abs (x : ℝ) : sincLoss |x|=sincLoss x := by
  rcases le_total 0 x with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h]; simp [sincLoss]; ring

private theorem angle {ω a L : ℝ} (h : |ω| *L≤9/8) (a0 : 0≤a) (aL : a≤L) :
    |ω*a|∈Icc 0 (9/8) := ⟨abs_nonneg _,by rw [abs_mul,abs_of_nonneg a0]; exact
      (mul_le_mul_of_nonneg_left aL (abs_nonneg _)).trans h⟩

theorem free_quartic_log (ω : ℝ) {t : ℕ} (ha : |ω| *t≤9/8) :
    0≤ -freeLog ω t-freeExponent ω t-freeQuartic ω t ∧
    -freeLog ω t-freeExponent ω t-freeQuartic ω t≤(1/20)*ω^6*sixthSum t := by
  induction t with
  | zero => simp [freeLog,freeExponent,freeQuartic,fourthSum,sixthSum]
  | succ t ih =>
    let x := ω*((t:ℝ)+1)
    push_cast at ha
    have prev := ih (by nlinarith only [ha,abs_nonneg ω])
    have hx : |x|∈Icc 0 (9/8) := angle ha (by positivity) le_rfl
    have low := cosLoss_control.1 (show (0:ℝ)∈Icc 0 (9/8) by norm_num) hx hx.1
    have up := cosLoss_control.2 _ hx
    rw [cosLoss_abs] at low up
    rw [← abs_pow,abs_of_nonneg (by positivity : 0≤x^6)] at up
    have inc : -freeLog ω (t+1)-freeExponent ω (t+1)-freeQuartic ω (t+1)=
        (-freeLog ω t-freeExponent ω t-freeQuartic ω t)+cosLoss x := by
      simp only [freeLog,freeExponent,freeQuartic,fourthSum,cosLoss,x,Finset.sum_range_succ,Nat.cast_succ]
      ring
    rw [inc]
    rw [sixthSum,Finset.sum_range_succ,← sixthSum]
    have l : 0≤cosLoss x := by simpa [cosLoss] using low
    refine ⟨add_nonneg prev.1 l,?_⟩
    apply (add_le_add prev.2 up).trans_eq
    dsimp only [x]; ring

private theorem double_log {x : ℝ} (h : |x|≤9/8) :
    log (cos x)=log (sinc (2*x))-log (sinc x) := by
  have eq : sinc (2*x)=sinc x*cos x := by
    by_cases hz : x=0
    · subst x; simp
    · rw [sinc_of_ne_zero (mul_ne_zero (by norm_num) hz),sinc_of_ne_zero hz,sin_two_mul]; field_simp
  rw [eq,log_mul (sinc_pos_nine_eighths h).ne' (cos_pos_nine_eighths h).ne']; ring

theorem bridge_quartic_log (ω : ℝ) {j : ℕ} (ha : |ω| *(2*j)≤9/8) :
    0≤ -bridgeLog ω j-bridgeExponent ω j-bridgeQuartic ω j ∧
    -bridgeLog ω j-bridgeExponent ω j-bridgeQuartic ω j≤(1/1000)*ω^6*sixthSum (2*j) := by
  induction j with
  | zero => simp [bridgeLog,bridgeExponent,bridgeQuartic,fourthSum,sixthSum]
  | succ j ih =>
    let b := ω*((j:ℝ)+1)
    let c := ω*(2*(j:ℝ)+1)
    push_cast at ha
    have j0 := Nat.cast_nonneg (α:=ℝ) j
    have prev := ih ((mul_le_mul_of_nonneg_left (show 2*(j:ℝ)≤2*(j+1) by linarith) (abs_nonneg _)).trans ha)
    have hb : |b|∈Icc 0 (9/8) := angle ha (by positivity) (by linarith only [j0])
    have hc : |c|∈Icc 0 (9/8) := angle ha (by positivity) (by linarith)
    have hh : |2*b|∈Icc 0 (9/8) := by rw [show 2*b=ω*(2*(j+1:ℝ)) by dsimp [b]; ring]; exact angle ha (by positivity) le_rfl
    have bc : |b|≤|c| := by
      dsimp [b,c]; rw [abs_mul,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤j+1),abs_of_nonneg (by positivity : (0:ℝ)≤2*j+1)]
      exact mul_le_mul_of_nonneg_left (by linarith only [j0]) (abs_nonneg _)
    have bh : |b|≤|2*b| := by rw [abs_mul (2:ℝ) b,abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith only [abs_nonneg b]
    have m := sincLoss_control.1
    have norm0 := m (show (0:ℝ)∈Icc 0 (9/8) by norm_num) hb hb.1
    have cmp := m hb hc bc
    have cmp' := m hb hh bh
    have up := sincLoss_control.2 _ hc
    have up' := sincLoss_control.2 _ hh
    simp only [sincLoss_abs] at norm0 cmp cmp' up up'
    have l : 0≤sincLoss b := by simpa [sincLoss] using norm0
    rw [← abs_pow,abs_of_nonneg (by positivity : 0≤c^6)] at up
    rw [← abs_pow,abs_of_nonneg (by positivity : 0≤(2*b)^6)] at up'
    have inc : -bridgeLog ω (j+1)-bridgeExponent ω (j+1)-bridgeQuartic ω (j+1)=
        (-bridgeLog ω j-bridgeExponent ω j-bridgeQuartic ω j)+(sincLoss (2*b)+sincLoss c-2*sincLoss b) := by
      rw [bridgeLog,Finset.sum_range_succ,← bridgeLog]
      change -(bridgeLog ω j+(log (cos b)+log (sinc c)-log (sinc b)))-_-_=_
      rw [double_log hb.2]
      simp only [bridgeExponent,bridgeQuartic,fourthSum,show 2*(j+1)=2*j+1+1 by omega,
        Finset.sum_range_succ,Nat.cast_succ,Nat.cast_mul,sincLoss,b,c]
      ring
    rw [inc]
    refine ⟨by linarith only [prev.1,cmp,cmp'],?_⟩
    apply (add_le_add prev.2 (show sincLoss (2*b)+sincLoss c-2*sincLoss b≤
      (1/1000)*(2*b)^6+(1/1000)*c^6 by linarith only [l,up,up'])).trans_eq
    simp only [sixthSum,show 2*(j+1)=2*j+1+1 by omega,Finset.sum_range_succ,Nat.cast_succ,
      Nat.cast_mul,b,c]; ring

end CentralUnimodality.ReturnSplit
