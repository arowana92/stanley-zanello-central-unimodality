module

public import CentralUnimodality.SexticLatticeLogs
public import CentralUnimodality.QuadraticSymbolTransfer

/-! Coefficients and signed cubic errors for the free and bridge logarithms
in the time step τ. The formulas apply to both free parities, including time zero. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit

noncomputable def freeSecondLog (σ : ℕ) (v : ℝ) :=
  (12*σ+1:ℝ)*v/192+(2*σ+1:ℝ)*v^4/1536+v^7/80640

noncomputable def bridgeSecondLog (v : ℝ) := 7*v^4/184320+v^7/5160960

noncomputable def freeThirdLogBound (v τ : ℝ) :=
  1/64+(104*v^3/3+24*τ*v^2+8*τ^2*v+τ^3)/12288+
    (v+τ)^6/11520+(v+τ)^9/(18432*70)

noncomputable def bridgeThirdLogBound (v τ : ℝ) :=
  2*v^3/(180*32^2)+(v+τ)^6/(512*2835)+(v+τ)^9/(18432*32000)

private theorem sixth_sum_exact (n : ℕ) : sixthSum n=
    n*(n+1:ℝ)*(2*n+1)*(3*(n:ℝ)^4+6*(n:ℝ)^3-3*n+1)/42 := by
  induction n with
  | zero => simp [sixthSum]
  | succ n ih =>
    rw [sixthSum,Finset.sum_range_succ,← sixthSum,ih,Nat.cast_succ]
    ring

private theorem eighth_power_bound (n : ℕ) : eighthSum n≤((n:ℝ)+1)^9/9 := by
  induction n with
  | zero => norm_num [eighthSum]
  | succ n ih =>
    rw [eighthSum,Finset.sum_range_succ,← eighthSum,Nat.cast_succ]
    have h : 0≤((n:ℝ)+1+1)^9/9-((n:ℝ)+1)^9/9-((n:ℝ)+1)^8 := by ring_nf; positivity
    linarith only [ih,h]

private theorem eighth_scaled {ω τ : ℝ} {j t : ℕ} (ht : t≤2*j+1)
    (hω : ω^2=τ^3/32) : ω^8*eighthSum t≤τ^3*((j:ℝ)*τ+τ)^9/18432 := by
  have lim : (t:ℝ)+1≤2*j+2 := by exact_mod_cast (show t+1≤2*j+2 by omega)
  have h := pow_le_pow_left₀ (by positivity) lim 9
  have upper : eighthSum t≤(2*(j:ℝ)+2)^9/9 := by linarith only [eighth_power_bound t,h]
  have h8 : ω^8=(τ^3/32)^4 := by rw [← hω]; ring
  rw [h8]
  apply (mul_le_mul_of_nonneg_left upper (by positivity : 0≤(τ^3/32)^4)).trans_eq
  ring

set_option maxHeartbeats 3000000 in
theorem free_log_second_scaled {ω τ : ℝ} {j σ : ℕ} (hs : σ≤1) (hτ : 0≤τ)
    (hω : ω^2=τ^3/32) (ha : |ω| *(2*j+σ)≤9/8) (v : ℝ) (hv : v=j*τ) :
    let d := -freeLog ω (2*j+σ)-v^3/24-τ*freeLogCorrection σ v-τ^2*freeSecondLog σ v
    0≤d ∧ d≤τ^3*freeThirdLogBound v τ := by
  have H := free_sextic_log ω (t:=2*j+σ) (by push_cast; exact ha)
  dsimp only at H ⊢
  have E := eighth_scaled (j:=j) (t:=2*j+σ) (by omega) hω
  rw [← hv] at E
  let p := freeExponent ω (2*j+σ)+freeQuartic ω (2*j+σ)+ω^6*sixthSum (2*j+σ)/45-
    (v^3/24+τ*freeLogCorrection σ v+τ^2*freeSecondLog σ v)
  have h4 : ω^4=(τ^3/32)^2 := by rw [← hω]; ring
  have h6 : ω^6=(τ^3/32)^3 := by rw [← hω]; ring
  have poly : 0≤p ∧ p≤τ^3*(freeThirdLogBound v τ-(v+τ)^9/(18432*70)) := by
    dsimp only [p,freeExponent,freeQuartic,freeLogCorrection,freeSecondLog,freeThirdLogBound]
    simp only [fourthSum_closed,sixth_sum_exact,h4,h6,hω,hv,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    interval_cases σ <;> cases j <;> push_cast <;> constructor
      <;> (apply sub_nonneg.mp; ring_nf; positivity)
  dsimp only [p] at poly
  constructor <;> linarith only [H.1,H.2,poly.1,poly.2,E]

set_option maxHeartbeats 3000000 in
theorem bridge_log_second_scaled {ω τ : ℝ} {j : ℕ} (hτ : 0≤τ)
    (hω : ω^2=τ^3/32) (ha : |ω| *(2*j)≤9/8) (v : ℝ) (hv : v=j*τ) :
    let d := -bridgeLog ω j-v^3/96-τ*bridgeLogCorrection v-τ^2*bridgeSecondLog v
    0≤d ∧ d≤τ^3*bridgeThirdLogBound v τ := by
  have H := bridge_sextic_log ω (j:=j) (by push_cast; exact ha)
  dsimp only at H ⊢
  have E := eighth_scaled (j:=j) (t:=2*j) (by omega) hω
  rw [← hv] at E
  let p := bridgeExponent ω j+bridgeQuartic ω j+ω^6*(sixthSum (2*j)-2*sixthSum j)/2835-
    (v^3/96+τ*bridgeLogCorrection v+τ^2*bridgeSecondLog v)
  have h4 : ω^4=(τ^3/32)^2 := by rw [← hω]; ring
  have h6 : ω^6=(τ^3/32)^3 := by rw [← hω]; ring
  have poly : 0≤p ∧ p≤τ^3*(bridgeThirdLogBound v τ-(v+τ)^9/(18432*32000)) := by
    dsimp only [p,bridgeExponent,bridgeQuartic,bridgeLogCorrection,bridgeSecondLog,bridgeThirdLogBound]
    simp only [fourthSum_closed,sixth_sum_exact,h4,h6,hω,hv,Nat.cast_mul,Nat.cast_ofNat]
    cases j <;> push_cast <;> constructor
      <;> (apply sub_nonneg.mp; ring_nf; positivity)
  dsimp only [p] at poly
  constructor <;> linarith only [H.1,H.2,poly.1,poly.2,E]

open PowerSeries Real

theorem free_quadratic_symbol {ω τ : ℝ} {j σ : ℕ} (hs : σ≤1) (hτ : 0≤τ)
    (hω : ω^2=τ^3/32) (ha : |ω| *(2*j+σ)≤9/8) (v : ℝ) (hv : v=j*τ) :
    let A := freeLogCorrection σ v
    let B := freeSecondLog σ v
    ‖coeff (2*j+σ) (fairSeries (areaCharacter ω) words)-
      (freeCurve v*(1-τ*A+τ^2*(A^2/2-B)):ℝ)‖≤
      τ^3*freeCurve v*(freeThirdLogBound v τ+A^3/6+A*B+τ*B^2/2) := by
  dsimp only
  rw [freeSymbol_log_wide ω (by push_cast; exact ha),← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have h := free_log_second_scaled hs hτ hω ha v hv
  exact exponential_transfer_second hτ (by rw [hv]; unfold freeLogCorrection; positivity)
    (by rw [hv]; unfold freeSecondLog; positivity) h.1 h.2

theorem bridge_quadratic_symbol {ω τ : ℝ} {j : ℕ} (hτ : 0≤τ)
    (hω : ω^2=τ^3/32) (ha : |ω| *(2*j)≤9/8) (v : ℝ) (hv : v=j*τ) :
    let A := bridgeLogCorrection v
    let B := bridgeSecondLog v
    ‖coeff (2*j) (fairSeries (areaCharacter ω) bridges)/(survival j:ℂ)-
      (bridgeCurve v*(1-τ*A+τ^2*(A^2/2-B)):ℝ)‖≤
      τ^3*bridgeCurve v*(bridgeThirdLogBound v τ+A^3/6+A*B+τ*B^2/2) := by
  have raw : coeff (2*j) (fairSeries (areaCharacter ω) bridges) =
      ((survival j*exp (bridgeLog ω j):ℝ):ℂ) := by
    by_cases hz : ω=0
    · subst ω; simp [fair_bridge_zero_frequency,bridgeLog]
    · exact bridgeSymbol_log_wide hz ha
  dsimp only
  rw [raw,Complex.ofReal_mul,mul_div_cancel_left₀ _ (by exact_mod_cast (survival_pos j).ne' : (survival j:ℂ)≠0),
    ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have h := bridge_log_second_scaled hτ hω ha v hv
  exact exponential_transfer_second hτ (by rw [hv]; unfold bridgeLogCorrection; positivity)
    (by rw [hv]; unfold bridgeSecondLog; positivity) h.1 h.2

end CentralUnimodality.ReturnSplit
