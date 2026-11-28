module

public import CentralUnimodality.GaussianResidual

/-! Direct finite-size estimates between the actual lattice symbols and
the two elementary cubic exponentials at scaled time. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit

open Real PowerSeries

noncomputable def freeCurve (v : ℝ) : ℝ := exp (-(v^3/24))
noncomputable def bridgeCurve (v : ℝ) : ℝ := exp (-(v^3/96))

noncomputable def inputCost (τ : ℝ) (N : ℕ) : ℝ := τ^3*N^2+τ^6*N^5

theorem inputCost_rescale {N : ℕ} (hN : 0<N) (u : ℝ) :
    inputCost (u/N) N=(u^3+u^6)/N := by
  unfold inputCost
  field_simp [(Nat.cast_pos.mpr hN : (0:ℝ)<N).ne']

theorem fourthSum_le_fifth (t : ℕ) : fourthSum t≤(t:ℝ)^5 := by
  calc
    _ ≤ ∑ _k ∈ Finset.range t, (t:ℝ)^4 := by
      apply Finset.sum_le_sum
      intro k hk
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Finset.mem_range.mp hk) _
    _ = _ := by simp; ring

private theorem free_exponent_error {N j σ : ℕ} (hN : 0<N) (hj : j≤N) (hs : σ≤1)
    {τ ω : ℝ} (hτ : 0≤τ) (hw : ω^2=τ^3/32) :
    |freeExponent ω (2*j+σ)-(τ*j)^3/24| ≤ τ^3*N^2 := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hJ : (j:ℝ)≤N := by exact_mod_cast hj
  have h₂ := pow_le_pow_left₀ (by positivity : 0≤(j:ℝ)) hJ 2
  have hq : (N:ℝ)≤(N:ℝ)^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hn) (by positivity : 0≤(N:ℝ))]
  rcases (by omega : σ=0 ∨ σ=1) with rfl|rfl
  · have eq : freeExponent ω (2*j+0)-(τ*j)^3/24=τ^3*((12*j^2+2*j)/384) := by
      simp [freeExponent,hw]; ring
    rw [eq,abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (by nlinarith only [h₂,hJ,hq]) (by positivity)
  · have eq : freeExponent ω (2*j+1)-(τ*j)^3/24=τ^3*((36*j^2+26*j+6)/384) := by
      simp [freeExponent,hw]; ring
    rw [eq,abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (by nlinarith only [h₂,hJ,hq,hn]) (by positivity)

private theorem bridge_exponent_error {N j : ℕ} (hj : j≤N) {τ ω : ℝ}
    (hτ : 0≤τ) (hw : ω^2=τ^3/32) :
    |bridgeExponent ω j-(τ*j)^3/96| ≤ τ^3*N^2 := by
  have eq : bridgeExponent ω j-(τ*j)^3/96=τ^3*((j:ℝ)^2/192) := by rw [bridgeExponent,hw]; ring
  rw [eq,abs_of_nonneg (by positivity)]
  have hm := pow_le_pow_left₀ (by positivity : 0≤(j:ℝ)) (show (j:ℝ)≤N by exact_mod_cast hj) 2
  exact mul_le_mul_of_nonneg_left (by nlinarith only [hm,sq_nonneg (j:ℝ)]) (by positivity)

private theorem fourth_angle {ω τ : ℝ} (hw : ω^2=τ^3/32) : ω^4=τ^6/1024 := by
  rw [show ω^4=(ω^2)^2 by ring,hw]; ring

theorem free_curve_bound {N j σ : ℕ} (hN : 0<N) (hj : j≤N) (hs : σ≤1)
    {τ ω : ℝ} (hτ : 0≤τ) (hw : ω^2=τ^3/32) (ha : |ω| * (2*N+1:ℕ)≤1) :
    ‖freeSymbol ω σ j-(freeCurve (τ*j):ℂ)‖ ≤ inputCost τ N := by
  let t := 2*j+σ
  have ht : (t:ℝ)≤(2*N+1:ℕ) := by exact_mod_cast (show t≤2*N+1 by dsimp [t]; omega)
  have ht' : (t:ℝ)≤3*(N:ℝ) := by exact_mod_cast (show t≤3*N by dsimp [t]; omega)
  have gauss := free_gaussian ((mul_le_mul_of_nonneg_left ht (abs_nonneg ω)).trans ha)
  have quart := (fourthSum_le_fifth t).trans (pow_le_pow_left₀ (by positivity) ht' 5)
  have err := mul_le_mul_of_nonneg_left quart (by positivity : 0≤3/4*ω^4)
  rw [fourth_angle hw] at err gauss
  have close : |exp (-freeExponent ω t)-freeCurve (τ*j)|≤τ^3*N^2 := by
    unfold freeCurve
    apply (exp_dist_nonpos (x := -freeExponent ω t) (y := -((τ*j)^3/24))
      (neg_nonpos.mpr (by unfold freeExponent; positivity)) (neg_nonpos.mpr (by positivity))).trans
    rw [neg_sub_neg,abs_sub_comm]
    exact free_exponent_error hN hj hs hτ hw
  have add := norm_add_le (freeSymbol ω σ j-(exp (-freeExponent ω t):ℂ))
    ((exp (-freeExponent ω t):ℂ)-(freeCurve (τ*j):ℂ))
  rw [sub_add_sub_cancel,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at add
  apply add.trans
  change ‖(coeff t) (fairSeries (areaCharacter ω) words)-_‖+_≤_
  unfold inputCost
  nlinarith only [gauss,close,err,mul_nonneg (by positivity : 0≤τ^6) (by positivity : 0≤(N:ℝ)^5)]

theorem bridge_curve_bound {N j : ℕ} (hj : j≤N) {τ ω : ℝ}
    (hτ : 0≤τ) (hw : ω^2=τ^3/32) (ha : |ω| * (2*N+1:ℕ)≤1) :
    ‖coeff (2*j) (fairSeries (areaCharacter ω) bridges)/(survival j:ℂ)-
      (bridgeCurve (τ*j):ℂ)‖ ≤ inputCost τ N := by
  have ht : (2*(j:ℝ))≤(2*N+1:ℕ) := by exact_mod_cast (by omega : 2*j≤2*N+1)
  have gauss := bridge_gaussian ((mul_le_mul_of_nonneg_left ht (abs_nonneg ω)).trans ha)
  have quart := (fourthSum_le_fifth j).trans (pow_le_pow_left₀ (by positivity)
    (show (j:ℝ)≤N by exact_mod_cast hj) 5)
  have err := mul_le_mul_of_nonneg_left quart (by positivity : 0≤8/5*ω^4)
  rw [fourth_angle hw] at err gauss
  have close : |exp (-bridgeExponent ω j)-bridgeCurve (τ*j)|≤τ^3*N^2 := by
    unfold bridgeCurve
    apply (exp_dist_nonpos (x := -bridgeExponent ω j) (y := -((τ*j)^3/96))
      (neg_nonpos.mpr (by unfold bridgeExponent; positivity)) (neg_nonpos.mpr (by positivity))).trans
    rw [neg_sub_neg,abs_sub_comm]
    exact bridge_exponent_error hj hτ hw
  have add := norm_add_le (coeff (2*j) (fairSeries (areaCharacter ω) bridges)/(survival j:ℂ)-
    (exp (-bridgeExponent ω j):ℂ)) ((exp (-bridgeExponent ω j):ℂ)-(bridgeCurve (τ*j):ℂ))
  rw [sub_add_sub_cancel,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at add
  apply add.trans
  unfold inputCost
  nlinarith only [gauss,close,err,mul_nonneg (by positivity : 0≤τ^6) (by positivity : 0≤(N:ℝ)^5)]

end CentralUnimodality.ReturnSplit
