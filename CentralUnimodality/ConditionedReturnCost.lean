module

public import CentralUnimodality.DiscountedInverse

/-! Conditioning the inverse last-return law with a separate cost at
each time. A uniform first residual and a time-dependent second
remainder enter with different weights. -/
@[expose] public section

namespace CentralUnimodality
open Real PowerSeries

noncomputable def conditionedCost (N : ℕ) (K : ℕ → ℝ) :=
  (K N+∑ j ∈ Finset.range (N+1), returnMass j*K (N-j))/survival N

private theorem inverse_cost {ω τ e : ℝ} {N : ℕ} (hN : 0<N) (ht : 0≤τ) (he : 0≤e)
    (E G : ℕ → ℂ) (K D : ℕ → ℝ)
    (endpt : D N=1) (unit : ∀ j≤N, D j≤1)
    (symbol : ∀ j≤N, ‖returnSymbol ω j‖≤returnMass j*D (N-j))
    (h : ∀ j≤N, ‖E j-G j‖≤τ*e+τ^2*K j) :
    ‖inverseAt ω N E-inverseAt ω N G‖/survival N≤4*sqrt N*τ*e+τ^2*conditionedCost N (fun j => D j*K j) := by
  let P := fun j => D j*K j
  let r := survival N
  have r0 := survival_pos N
  have err := inverseAt_discounted_error (ω:=ω) N E G K D (mul_nonneg ht he) endpt unit symbol h
  change _≤τ*e+τ^2*P N+∑ j ∈ Finset.range (N+1), returnMass j*(τ*e+τ^2*P (N-j)) at err
  have split : (∑ j ∈ Finset.range (N+1), returnMass j*(τ*e+τ^2*P (N-j)))=
      (1-r)*(τ*e)+τ^2*(∑ j ∈ Finset.range (N+1), returnMass j*P (N-j)) := by
    rw [← returnMass_sum]
    rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [split] at err
  apply (div_le_div_of_nonneg_right err r0.le).trans
  have lin : (2-r)*(τ*e)/r≤4*sqrt N*τ*e := calc
    _ ≤ (2*(τ*e))/r := div_le_div_of_nonneg_right (by nlinarith only [mul_nonneg r0.le (mul_nonneg ht he)]) r0.le
    _ = 2*(τ*e)*r⁻¹ := div_eq_mul_inv ..
    _ ≤ 2*(τ*e)*(2*sqrt N) := mul_le_mul_of_nonneg_left (survival_inv_le hN) (by positivity)
    _ = _ := by ring
  calc
    _ = (2-r)*(τ*e)/r+τ^2*conditionedCost N P := by unfold conditionedCost; dsimp only [r]; ring
    _ ≤ _ := add_le_add lin le_rfl

theorem amplitude_of_weighted_costs {n δ : ℕ} (hs : δ≤1) (hn : 0<n+δ)
    (θ : ℝ) (V : PowerSeries ℂ) (G : ℕ → ℂ) (K D : ℕ → ℝ) {ξ e b τ c : ℝ}
    (ht : 0≤τ) (hc : 0≤c) (freq : |θ| *(n+δ:ℕ)*sqrt (n+δ:ℕ)≤ξ)
    (val : ‖G (n+δ)‖≤e)
    (lip : ∀ j≤n+δ, ‖G (n+δ)-G (n+δ-j)‖≤j*(b/(n+δ:ℕ)))
    (endpt : D (n+δ)=1) (unit : ∀ j≤n+δ, D j≤1)
    (symbol : ∀ j≤n+δ, ‖returnSymbol (θ/2) j‖≤returnMass j*D (n+δ-j))
    (cost : ∀ j≤n+δ, ‖parityResidual (θ/2) V (1-δ) j-G j‖≤τ*c+τ^2*K j) :
    |signedAmplitude n δ θ-residualAmplitude (2*n+δ) V|≤(1+ξ/2)*e+b+
      4*sqrt (n+δ:ℕ)*τ*c+τ^2*conditionedCost (n+δ) (fun j => D j*K j) := by
  let N := n+δ
  let r := survival N
  let E := parityResidual (θ/2) V (1-δ)
  have hr : 0<r := survival_pos _
  have np : (0:ℝ)<N := by exact_mod_cast hn
  have hlen : 2*n+δ+1=2*N+(1-δ) := by dsimp only [N]; omega
  have hh : (2*n+δ+1)/2=N := by dsimp only [N]; omega
  have inv := inverse_cost (ω:=θ/2) hn ht hc E G K D endpt unit symbol cost
  have smooth := inverse_smooth_bound (θ/2) N G lip
  have factor : 0≤r+N*(|θ/2|/2) := by positivity
  have sm := smooth.trans (add_le_add (mul_le_mul_of_nonneg_left val factor) le_rfl)
  have hscale : (N:ℝ)*(|θ/2|/2)/r≤ξ/2 := by
    have h := mul_le_mul_of_nonneg_left (survival_inv_le hn) (show 0≤(N:ℝ)*(|θ|/4) by positivity)
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),div_eq_mul_inv]
    dsimp only [N,r] at *; linarith only [h,freq]
  have vv : (r+N*(|θ/2|/2))*e/r ≤ (1+ξ/2)*e := by
    rw [show (r+N*(|θ/2|/2))*e/r=(1+N*(|θ/2|/2)/r)*e by field_simp]
    exact mul_le_mul_of_nonneg_right (add_le_add le_rfl hscale) ((norm_nonneg _).trans val)
  have model : ‖inverseAt (θ/2) N G‖/r≤(1+ξ/2)*e+b := by
    apply (div_le_div_of_nonneg_right sm hr.le).trans
    rw [add_div,show (N*r)*(b/N)/r=b by field_simp]
    exact add_le_add vv le_rfl
  rw [signedAmplitude,residualAmplitude,← sub_div,abs_div,hh,abs_of_pos hr,hlen,← Complex.sub_re]
  apply (div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) hr.le).trans
  rw [← map_sub,strict_error_eq_inverseAt _ _ _ _ (by omega)]
  have tri := norm_add_le (inverseAt (θ/2) N E-inverseAt (θ/2) N G) (inverseAt (θ/2) N G)
  rw [sub_add_cancel] at tri
  apply (div_le_div_of_nonneg_right tri hr.le).trans
  rw [add_div]
  dsimp only [E,N,r] at *; linarith only [inv,model]

theorem amplitude_of_local_costs {n δ : ℕ} (hs : δ≤1) (hn : 0<n+δ)
    (θ : ℝ) (V : PowerSeries ℂ) (G : ℕ → ℂ) (K : ℕ → ℝ) {ξ e b τ c : ℝ}
    (ht : 0≤τ) (hc : 0≤c) (freq : |θ| *(n+δ:ℕ)*sqrt (n+δ:ℕ)≤ξ)
    (val : ‖G (n+δ)‖≤e)
    (lip : ∀ j≤n+δ, ‖G (n+δ)-G (n+δ-j)‖≤j*(b/(n+δ:ℕ)))
    (cost : ∀ j≤n+δ, ‖parityResidual (θ/2) V (1-δ) j-G j‖≤τ*c+τ^2*K j) :
    |signedAmplitude n δ θ-residualAmplitude (2*n+δ) V|≤(1+ξ/2)*e+b+
      4*sqrt (n+δ:ℕ)*τ*c+τ^2*conditionedCost (n+δ) K := by
  simpa only [one_mul] using amplitude_of_weighted_costs hs hn θ V G K (fun _ => 1) ht hc freq val lip
    rfl (fun _ _ => le_rfl) (fun j _ => by simpa using norm_returnSymbol_le (θ/2) j) cost

end CentralUnimodality
