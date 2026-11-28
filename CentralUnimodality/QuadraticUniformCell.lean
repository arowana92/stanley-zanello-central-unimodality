module

public import CentralUnimodality.UniformCellAmplitude
public import CentralUnimodality.QuadraticScaledPrices
public import CentralUnimodality.QuadraticLocalPrices
public import CentralUnimodality.CubicResidualEstimate

/-! Combine the two conditioned residuals at frequency scale, including the
endpoint parity correction. The remaining inputs are finite cell data. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open ReturnSplit Real Set Witness

set_option maxRecDepth 12000

theorem quadratic_uniform_cell {n δ i : ℕ} (hs : δ≤1) (hn : 10000≤n+δ) (hi : i<288)
    (second : ∀ {σ k : ℕ}, σ≤1 → k<228 → ∀ {v : ℝ}, v∈halfInterval k →
      |secondCurveResidual (value candidate) (correctedValue σ) σ v|≤(secondUnits k:ℝ)/10^30)
    (inputs : ∀ {k : ℕ}, k<228 → (cubeInput k).Sound k)
    (maxima : ∀ {k : ℕ}, k<228 → cubicMaxData[k]?=some (cubicMaxRow k))
    {ξ : ℝ} (cell : ξ∈Icc (frequencyEdge i) (frequencyEdge (i+1))) :
    |signedAmplitude n δ (ξ/cellScale (n+δ))-spectralTrial ξ|≤(quadraticFrequencyAllowance i:ℝ) := by
  let N := n+δ
  let u := |ξ|^(2/3:ℝ)
  let τ := u/(N:ℝ)
  let H : ℝ := (topTime i:ℝ)
  let t := H/10000
  let bin := fun j : ℕ => cappedBin i ((j:ℝ)*τ)
  have nn : 0≤ξ := (show 0≤frequencyEdge i by unfold frequencyEdge; positivity).trans cell.1
  have band : |ξ|≤1728 := by
    rw [abs_of_nonneg nn,← retained_endpoint]
    exact cell.2.trans (frequency_edge_mono (by omega))
  have hu : u∈halfInterval i := frequency_cell_time cell
  have u0 : 0≤u := rpow_nonneg (abs_nonneg _) _
  have uh : u≤H := by dsimp only [H]; rw [top_time]; exact_mod_cast hu.2
  have xh : |ξ|≤(topFrequency i:ℝ) := by rw [abs_of_nonneg nn]; exact cell.2.trans (top_frequency i)
  by_cases outside : 228≤ i
  · simpa only [quadraticFrequencyAllowance,ite_eq_right (Nat.not_lt.mpr outside)] using outer_cell_amplitude hs (by omega) outside nn band hu
  have inside : i<228 := by omega
  have t0 : 0≤τ := div_nonneg u0 (Nat.cast_nonneg _)
  have pos : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (by dsimp [N]; omega)
  have endpoint : (N:ℝ)*τ=u := by dsimp only [τ]; field_simp
  have ve : u≤((i:ℝ)+1)/2 := by exact_mod_cast hu.2
  have top : (N:ℝ)*τ≤114 := by
    rw [endpoint]; have ir : (i:ℝ)≤227 := by exact_mod_cast (by omega : i≤227)
    linarith only [ve,ir]
  have mem (j : ℕ) (hj : j≤N) : (j:ℝ)*τ∈halfInterval (bin j) := by
    have bound := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj : (j:ℝ)≤N) t0
    rw [endpoint] at bound
    exact mem_capped_bin (mul_nonneg (Nat.cast_nonneg _) t0) (by linarith only [bound,ve])
  have idx (j : ℕ) : bin j<228 := (min_le_left ..).trans_lt inside
  have sign : 1-δ≤1 := by omega
  have phase := (peak_frequency_scale (N:=N) (by dsimp [N]; omega) band).2
  let A := fun j => (unitPrice secondPrice (bin j):ℝ)
  let B := fun j => (unitPrice cubicPrice (bin j):ℝ)
  have amp := quadratic_amplitude_of_costs hs hn inside band hu A B
    (fun j hj => by
      change _≤(unitPrice secondPrice (bin j):ℝ)
      simp only [unitPrice,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat,(local_quadratic_prices (idx j)).1]
      exact second sign (idx j) (mem j hj))
    (fun j hj => by
      change _≤τ^3*(unitPrice cubicPrice (bin j):ℝ)
      simp only [unitPrice,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat,(local_quadratic_prices (idx j)).2.1]
      exact cubic_residual_of_inputs sign hj hn t0 phase top rfl (mem j hj)
        (fun _ hk => inputs (hk.trans_lt (idx j))) (maxima (idx j)))
  have ⟨step,first⟩ := quadratic_scaled_steps hn u0 uh
  have inv2 := scaled_inverse_price secondPrice 1 hn hu u0 uh
  have inv3 := scaled_inverse_price cubicPrice 2 hn hu u0 uh
  have gj := (inputs inside).signed sign (by decide : 0<5) hu
  rw [iteratedDeriv_zero,← (local_quadratic_prices inside).2.2] at gj
  have product := mul_le_mul step gj (abs_nonneg _) (div_nonneg (u0.trans uh) (by norm_num))
  apply amp.trans
  change (1+|ξ|/2)*(15/10^16)+(36/10^14)*u+4*sqrt N*τ*(3/10^12)+
    τ^2*conditionedCost N (pricedResidual secondPrice i N u)+τ^3*conditionedCost N (pricedResidual cubicPrice i N u)+
    τ*|correctedValue (1-δ) u|≤_
  have price : (quadraticFrequencyAllowance i:ℝ)=(1+(topFrequency i:ℝ)/2)*(15/10^16)+(36/10^14)*H+
      400*t*(3/10^12)+t^2*(inverseQuote secondPrice i:ℝ)+t^3*(inverseQuote cubicPrice i:ℝ)+t*(signedPrice i:ℝ)/10^30 := by
    simp only [quadraticFrequencyAllowance,ite_eq_left inside,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,
      Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_one]
    rfl
  rw [price]
  change sqrt N*τ≤100*t at first
  change τ*|correctedValue (1-δ) u|≤t*((signedPrice i:ℝ)/10^30) at product
  change τ^2*conditionedCost N (pricedResidual secondPrice i N u)≤t^2*(inverseQuote secondPrice i:ℝ) at inv2
  change τ^3*conditionedCost N (pricedResidual cubicPrice i N u)≤t^3*(inverseQuote cubicPrice i:ℝ) at inv3
  linarith only [xh,uh,first,inv2,inv3,product]

end CentralUnimodality.PolynomialTrial
