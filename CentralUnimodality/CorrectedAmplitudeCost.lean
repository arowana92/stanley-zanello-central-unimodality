module

public import CentralUnimodality.ConditionedReturnCost
public import CentralUnimodality.FirstResidualTransfer
public import CentralUnimodality.CertifiedCurveResidual

/-! Transfer the signed first residual and local second-order costs to
the actual conditional amplitude at each retained frequency. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Real Set ReturnSplit Witness

noncomputable def correctedSeries (σ : ℕ) (τ : ℝ) :=
  trialSeries (fun j => value candidate ((j:ℝ)*τ)+τ*correctedValue σ ((j:ℝ)*τ))

theorem corrected_amplitude_of_costs {n δ : ℕ} (hs : δ≤1) (hn : 300000≤n+δ) {ξ : ℝ}
    (hξ : |ξ|≤1728) (K : ℕ → ℝ)
    (first : ∀ v∈Icc (0:ℝ) 144, |firstCurveResidual (value candidate) (correctedValue (1-δ)) (1-δ) v|≤3/10^12)
    (cost : ∀ j≤n+δ, let τ := |ξ|^(2/3:ℝ)/(n+δ:ℕ); let v := (j:ℝ)*τ
      ‖parityResidual (ξ/cellScale (n+δ)/2) (correctedSeries (1-δ) τ) (1-δ) j-
        ((curveResidual (value candidate) v+τ*firstCurveResidual (value candidate) (correctedValue (1-δ)) (1-δ) v:ℝ):ℂ)‖
        ≤τ^2*K j) :
    let u := |ξ|^(2/3:ℝ)
    let τ := u/(n+δ:ℕ)
    |signedAmplitude n δ (ξ/cellScale (n+δ))-value candidate u|≤
      (1+|ξ|/2)*(15/10^16)+(36/10^14)*u+4*sqrt (n+δ:ℕ)*τ*(3/10^12)+
      τ^2*conditionedCost (n+δ) K+τ*|correctedValue (1-δ) u| := by
  let N := n+δ
  let σ := 1-δ
  let S := cellScale N
  let u := |ξ|^(2/3:ℝ)
  let τ := u/(N:ℝ)
  let E := fun j : ℕ => (curveResidual (value candidate) ((j:ℝ)*τ):ℂ)
  let V := correctedSeries σ τ
  obtain ⟨hu,ht,_,_⟩ := retained_scaling hn hξ
  have N0 : 0<N := by dsimp only [N]; omega
  have np : (0:ℝ)<N := by exact_mod_cast N0
  have sp : 0<S := cellScale_pos N0
  have endpoint : (N:ℝ)*τ=u := by dsimp only [τ]; field_simp
  have step (j : ℕ) (hj : j≤N) : (j:ℝ)*τ∈Icc (0:ℝ) 144 :=
    ⟨mul_nonneg (Nat.cast_nonneg _) ht,((mul_le_mul_of_nonneg_right (by exact_mod_cast hj : (j:ℝ)≤N) ht).trans_eq endpoint).trans hu.2⟩
  have big {v : ℝ} (hv : v∈Icc (0:ℝ) 144) : v∈Icc (0:ℝ) 256 := ⟨hv.1,by linarith only [hv.2]⟩
  have freq : |ξ/S| *(N:ℝ)*sqrt N≤|ξ| := by
    have compare : (N:ℝ)*sqrt N≤S := by
      apply mul_le_mul (by linarith only [np]) (sqrt_le_sqrt (by linarith only [np])) (sqrt_nonneg _) (by positivity)
    rw [abs_div,abs_of_pos sp,div_mul_eq_mul_div,div_mul_eq_mul_div,div_le_iff₀ sp,mul_assoc]
    exact mul_le_mul_of_nonneg_left compare (abs_nonneg _)
  have val : ‖E N‖≤15/10^16 := by
    simp only [E,Complex.norm_real,Real.norm_eq_abs,endpoint]; exact curve_value_bound (big hu)
  have lip (j : ℕ) (hj : j≤N) : ‖E N-E (N-j)‖≤j*((36/10^14*u)/N) := by
    dsimp only [E]; rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    apply (curve_lipschitz (big (step N le_rfl)) (big (step _ (Nat.sub_le ..)))).trans_eq
    rw [Nat.cast_sub hj,show (N:ℝ)*τ-((N:ℝ)-j)*τ=j*τ by ring,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) ht)]
    ring
  have rem (j : ℕ) (hj : j≤N) : ‖parityResidual (ξ/S/2) V σ j-E j‖≤τ*(3/10^12)+τ^2*K j := by
    let v := (j:ℝ)*τ
    let R := firstCurveResidual (value candidate) (correctedValue σ) σ v
    let H := curveResidual (value candidate) v
    let z := parityResidual (ξ/S/2) V σ j
    have h₁ : |R|≤3/10^12 := first v (step j hj)
    have h₂ : ‖z-((H+τ*R:ℝ):ℂ)‖≤τ^2*K j := cost j hj
    have id : z-(H:ℂ)=(z-((H+τ*R:ℝ):ℂ))+((τ*R:ℝ):ℂ) := by push_cast; ring
    change ‖z-(H:ℂ)‖≤_
    rw [id]; apply (norm_add_le ..).trans
    rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg ht]
    linarith only [h₂,mul_le_mul_of_nonneg_left h₁ ht]
  have A := amplitude_of_local_costs hs N0 (ξ/S) V E K ht (by norm_num) freq val lip rem
  have normalized : residualAmplitude (2*n+δ) V=value candidate u+τ*correctedValue σ u := by
    dsimp only [residualAmplitude,V,correctedSeries]
    rw [trialSeries,PowerSeries.coeff_mk,show (2*n+δ+1)/2=N by dsimp only [N]; omega,endpoint]
    simp [(survival_pos N).ne']
  rw [normalized] at A
  change |signedAmplitude n δ (ξ/S)-value candidate u|≤_
  have t := abs_sub_le (signedAmplitude n δ (ξ/S)) (value candidate u+τ*correctedValue σ u) (value candidate u)
  rw [add_sub_cancel_left,abs_mul,abs_of_nonneg ht] at t
  exact t.trans (add_le_add A le_rfl)

end CentralUnimodality.PolynomialTrial
