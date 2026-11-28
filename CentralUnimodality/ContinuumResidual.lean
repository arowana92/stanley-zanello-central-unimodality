module

public import CentralUnimodality.ArcsineQuadrature
public import CentralUnimodality.LatticeCubicInputs
public import CentralUnimodality.ResidualModel

/-! A quantitative comparison of the true staircase amplitude with
a trial for the continuum last-return equation, at finite half-length. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit

open PowerSeries Real

noncomputable def splitCurve (f : ℝ → ℝ) (v x : ℝ) : ℝ := bridgeCurve (v*x)*f (v*(1-x))
noncomputable def curveResidual (f : ℝ → ℝ) (v : ℝ) : ℝ := freeCurve v-arc (splitCurve f v)

theorem splitCurve_continuous {f : ℝ → ℝ} (hf : Continuous f) (v : ℝ) :
    Continuous (splitCurve f v) := by
  unfold splitCurve bridgeCurve; fun_prop

private theorem split_node {j k : ℕ} (hk : k≤j) (τ : ℝ) (f : ℝ → ℝ) :
    splitCurve f (τ*j) ((k:ℝ)/j)=bridgeCurve (τ*k)*f (τ*(j-k:ℕ)) := by
  by_cases zero : j=0
  · have : k=0 := by omega
    simp [zero,this,splitCurve]
  have hn : (j:ℝ)≠0 := by exact_mod_cast zero
  unfold splitCurve
  congr 1
  · congr 1; field_simp
  · congr 1; rw [Nat.cast_sub hk]; field_simp

theorem curve_quadrature {N j : ℕ} (hj : j≤N) {τ K : ℝ} (hK : 0≤K)
    {f : ℝ → ℝ} (hf : Continuous f)
    (hq : ∃ slope, QuadraticRemainder (splitCurve f (τ*j)) slope (K*(τ*j)^2)) :
    |average j (fun k => bridgeCurve (τ*k)*f (τ*(j-k:ℕ)))-arc (splitCurve f (τ*j))|≤
      K*τ^2*N/8 := by
  have same : sample j (splitCurve f (τ*j))=
      average j (fun k => bridgeCurve (τ*k)*f (τ*(j-k:ℕ))) :=
    average_congr (fun k hk => split_node hk τ f)
  rw [← same]
  rcases j with _|j
  · have zero : splitCurve f (τ*(0:ℕ))=fun _ => bridgeCurve 0*f 0 := by funext x; simp [splitCurve]
    rw [zero,arc_const]
    simp [sample,average,weight,survival]
    positivity
  obtain ⟨slope,ht⟩ := hq
  have H := sample_arc_bound (Nat.succ_pos j) (splitCurve_continuous hf _) (by positivity) ht
  have hn : (0:ℝ)<(j+1:ℕ) := by positivity
  have id : K*(τ*(j+1:ℕ))^2/(8*(j+1:ℕ))=K*τ^2*(j+1:ℕ)/8 := by field_simp
  have bound := mul_le_mul_of_nonneg_left (show ((j+1:ℕ):ℝ)≤N by exact_mod_cast hj)
    (by positivity : 0≤K*τ^2)
  exact H.trans (id.le.trans (by linarith only [bound]))

theorem curve_residual_bound {N j σ : ℕ} (hN : 0<N) (hj : j≤N) (hs : σ≤1)
    {ω τ K M : ℝ} (hτ : 0≤τ) (hw : ω^2=τ^3/32) (ha : |ω| * (2*N+1:ℕ)≤1)
    {f : ℝ → ℝ} (hf : Continuous f) (hK : 0≤K) (hb : ∀ k≤N, |f (τ*k)|≤M)
    (hq : ∃ slope, QuadraticRemainder (splitCurve f (τ*j)) slope (K*(τ*j)^2)) :
    ‖parityResidual ω (trialSeries (fun k => f (τ*k))) σ j-(curveResidual f (τ*j):ℂ)‖ ≤
      (1+M)*inputCost τ N+K*τ^2*N/8 := by
  let A := fun k : ℕ => bridgeCurve (τ*k)*f (τ*(j-k:ℕ))
  have mean : complexAverage j (fun k => (A k:ℂ))=(average j A:ℂ) := by
    simp [complexAverage,average]
  have hc : 0 ≤ inputCost τ N := by unfold inputCost; positivity
  have hprod := norm_average_minus (N:=j) (profile ω (trialSeries (fun k => f (τ*k))) σ j)
    (fun k => (A k:ℂ)) (v:=inputCost τ N*M) (by
      intro k hk
      simp only [profile,trial_normalized _ _ _ hs,A,Complex.ofReal_mul,← sub_mul,norm_mul,
        Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul (bridge_curve_bound (hk.trans hj) hτ hw ha) (hb _ ((Nat.sub_le ..).trans hj))
        (abs_nonneg _) hc)
  rw [mean] at hprod
  have quad : ‖(average j A:ℂ)-(arc (splitCurve f (τ*j)):ℂ)‖≤K*τ^2*N/8 := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact curve_quadrature hj hK hf hq
  have htotal := (norm_add_le _ _).trans (add_le_add hprod quad)
  rw [sub_add_sub_cancel] at htotal
  rw [residual_split _ _ _ _ hs,curveResidual,Complex.ofReal_sub,sub_sub_sub_comm]
  exact (norm_sub_le ..).trans ((add_le_add (free_curve_bound hN hj hs hτ hw ha) htotal).trans_eq (by ring))

/-- The first two terms depend only on the trial on a fixed interval.
The finite lattice contribution is explicit and decays as 1/sqrt N. -/
theorem signed_curve_bound {n δ : ℕ} (hδ : δ≤1) (hN : 0<n+δ)
    {θ τ ξ K M e L : ℝ} (hτ : 0≤τ) (hw : (θ/2)^2=τ^3/32)
    (ha : |θ/2| * (2*(n+δ)+1:ℕ)≤1) (hfreq : |θ| * (n+δ:ℕ)*sqrt (n+δ:ℕ)≤ξ)
    {f : ℝ → ℝ} (hf : Continuous f) (hK : 0≤K) (hb : ∀ k≤n+δ, |f (τ*k)|≤M)
    (hq : ∀ j≤n+δ, ∃ slope, QuadraticRemainder (splitCurve f (τ*j)) slope (K*(τ*j)^2))
    (he : |curveResidual f (τ*(n+δ:ℕ))|≤e)
    (hL : ∀ x ∈ Set.Icc 0 (τ*(n+δ:ℕ)), ∀ y ∈ Set.Icc 0 (τ*(n+δ:ℕ)),
      |curveResidual f x-curveResidual f y|≤L*|x-y|) :
    |signedAmplitude n δ θ-f (τ*(n+δ:ℕ))| ≤
      (1+ξ/2)*e+L*(τ*(n+δ:ℕ))+4*sqrt (n+δ:ℕ)*
        ((1+M)*inputCost τ (n+δ)+K*τ^2*(n+δ:ℕ)/8) := by
  let N := n+δ
  have pos : (0:ℝ)<N := by exact_mod_cast hN
  have normalized : residualAmplitude (2*n+δ) (trialSeries (fun k => f (τ*k)))=f (τ*N) := by
    rw [residualAmplitude,trialSeries,coeff_mk,show (2*n+δ+1)/2=N by dsimp [N]; omega]
    simp [(survival_pos N).ne']
  rw [← normalized]
  apply amplitude_of_residual_model hδ hN _ _ (fun j => (curveResidual f (τ*j):ℂ)) hfreq
  · simpa only [Complex.norm_real,Real.norm_eq_abs] using he
  · intro j hj
    have hN₀ : 0≤τ*(N:ℝ) := by positivity
    have hj' : (j:ℝ)≤N := by exact_mod_cast hj
    have mem : τ*(N-j:ℕ)∈Set.Icc 0 (τ*(N:ℝ)) :=
      ⟨by positivity,mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le N j) hτ⟩
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    apply (hL _ ⟨hN₀,le_rfl⟩ _ mem).trans_eq
    change L*|τ*(N:ℝ)-τ*(N-j:ℕ)|=j*((L*(τ*N))/N)
    rw [Nat.cast_sub hj,show τ*(N:ℝ)-τ*((N:ℝ)-j)=τ*j by ring,
      abs_of_nonneg (mul_nonneg hτ (Nat.cast_nonneg j))]
    field_simp
  · intro j hj
    exact curve_residual_bound hN hj (by omega) hτ hw ha hf hK hb (hq _ hj)

end CentralUnimodality.ReturnSplit
