module

public import CentralUnimodality.SplitDerivativeBounds

/-! Local residual for the actual signed walk after subtracting the
continuum residual and its first correction. The right side is the
sum of the separate bin costs used in the rational verifier. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open Real Set PowerSeries

noncomputable def firstCurveResidual (F G : ℝ → ℝ) (σ : ℕ) (v : ℝ) :=
  -freeCurve v*freeLogCorrection σ v-arc (mixedCurve F G v)-
    (v/2)*arc (fun x => x*(1-x)*splitJet 2 bridgeCurve F v x)

theorem direct_corrected_residual {ω τ : ℝ} {j σ : ℕ} (hs : σ≤1) (hτ : 0≤τ)
    (hω : ω^2=τ^3/32) (ha : |ω| *(2*j+σ)≤9/8) (F G : ℝ → ℝ)
    (hF : ContDiff ℝ 4 F) (hG : ContDiff ℝ 2 G) (v : ℝ) (hv : v=j*τ)
    {K D₂ D₃ D₄ : ℝ} (d₂ : 0≤D₂) (d₄ : 0≤D₄)
    (cost : ∀ k≤j, let a := (k:ℝ)*τ; let b := ((j-k:ℕ):ℝ)*τ
      bridgeLocalCost a τ*(|F b|+τ*|G b|)+|bridgeFirst a| *|G b|≤K)
    (two : ∀ x∈Icc (0:ℝ) 1, splitJetBound 2 bridgeFirst F v x+splitJetBound 2 bridgeCurve G v x≤D₂)
    (three : ∀ x∈Icc (0:ℝ) 1, splitJetBound 3 bridgeCurve F v x≤D₃)
    (four : ∀ x∈Icc (0:ℝ) 1, splitJetBound 4 bridgeCurve F v x≤D₄) :
    ‖parityResidual ω (trialSeries (fun k => F ((k:ℝ)*τ)+τ*G ((k:ℝ)*τ))) σ j-
      ((curveResidual F v+τ*firstCurveResidual F G σ v:ℝ):ℂ)‖≤
      τ^2*(freeLocalCost σ v τ+K+v*D₂/8+v*D₃/24+v^2*D₄/128) := by
  let g := splitCurve F v
  let m := mixedCurve F G v
  let e := splitJet 2 bridgeCurve F v
  have hb (r : ℕ) : ContDiff ℝ r bridgeCurve := by unfold bridgeCurve; fun_prop
  have hb₁ : ContDiff ℝ 2 bridgeFirst := by
    unfold bridgeFirst bridgeLogCorrection bridgeCurve; fun_prop
  have hF₂ : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  have hF₃ : ContDiff ℝ 3 F := hF.of_le (by norm_num)
  have smoothg : ContDiff ℝ 4 g := splitPair_smooth (hb 4) hF v
  have smoothm : ContDiff ℝ 2 m := (splitPair_smooth hb₁ hF₂ v).add (splitPair_smooth (hb 2) hG v)
  have v0 : 0≤v := hv ▸ mul_nonneg (Nat.cast_nonneg _) hτ
  have quad : |sample j (fun x => g x+τ*m x)-(arc g+τ*(arc m+(v/2)*arc (fun x => x*(1-x)*e x)))|≤
      τ^2*(v*D₂/8+v*D₃/24+v^2*D₄/128) := by
    by_cases hz : j=0
    · subst j
      have vz : v=0 := by simpa using hv
      subst v
      have a : g=fun _ => bridgeCurve 0*F 0 := by funext x; simp [g,splitCurve]
      have b : m=fun _ => bridgeFirst 0*F 0+bridgeCurve 0*G 0 := by funext x; simp [m,mixedCurve]
      rw [a,b,arc_const,arc_const]
      simp [sample,average,weight,survival]
    apply direct_split_error (Nat.pos_of_ne_zero hz) hv hτ d₂ d₄ smoothg smoothm
    · exact splitPair_derivative (hb 2) hF₂ v
    · intro x hx
      change |iteratedDeriv 2 (splitPair bridgeFirst F v+splitPair bridgeCurve G v) x|≤_
      rw [iteratedDeriv_add (splitPair_smooth hb₁ hF₂ v).contDiffAt (splitPair_smooth (hb 2) hG v).contDiffAt]
      apply (abs_add_le ..).trans
      apply (add_le_add (splitPair_derivative_bound hb₁ hF₂ v0 x) (splitPair_derivative_bound (hb 2) hG v0 x)).trans
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (two x hx) (sq_nonneg v)
    · intro x hx
      exact (splitPair_derivative_bound (hb 3) hF₃ v0 x).trans (mul_le_mul_of_nonneg_left (three x hx) (pow_nonneg v0 3))
    · intro x hx
      exact (splitPair_derivative_bound (hb 4) hF v0 x).trans (mul_le_mul_of_nonneg_left (four x hx) (pow_nonneg v0 4))
  let P := freeCurve v*(1-τ*freeLogCorrection σ v)-sample j (fun x => g x+τ*m x)
  have H := direct_lattice_residual hs hτ hω ha F G v hv cost
  have eq : P-(curveResidual F v+τ*firstCurveResidual F G σ v)=
      -(sample j (fun x => g x+τ*m x)-(arc g+τ*(arc m+(v/2)*arc (fun x => x*(1-x)*e x)))) := by
    dsimp only [P,g,m,e,curveResidual,firstCurveResidual]; ring
  have b : ‖(P:ℂ)-((curveResidual F v+τ*firstCurveResidual F G σ v:ℝ):ℂ)‖≤
      τ^2*(v*D₂/8+v*D₃/24+v^2*D₄/128) := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,eq,abs_neg]; exact quad
  calc
    _ ≤ ‖parityResidual ω _ σ j-(P:ℂ)‖+‖(P:ℂ)-((curveResidual F v+τ*firstCurveResidual F G σ v:ℝ):ℂ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ _ := (add_le_add H b).trans_eq (by ring)

end CentralUnimodality.ReturnSplit
