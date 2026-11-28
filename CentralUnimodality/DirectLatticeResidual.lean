module

public import CentralUnimodality.RetainedLatticeSymbols
public import CentralUnimodality.DirectSplitError
public import CentralUnimodality.ContinuumResidual

/-! Error in replacing the two actual lattice inputs in the residual
by their first corrections, before approximating the discrete split. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open Real PowerSeries

noncomputable def bridgeFirst (a : ℝ) := -bridgeCurve a*bridgeLogCorrection a
noncomputable def freeLocalCost (σ : ℕ) (v τ : ℝ) :=
  freeCurve v*freeLogRemainder v τ+freeCurve v*(freeLogCorrection σ v)^2/2
noncomputable def bridgeLocalCost (v τ : ℝ) :=
  bridgeCurve v*bridgeLogRemainder v τ+bridgeCurve v*(bridgeLogCorrection v)^2/2

noncomputable def mixedCurve (F G : ℝ → ℝ) (v x : ℝ) :=
  bridgeFirst (v*x)*F (v*(1-x))+bridgeCurve (v*x)*G (v*(1-x))

private theorem product_error {z : ℂ} {b l f g τ E : ℝ} (ht : 0≤τ)
    (H : ‖z-(b*(1-τ*l):ℝ)‖≤τ^2*E) :
    ‖z*((f+τ*g:ℝ):ℂ)-((b*f+τ*((-b*l)*f+b*g):ℝ):ℂ)‖≤
      τ^2*(E*(|f|+τ*|g|)+|-b*l| *|g|) := by
  have eq : z*((f+τ*g:ℝ):ℂ)-((b*f+τ*((-b*l)*f+b*g):ℝ):ℂ)=
      (z-((b*(1-τ*l):ℝ):ℂ))*((f+τ*g:ℝ):ℂ)+((τ^2*(-b*l)*g:ℝ):ℂ) := by push_cast; ring
  rw [eq]
  apply (norm_add_le ..).trans
  rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
  have linear := abs_add_le f (τ*g)
  rw [abs_mul,abs_of_nonneg ht] at linear
  have cost := mul_le_mul H linear (abs_nonneg _) ((norm_nonneg _).trans H)
  rw [abs_mul (τ^2*(-b*l)) g,abs_mul (τ^2) (-b*l),abs_of_nonneg (sq_nonneg τ)]
  linarith only [cost]

theorem direct_lattice_residual {ω τ : ℝ} {j σ : ℕ} (hs : σ≤1) (hτ : 0≤τ)
    (hω : ω^2=τ^3/32) (ha : |ω| *(2*j+σ)≤9/8) (F G : ℝ → ℝ) (v : ℝ) (hv : v=j*τ)
    {K : ℝ} (cost : ∀ k≤j, let a := (k:ℝ)*τ; let b := ((j-k:ℕ):ℝ)*τ
      bridgeLocalCost a τ*(|F b|+τ*|G b|)+|bridgeFirst a| *|G b|≤K) :
    ‖parityResidual ω (trialSeries (fun k => F ((k:ℝ)*τ)+τ*G ((k:ℝ)*τ))) σ j-
      ((freeCurve v*(1-τ*freeLogCorrection σ v)-sample j (fun x => splitCurve F v x+τ*mixedCurve F G v x):ℝ):ℂ)‖
      ≤τ^2*(freeLocalCost σ v τ+K) := by
  let T := trialSeries (fun k : ℕ => F ((k:ℝ)*τ)+τ*G ((k:ℝ)*τ))
  let g := fun x => splitCurve F v x+τ*mixedCurve F G v x
  have nodes (k : ℕ) (hk : k≤j) : v*((k:ℝ)/j)=k*τ ∧ v*(1-(k:ℝ)/j)=(j-k:ℕ)*τ := by
    by_cases hz : j=0
    · have zero : k=0 := by omega
      simp [hv,hz,zero]
    have nz : (j:ℝ)≠0 := Nat.cast_ne_zero.mpr hz
    rw [hv,Nat.cast_sub hk]
    constructor <;> field_simp
  have bound := norm_average_minus (N:=j) (profile ω T σ j) (fun k => (g ((k:ℝ)/j):ℂ))
    (v:=τ^2*K) (by
      intro k hk
      obtain ⟨a,b⟩ := nodes k hk
      have ang : |ω| *(2*k)≤9/8 := (mul_le_mul_of_nonneg_left
        (show 2*(k:ℝ)≤2*j+σ by exact_mod_cast (by omega : 2*k≤2*j+σ)) (abs_nonneg _)).trans ha
      have H := bridge_corrected_symbol hτ hω ang _ rfl
      simp only [profile,T,trial_normalized _ _ _ hs,g,splitCurve,mixedCurve,a,b]
      exact (product_error hτ H).trans (mul_le_mul_of_nonneg_left (cost k hk) (sq_nonneg τ)))
  have mean : complexAverage j (fun k => (g ((k:ℝ)/j):ℂ))=(sample j g:ℂ) := by
    simp [complexAverage,sample,average]
  rw [mean] at bound
  rw [residual_split _ _ _ _ hs,Complex.ofReal_sub,sub_sub_sub_comm]
  exact (norm_sub_le ..).trans ((add_le_add (free_corrected_symbol hs hτ hω ha v hv) bound).trans_eq (by
    dsimp [freeLocalCost]; ring))

end CentralUnimodality.ReturnSplit
