module

public import CentralUnimodality.QuadraticOuterSymbols
public import CentralUnimodality.DirectCorrectedResidual

/-! Replacing the lattice inputs by the signed quadratic approximants in the
actual last-return convolution, uniformly across the small and outer angles. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open PowerSeries

noncomputable def bridgeSecond (v : ℝ) :=
  bridgeCurve v*((bridgeLogCorrection v)^2/2-bridgeSecondLog v)
noncomputable def freeSecond (σ : ℕ) (v : ℝ) :=
  freeCurve v*((freeLogCorrection σ v)^2/2-freeSecondLog σ v)
noncomputable def secondMixedCurve (F G : ℝ → ℝ) (v x : ℝ) :=
  splitPair bridgeSecond F v x+splitPair bridgeFirst G v x

private theorem quadratic_product_error {z : ℂ} {b t a c f g E : ℝ} (ht : 0≤t)
    (H : ‖z-(b*(1-t*a+t^2*c):ℝ)‖≤t^3*E) :
    ‖z*((f+t*g:ℝ):ℂ)-((b*f+t*((-b*a)*f+b*g)+t^2*((b*c)*f+(-b*a)*g):ℝ):ℂ)‖≤
      t^3*(E*(|f|+t*|g|)+|b*c| *|g|) := by
  have eq : z*((f+t*g:ℝ):ℂ)-((b*f+t*((-b*a)*f+b*g)+t^2*((b*c)*f+(-b*a)*g):ℝ):ℂ)=
      (z-((b*(1-t*a+t^2*c):ℝ):ℂ))*((f+t*g:ℝ):ℂ)+((t^3*(b*c)*g:ℝ):ℂ) := by push_cast; ring
  rw [eq]
  apply (norm_add_le ..).trans
  rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
  have linear := abs_add_le f (t*g)
  rw [abs_mul,abs_of_nonneg ht] at linear
  have cost := mul_le_mul H linear (abs_nonneg _) ((norm_nonneg _).trans H)
  rw [abs_mul (t^3*(b*c)) g,abs_mul (t^3) (b*c),abs_of_nonneg (pow_nonneg ht 3)]
  linarith only [cost]

theorem quadratic_lattice_residual {ω τ : ℝ} {j N σ : ℕ} (hs : σ≤1) (hτ : 0≤τ) (hω : ω^2=τ^3/32)
    (hj : j≤N) (hN : 10000≤N) (hu : (N:ℝ)*τ≤114) (F G : ℝ → ℝ) (v : ℝ) (hv : v=j*τ)
    {K : ℝ} (cost : ∀ k≤j, let a := (k:ℝ)*τ; let b := ((j-k:ℕ):ℝ)*τ
      bridgeQuadraticCost a τ*(|F b|+τ*|G b|)+|bridgeSecond a| *|G b|≤K) :
    ‖parityResidual ω (trialSeries (fun k => F ((k:ℝ)*τ)+τ*G ((k:ℝ)*τ))) σ j-
      ((freeCurve v*(1-τ*freeLogCorrection σ v)+τ^2*freeSecond σ v-
        sample j (fun x => splitCurve F v x+τ*mixedCurve F G v x+τ^2*secondMixedCurve F G v x):ℝ):ℂ)‖≤
      τ^3*(freeQuadraticCost σ v τ+K) := by
  let T := trialSeries (fun k : ℕ => F ((k:ℝ)*τ)+τ*G ((k:ℝ)*τ))
  let g := fun x => splitCurve F v x+τ*mixedCurve F G v x+τ^2*secondMixedCurve F G v x
  have bound := norm_average_minus (N:=j) (profile ω T σ j) (fun k => (g ((k:ℝ)/j):ℂ))
    (v:=τ^3*K) (by
      intro k hk
      have coords : v*((k:ℝ)/j)=k*τ ∧ v*(1-(k:ℝ)/j)=(j-k:ℕ)*τ := by
        by_cases hz : j=0
        · simp [hv,hz,show k=0 by omega]
        have nz : (j:ℝ)≠0 := Nat.cast_ne_zero.mpr hz
        rw [hv,Nat.cast_sub hk]; constructor <;> field_simp
      have H := (retained_quadratic_symbols hs hτ hω (hk.trans hj) hN hu _ rfl).2
      simp only [profile,T,trial_normalized _ _ _ hs,g,splitCurve,mixedCurve,secondMixedCurve,splitPair,
        coords.1,coords.2]
      exact (quadratic_product_error hτ H).trans (mul_le_mul_of_nonneg_left (cost k hk) (pow_nonneg hτ 3)))
  have mean : complexAverage j (fun k => (g ((k:ℝ)/j):ℂ))=(sample j g:ℂ) := by
    simp [complexAverage,sample,average]
  rw [mean] at bound
  rw [residual_split _ _ _ _ hs,Complex.ofReal_sub,sub_sub_sub_comm]
  have f := (retained_quadratic_symbols hs hτ hω hj hN hu v hv).1
  dsimp only at f
  rw [show freeCurve v*(1-τ*freeLogCorrection σ v)+τ^2*freeSecond σ v=
    freeCurve v*(1-τ*freeLogCorrection σ v+τ^2*(freeLogCorrection σ v^2/2-freeSecondLog σ v))
    by unfold freeSecond; ring]
  exact (norm_sub_le ..).trans ((add_le_add f bound).trans_eq (by ring))

end CentralUnimodality.ReturnSplit
