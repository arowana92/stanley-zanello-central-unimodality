module

public import CentralUnimodality.ResidualModel

/-! Pointwise inversion costs for the true signed first-return law.
At a late return the bound keeps the time remaining in the residual. -/
@[expose] public section

namespace CentralUnimodality

open Real

theorem scaled_survival_monotone : Monotone (fun j : ℕ => sqrt (j:ℝ)*survival j) := by
  apply monotone_nat_of_le_succ
  intro j
  have a := survival_pos j
  have b := survival_pos (j+1)
  apply (sq_le_sq₀ (mul_nonneg (sqrt_nonneg _) a.le) (mul_nonneg (sqrt_nonneg _) b.le)).mp
  rw [mul_pow,mul_pow,sq_sqrt (by positivity),sq_sqrt (by positivity),survival_succ]
  push_cast
  field_simp
  nlinarith only [sq_nonneg (survival j)]

theorem returnMass_exact {j : ℕ} (hj : 0<j) : returnMass j=survival j/(2*j-1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  rw [returnMass_succ,survival_succ]
  push_cast
  have d : (2:ℝ)*((k:ℝ)+1)-1≠0 := by linarith only [Nat.cast_nonneg (α:=ℝ) k]
  field_simp; ring

theorem returnMass_ratio {j N : ℕ} (hj : 501≤j) (hle : j≤N) :
    returnMass j/survival N ≤ (501/1000:ℝ)*(sqrt (N:ℝ)/sqrt (j:ℝ))/j := by
  have p : (501:ℝ)≤j := by exact_mod_cast hj
  have j0 : (0:ℝ)<j := by linarith
  have d0 : 0<2*(j:ℝ)-1 := by linarith
  have sj := sqrt_pos.mpr j0
  have sn := survival_pos N
  have m := scaled_survival_monotone hle
  change sqrt (j:ℝ)*survival j≤sqrt (N:ℝ)*survival N at m
  rw [returnMass_exact (by omega)]
  apply (div_le_iff₀ sn).mpr
  apply (div_le_iff₀ d0).mpr
  field_simp
  have t : (1000:ℝ)*j≤501*(2*j-1) := by linarith only [p]
  have A := mul_le_mul_of_nonneg_right m (show 0≤1000*(j:ℝ) by positivity)
  have B := mul_le_mul_of_nonneg_left t (mul_nonneg (sqrt_nonneg (N:ℝ)) sn.le)
  linarith only [A,B]

theorem inverseAt_local_error (ω : ℝ) (N : ℕ) (E G : ℕ → ℂ) (b : ℕ → ℝ)
    (hb : ∀ j≤N, ‖E j-G j‖≤b j) :
    ‖inverseAt ω N E-inverseAt ω N G‖≤b N+∑ j ∈ Finset.range (N+1), returnMass j*b (N-j) := by
  have eq : inverseAt ω N E-inverseAt ω N G=E N-G N-
      ∑ j ∈ Finset.range (N+1), returnSymbol ω j*(E (N-j)-G (N-j)) := by
    simp only [inverseAt,mul_sub,Finset.sum_sub_distrib]; abel
  rw [eq]
  apply (norm_sub_le ..).trans (add_le_add (hb N le_rfl) ((norm_sum_le ..).trans (Finset.sum_le_sum _)))
  intro j _
  rw [norm_mul]
  exact mul_le_mul (norm_returnSymbol_le ..) (hb _ (Nat.sub_le ..)) (norm_nonneg _) (by unfold returnMass; positivity)

end CentralUnimodality
