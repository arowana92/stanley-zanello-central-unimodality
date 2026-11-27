module

public import CentralUnimodality.SpatialDifferences

/-! Derivatives of arbitrary order of the actual retained cosine sum. -/
@[expose] public section

namespace CentralUnimodality

noncomputable def spatialDerivative (Q J : ℕ) (G : ℝ) (A : ℕ → ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  (4*G/Q)*∑ t ∈ positiveModes J, A t*(G*gridFrequency Q t)^r *
    Real.cos (G*gridFrequency Q t*x+r*(Real.pi/2))

theorem spatial_zero (Q J : ℕ) (G : ℝ) (A : ℕ → ℝ) :
    spatialDerivative Q J G A 0 = spatialCosine Q J G A := by
  funext x
  simp [spatialDerivative,spatialCosine]

theorem spatial_derivative_step (Q J r : ℕ) (G : ℝ) (A : ℕ → ℝ) (x : ℝ) :
    HasDerivAt (spatialDerivative Q J G A r) (spatialDerivative Q J G A (r+1) x) x := by
  have ht (ω c : ℝ) :
      HasDerivAt (fun y : ℝ => c*ω^r*Real.cos (ω*y+r*(Real.pi/2)))
        (c*ω^(r+1)*Real.cos (ω*x+(r+1:ℕ)*(Real.pi/2))) x := by
    have hd : HasDerivAt (fun y : ℝ => ω*y+r*(Real.pi/2)) ω x := by
      simpa using (((hasDerivAt_id x).const_mul ω).add_const ((r:ℝ)*(Real.pi/2)))
    convert ((Real.hasDerivAt_cos _).comp x hd).const_mul (c*ω^r) using 1
    · rfl
    rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,← add_assoc,Real.cos_add_pi_div_two,pow_succ]
    ring
  unfold spatialDerivative
  apply HasDerivAt.const_mul
  exact HasDerivAt.fun_sum (fun t _ => ht (G*gridFrequency Q t) (A t))

theorem spatial_derivative_bound {Q J : ℕ} {G : ℝ} (hG : 0 ≤ G) (A : ℕ → ℝ) (r : ℕ) (x : ℝ) :
    |spatialDerivative Q J G A r x| ≤ spectralAllowance G Q J r (fun t => |A t|) := by
  unfold spatialDerivative spectralAllowance
  rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 4*G/Q)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply Finset.sum_le_sum
  intro t _
  have hw : 0 ≤ G*gridFrequency Q t := by unfold gridFrequency; positivity
  rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg hw _)]
  have hc := Real.abs_cos_le_one (G*gridFrequency Q t*x+r*(Real.pi/2))
  have h := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ |A t| * (G*gridFrequency Q t)^r)
  rw [mul_one] at h
  exact h.trans_eq (mul_comm ..)

end CentralUnimodality
