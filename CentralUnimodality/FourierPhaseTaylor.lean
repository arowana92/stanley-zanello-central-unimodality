module

public import CentralUnimodality.CosineTaylor

/-! Taylor polynomials with exact signed integer numerators for all
spatial derivatives of the Fourier cosine kernel. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial

open Real Set

noncomputable def phase (r : ℕ) (t : ℝ) := cos (t+r*π/2)

def phaseInt : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | r+2 => -phaseInt r

theorem phase_zero : ∀ r, phase r 0=(phaseInt r:ℝ)
  | 0 => by simp [phase,phaseInt]
  | 1 => by simp [phase,phaseInt]
  | r+2 => by
    rw [phaseInt,Int.cast_neg,← phase_zero r]
    unfold phase
    rw [show (0:ℝ)+(r+2:ℕ)*π/2=(0+r*π/2)+π by push_cast; ring,cos_add_pi]

theorem phase_derivative (r : ℕ) (t : ℝ) : HasDerivAt (phase r) (phase (r+1) t) t := by
  have H := ((hasDerivAt_id t).add_const ((r:ℝ)*π/2)).cos
  convert H using 1
  · rfl
  · unfold phase
    rw [show t+(r+1:ℕ)*π/2=(t+r*π/2)+π/2 by push_cast; ring,cos_add_pi_div_two]
    simp

theorem phase_iterated (r k : ℕ) : iteratedDeriv k (phase r)=phase (r+k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ,ih]; funext x
    exact (phase_derivative (r+k) x).deriv

noncomputable def phaseTaylor (r D : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (D+1), (phaseInt (r+j):ℝ)*t^j/j.factorial

theorem phase_remainder (r D : ℕ) (t : ℝ) :
    |phase r t-phaseTaylor r D t|≤|t|^(D+1)/(D+1).factorial := by
  by_cases hz : t=0
  · subst t
    simp [phaseTaylor,Finset.sum_range_succ',phase_zero]
  let s := uIcc 0 t
  have smooth (i : ℕ) : ContDiff ℝ i (phase r) := by unfold phase; fun_prop
  obtain ⟨y,_,hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n:=D) (Ne.symm hz)
    ((smooth (D+1)).contDiffOn (s:=s))
  have der (k : ℕ) : iteratedDerivWithin k (phase r) s 0=phase (r+k) 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (Ne.symm hz)) (smooth k).contDiffAt
      left_mem_uIcc,phase_iterated]
  have hsum : taylorWithinEval (phase r) D s 0 t=phaseTaylor r D t := by
    rw [taylor_within_apply,phaseTaylor]
    apply Finset.sum_congr rfl
    intro j _
    rw [der,phase_zero]
    simp [smul_eq_mul,div_eq_mul_inv]; ring
  change phase r t-taylorWithinEval (phase r) D s 0 t=_ at hy
  rw [hsum,phase_iterated] at hy
  rw [hy]
  simp only [sub_zero,abs_div,abs_mul,abs_pow,Nat.abs_cast]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_of_le_one_left (by positivity)
  exact abs_cos_le_one _

end CentralUnimodality.PolynomialTrial
