module

public import CentralUnimodality.LocalizedInverse

/-! Keep a pointwise Fourier bound on each first return when inverting the
renewal equation. A uniform part of the local error pays only the fair
mass; the variable part keeps the frequency-dependent saving. -/
@[expose] public section

namespace CentralUnimodality

theorem inverseAt_discounted_error {ω s t : ℝ} (N : ℕ) (E G : ℕ → ℂ)
    (K D : ℕ → ℝ) (s0 : 0≤s) (endpt : D N=1)
    (hd : ∀ v≤N, D v≤1)
    (symbol : ∀ j≤N, ‖returnSymbol ω j‖≤returnMass j*D (N-j))
    (localBound : ∀ j≤N, ‖E j-G j‖≤s+t*K j) :
    ‖inverseAt ω N E-inverseAt ω N G‖≤s+t*(D N*K N)+
      ∑ j ∈ Finset.range (N+1), returnMass j*(s+t*(D (N-j)*K (N-j))) := by
  rw [endpt,one_mul]
  have eq : inverseAt ω N E-inverseAt ω N G=E N-G N-
      ∑ j ∈ Finset.range (N+1), returnSymbol ω j*(E (N-j)-G (N-j)) := by
    simp only [inverseAt,mul_sub,Finset.sum_sub_distrib]; abel
  rw [eq]
  apply (norm_sub_le ..).trans (add_le_add (localBound N le_rfl) ((norm_sum_le ..).trans (Finset.sum_le_sum _)))
  intro j hj
  have jm : j≤N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have sig := symbol j jm
  have mass : 0≤returnMass j := (norm_nonneg _).trans (norm_returnSymbol_le ω j)
  have small := mul_le_mul_of_nonneg_right (hd (N-j) (Nat.sub_le ..)) (mul_nonneg mass s0)
  rw [norm_mul]
  apply (mul_le_mul sig (localBound (N-j) (Nat.sub_le ..)) (norm_nonneg _) ((norm_nonneg _).trans sig)).trans
  nlinarith only [small]

end CentralUnimodality
