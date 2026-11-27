module

public import CentralUnimodality.KilledSurvival
public import CentralUnimodality.SineArc

/-! The minimum of the two certified killed-row bounds in fair probability
units. Any verified unrestricted envelope may be used at each suffix length. -/
@[expose] public section

namespace CentralUnimodality

private theorem pair_whole (ω : ℝ) (n : ℕ) :
    EndpointNormBound ω n ((2:ℝ)^n*pairFactor ω (n/2)) := by
  have h := endpoint_norm_even ω (n/2)
  rcases (by omega : n = 2*(n/2) ∨ n = 2*(n/2)+1) with he|ho
  · nth_rw 1 2 [he]
    exact h
  · have hh := endpoint_norm_one h
    rwa [← ho,← mul_assoc,show 2*(2:ℝ)^(2*(n/2)) = 2^n by rw [mul_comm,← pow_succ,← ho]] at hh

private theorem restore_mass (f : ℕ → ℝ) (n : ℕ) :
    (∑ t ∈ Finset.range (n+1), f t/(2:ℝ)^t)*(2:ℝ)^n =
      ∑ t ∈ Finset.range (n+1), f t*2^(n-t) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  have h : t+(n-t)=n := by have := Finset.mem_range.mp ht; omega
  have he : (2:ℝ)^n = 2^t*2^(n-t) := by rw [← pow_add,h]
  rw [he]
  field_simp

theorem killed_block_bound (ω : ℝ) {a : ℕ} (ha : 0 < a) (n : ℕ) (s : Finset ℤ)
    (ρ : ℕ → ℝ) (hρ : ∀ j ≤ n, pairFactor ω (j/2) ≤ ρ j) :
    (∑ z ∈ s, ‖killedAt ω a n z‖)/(2:ℝ)^n ≤
      min (1-∑ t ∈ Finset.range (n+1), (hitWords a t).card/(2:ℝ)^t)
        (ρ n + ∑ t ∈ Finset.range (n+1), (hitWords a t).card/(2:ℝ)^t*ρ (n-t)) := by
  have hp : 0 < (2:ℝ)^n := by positivity
  apply le_min
  · apply (div_le_iff₀ hp).mpr
    rw [sub_mul,one_mul,restore_mass]
    have hmass : ((survivors a n).card:ℝ) +
        ∑ t ∈ Finset.range (n+1), (hitWords a t).card*(2:ℝ)^(n-t) = 2^n := by exact_mod_cast survivor_hit_total ha n
    linarith only [hmass,killed_norm_le_survivors ω a n s]
  · apply (div_le_iff₀ hp).mpr
    have h := killed_norm_from_first_hits ω ha n (fun j => (2:ℝ)^j*ρ j) (fun j hj S =>
      (pair_whole ω j S).trans (mul_le_mul_of_nonneg_left (hρ j hj) (by positivity))) s
    have he := restore_mass (fun t => (hitWords a t).card*ρ (n-t)) n
    simp only [div_mul_eq_mul_div] at *
    rw [add_mul,he,mul_comm (ρ n)]
    simpa only [mul_left_comm,mul_comm,mul_assoc] using h

end CentralUnimodality
