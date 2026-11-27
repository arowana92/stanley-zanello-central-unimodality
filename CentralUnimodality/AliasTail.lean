module

public import CentralUnimodality.CorankTail
public import CentralUnimodality.NormalizedCells

/-! Bound the normalized alias contribution using the ballot survival factor
and an explicit Gaussian rate on the length range of the central grid. -/
@[expose] public section

namespace CentralUnimodality

theorem ballot_fraction (n δ : ℕ) (hδ : δ ≤ 1) :
    ((2*n+δ).choose n:ℝ)/(2:ℝ)^(2*n+δ) = survival (n+δ) := by
  rcases (by omega : δ = 0 ∨ δ = 1) with rfl|rfl
  · simp [survival,Nat.centralBinom,pow_mul]
    norm_num
  · have h := survival_even (n+1)
    rw [show 2*(n+1) = 2*n+1+1 by omega,card_strictWords n 1 (by decide)] at h
    simp only [pow_succ (2:ℝ) (2*n+1),Nat.cast_mul,Nat.cast_ofNat] at h
    convert h using 1
    field_simp

theorem survival_inv_le {N : ℕ} (hN : 0 < N) : (survival N)⁻¹ ≤ 2*Real.sqrt N := by
  have hs := survival_pos N
  apply (inv_le_iff_one_le_mul₀ hs).mpr
  have h : (1:ℝ)^2 ≤ (2*Real.sqrt N*survival N)^2 := by
    rw [one_pow,mul_pow,mul_pow,Real.sq_sqrt (by positivity)]
    nlinarith only [survival_sq_lower hN]
  have hw := (sq_le_sq₀ (by norm_num) (by positivity)).mp h
  linarith only [hw]

theorem normalized_corankTail {n δ : ℕ} (hδ : δ ≤ 1) (hm : 0 < 2*n+δ) {x : ℝ} (hx : 0 ≤ x) :
    (corankTail n δ x:ℝ)/((2*n+δ).choose n:ℝ) ≤
      2*Real.sqrt (n+δ)*Real.exp (-2*x^2/(squareWeights (2*n+δ):ℝ)) := by
  have hc : (0:ℝ) < (2*n+δ).choose n := by exact_mod_cast Nat.choose_pos (by omega : n ≤ 2*n+δ)
  have he : (2:ℝ)^(2*n+δ) / ((2*n+δ).choose n:ℝ) = (survival (n+δ))⁻¹ := by
    rw [← ballot_fraction n δ hδ,inv_div]
  calc
    _ ≤ _ := div_le_div_of_nonneg_right (corankTail_chernoff n δ hδ hm hx) hc.le
    _ = _ := by rw [mul_div_right_comm,he]
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_right (by simpa using survival_inv_le (N := n+δ) (by omega)) (Real.exp_pos _).le

theorem excess_le_tail {n δ Q j : ℕ} (hj : j ≤ n*(n+δ))
    (hc : 2*(n*(n+δ)-j)+(3*n+2*δ+1) < Q) {x : ℝ}
    (hx : ((n*(n+δ)-j:ℕ):ℝ)+(3*n+2*δ+1)+x ≤ Q) :
    periodicCount n δ Q j ≤ rankCount (2*n+δ) j + corankTail n δ x := by
  apply (periodicCount_bounds hj hc).2.trans
  apply Nat.add_le_add_left
  apply Finset.sum_le_sum
  intro l _
  split
  next h =>
    have h' : (Q:ℝ) ≤ ((n*(n+δ)-j:ℕ):ℝ)+((n*(n+δ)-l:ℕ):ℝ)+(3*n+2*δ+1) := by exact_mod_cast h
    rw [ite_eq_left (by linarith only [hx,h'] : x ≤ ((n*(n+δ)-l:ℕ):ℝ))]
  next => exact Nat.zero_le _

theorem gaussian_grid_rate {m N : ℕ} (hm : m ≤ 2*N) (hN : 1024 ≤ N) :
    (599/100:ℝ)*(squareWeights m:ℝ) ≤ 2*(Witness.cellScale N)^2 := by
  have hW : 6*(squareWeights m:ℝ) = m*((m:ℝ)+1)*(2*m+1) := by exact_mod_cast squareWeights_closed m
  have hh : (m:ℝ) ≤ 2*N := by exact_mod_cast hm
  have h₁ := mul_le_mul hh (add_le_add hh (le_refl (1:ℝ))) (by positivity) (by positivity)
  have h₂ := mul_le_mul h₁ (add_le_add (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2)) le_rfl)
    (by positivity : (0:ℝ) ≤ 2*m+1) (by positivity)
  rw [Witness.cellScale,mul_pow,Real.sq_sqrt (by positivity)]
  have hn : (1024:ℝ) ≤ N := by exact_mod_cast hN
  have h₃ := mul_nonneg (sub_nonneg.mpr hn) (sq_nonneg (N:ℝ))
  have h₄ := mul_nonneg (sub_nonneg.mpr hn) (by positivity : 0 ≤ (N:ℝ))
  nlinarith only [hW,h₂,h₃,h₄,hn]

end CentralUnimodality
