module

public import CentralUnimodality.KilledProducts
public import CentralUnimodality.SurvivalBounds

/-! After conditioning on a ballot walk, keeping at least a sixty-fourth of
the steps as a prefix costs a factor of at most sixteen in either parity. -/
@[expose] public section

namespace CentralUnimodality

theorem survivors_one_card (m : ℕ) : (survivors 1 m).card = m.choose (m/2) := by
  let n := m/2
  let δ := m%2
  have hδ : δ ≤ 1 := by dsimp [δ]; omega
  have hm : 2*n+δ = m := by dsimp [n,δ]; omega
  have h := ballot_rank_polynomial (1:ℕ) n δ hδ
  simp only [corankSum,one_pow,Finset.sum_const,smul_eq_mul,mul_one] at h
  rw [sum_rankCount n δ hδ,hm] at h
  have hs : survivors 1 m = ballots m := by
    ext w
    simp [survivors,ballots,positive_one_iff]
  rwa [hs]

theorem ballot_survival (m : ℕ) :
    (m.choose (m/2):ℝ)/(2:ℝ)^m = survival ((m+1)/2) := by
  let n := m/2
  let δ := m%2
  have hδ : δ ≤ 1 := by dsimp [δ]; omega
  have hm : 2*n+δ = m := by dsimp [n,δ]; omega
  have hc := card_strictWords n δ hδ
  rw [hm] at hc
  have e : (strictWords (m+1)).card/(2:ℝ)^(m+1) = (m.choose (m/2):ℝ)/(2:ℝ)^m := by
    rw [hc,pow_succ,Nat.cast_mul,Nat.cast_ofNat]
    dsimp [n]
    ring
  rw [← e]
  rcases (by omega : m+1 = 2*((m+1)/2) ∨ m+1 = 2*((m+1)/2)+1) with h|h
  · simpa only [← h] using survival_even ((m+1)/2)
  · simpa only [← h] using survival_odd ((m+1)/2)

theorem prefix_survival_factor {p m : ℕ} (hm : 1 ≤ m) (hp : m/64 ≤ p) :
    survival ((p+1)/2) ≤ 16*survival ((m+1)/2) := by
  let K := (p+1)/2
  let N := (m+1)/2
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hsize : 4*(N:ℝ) ≤ 256*((K:ℝ)+1) := by
    exact_mod_cast (by dsimp [K,N]; omega : 4*N ≤ 256*(K+1))
  have h₁ := survival_sq_upper K
  have h₂ := survival_sq_lower hN
  have h₃ := mul_le_mul_of_nonneg_right hsize (sq_nonneg (survival N))
  have h₄ : ((K:ℝ)+1)*(survival K)^2 ≤ ((K:ℝ)+1)*(16*survival N)^2 := by
    linarith only [h₁,h₂,h₃]
  exact (sq_le_sq₀ (survival_pos K).le (mul_nonneg (by norm_num) (survival_pos N).le)).mp
    (le_of_mul_le_mul_left h₄ (by positivity))

/-- The absolute Fourier transform under the uniform distribution on
partitions contained in either staircase, on an arc with block rate c. -/
theorem conditional_rank_arc {ω c : ℝ} {L : ℕ} (hL : 0 < L) (hc : 0 ≤ c)
    (h : KilledBound ω L (Real.exp (-c*L))) (n δ : ℕ) (hδ : δ ≤ 1) (hm : 1 ≤ 2*n+δ) :
    ‖∑ j ∈ Finset.range (n*(n+δ)+1),
      rankCount (2*n+δ) j • (areaCharacter ω 2)^(n*(n+δ)-j)‖/((2*n+δ).choose n:ℝ) ≤
      16*Real.exp (c*L-c*(63/64)*(2*n+δ)) := by
  let m := 2*n+δ
  let t := m/64
  let k := (m-t)/L
  let p := t+(m-t)%L
  have ht : t ≤ m := Nat.div_le_self ..
  have hsplit : m = p+k*L := by
    dsimp [p,k]
    have := Nat.mod_add_div (m-t) L
    rw [Nat.mul_comm L] at this
    omega
  have hp : m/64 ≤ p := Nat.le_add_right _ _
  have hfrac : 64*t ≤ m := by simpa only [t,Nat.mul_comm] using Nat.div_mul_le_self m 64
  have hcount : m < t+k*L+L := by
    have := Nat.mod_lt (m-t) hL
    dsimp [p] at hsplit
    omega
  have ht' : 64*(t:ℝ) ≤ m := by exact_mod_cast hfrac
  have hcount' : (m:ℝ) ≤ t+k*L+L := by exact_mod_cast hcount.le
  have hsteps : (63/64)*(m:ℝ)-(L:ℝ) ≤ k*L := by linarith only [ht',hcount']
  have he : (Real.exp (-c*L))^k ≤ Real.exp (c*L-c*(63/64)*m) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hsteps hc]
  have hs := rank_fourier_blocks h (Real.exp_pos _).le n δ hδ p k hsplit
  rw [survivors_one_card,ballot_survival] at hs
  have hr := mul_le_mul (prefix_survival_factor hm hp) he (by positivity) (mul_nonneg (by norm_num) (survival_pos ((m+1)/2)).le)
  have hb := hs.trans hr
  have hhalf : m/2 = n := by dsimp [m]; omega
  have hnorm := ballot_survival m
  rw [hhalf] at hnorm
  have hpos : 0 < (m.choose n:ℝ) := by
    exact_mod_cast Nat.choose_pos (by dsimp [m]; omega : n ≤ m)
  apply (div_le_iff₀ hpos).mpr
  rw [← hnorm] at hb
  have hh := (div_le_iff₀ (by positivity)).mp hb
  dsimp [m] at hh ⊢
  push_cast at hh ⊢
  convert hh using 1
  field_simp

end CentralUnimodality
