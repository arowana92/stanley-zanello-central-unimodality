module

public import CentralUnimodality.RankInnerTail
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The signed conditional law assigns equal mass to a shifted corank and
its reflection. Its transform is bounded by the absolute characteristic
function of corank. -/
@[expose] public section

namespace CentralUnimodality

open PowerSeries

private theorem conjugate_character (ω : ℝ) (x : ℤ) :
    areaCharacter ω (-x) = (starRingEnd ℂ) (areaCharacter ω x) := by
  rw [areaCharacter,areaCharacter,← Complex.exp_conj]
  congr 1
  simp

private theorem char_nat_mul (ω : ℝ) (x : ℤ) (k : ℕ) :
    areaCharacter ω ((k:ℤ)*x) = (areaCharacter ω x)^k := by
  induction k with
  | zero => simp [areaCharacter_zero]
  | succ k ih => rw [Nat.cast_succ,add_mul,one_mul,areaCharacter_add,ih,pow_succ]

theorem signed_norm_le_corank (θ : ℝ) (n δ : ℕ) (hδ : δ ≤ 1) :
    ‖coeff (2*n+δ+1) (fairSeries (areaCharacter (θ/2)) strictWords)‖ ≤
      survival ((2*n+δ+1)/2)*‖corankCharacteristic θ n δ‖ := by
  let m := 2*n+δ
  let D := n*(n+δ)
  let A := (2*(n:ℤ)+δ+1) + (n+δ)
  let Z := ∑ j ∈ Finset.range (D+1), rankCount m j • areaCharacter (θ/2) (signedAreaAtRank n δ j)
  let Q := ∑ j ∈ Finset.range (D+1), rankCount m j • (areaCharacter (θ/2) 2)^(D-j)
  have hpos : Z = areaCharacter (θ/2) A * Q := by
    dsimp only [Z,Q]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hd : j ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have he : signedAreaAtRank n δ j = A+((D-j:ℕ):ℤ)*2 := by
      rw [Nat.cast_sub hd]
      dsimp [signedAreaAtRank,A,D]
      ring
    rw [he,areaCharacter_add,char_nat_mul]
    simp only [nsmul_eq_mul]
    ring
  have hneg : (∑ j ∈ Finset.range (D+1), rankCount m j • areaCharacter (θ/2) (-signedAreaAtRank n δ j)) =
      (starRingEnd ℂ) Z := by simp [Z,conjugate_character]
  have hZ : ‖Z‖ = ‖Q‖ := by rw [hpos,norm_mul,norm_areaCharacter,one_mul]
  have hh : ‖Z+(starRingEnd ℂ) Z‖ ≤ 2*‖Q‖ := by
    simpa only [Complex.norm_conj,hZ,two_mul] using norm_add_le Z ((starRingEnd ℂ) Z)
  have hsum : coeff (m+1) (fairSeries (areaCharacter (θ/2)) strictWords) =
      (2:ℂ)⁻¹^(m+1)*(Z+(starRingEnd ℂ) Z) := by
    rw [coeff_walkSeries,signed_ranks _ n δ hδ]
    simp only [nsmul_add,Finset.sum_add_distrib]
    exact congrArg _ (congrArg (Z+·) hneg)
  have hhalf : m/2 = n := by dsimp [m]; omega
  have hn : 0 < (m.choose n:ℝ) := by exact_mod_cast Nat.choose_pos (by dsimp [m]; omega : n ≤ m)
  have hs := ballot_survival m
  rw [hhalf] at hs
  rw [norm_corankCharacteristic]
  change ‖coeff (m+1) _‖ ≤ survival ((m+1)/2)*(‖Q‖/(m.choose n:ℝ))
  rw [hsum,norm_mul,norm_pow,norm_inv,show ‖(2:ℂ)‖ = (2:ℝ) by norm_num,← hs]
  apply (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq
  rw [pow_succ,inv_pow]
  field_simp

theorem signed_conditional_le_corank (θ : ℝ) (n δ : ℕ) (hδ : δ ≤ 1) :
    ‖coeff (2*n+δ+1) (fairSeries (areaCharacter (θ/2)) strictWords)‖/survival ((2*n+δ+1)/2) ≤
      ‖corankCharacteristic θ n δ‖ := by
  apply (div_le_iff₀ (survival_pos _)).mpr
  simpa only [mul_comm (survival _)] using signed_norm_le_corank θ n δ hδ

/-- A conditional bound stated directly on the fair strict-word Fourier
series that is inverted in the central certificate. -/
theorem signed_inner_008 {n δ : ℕ} (hδ : δ ≤ 1) (hn : 2049 ≤ n+δ) {z : ℝ} (hz : 0 < z) (hZ : z ≤ 0.2) :
    ‖coeff (2*n+δ+1) (fairSeries (areaCharacter (z^3/2)) strictWords)‖/survival ((2*n+δ+1)/2) ≤
      100*Real.exp (-(0.157*(2*((n:ℝ)+δ))*z^2)) := by
  exact (signed_conditional_le_corank _ n δ hδ).trans (corank_inner_008 hδ hn hz hZ)

theorem signed_inner_frequency {n δ : ℕ} (hδ : δ ≤ 1) (hn : 2049 ≤ n+δ)
    {θ : ℝ} (hθ : 0 < θ) (ht : θ ≤ 0.008) :
    ‖coeff (2*n+δ+1) (fairSeries (areaCharacter (θ/2)) strictWords)‖/survival ((2*n+δ+1)/2) ≤
      100*Real.exp (-(0.157*(2*((n:ℝ)+δ))*θ^(2/3:ℝ))) := by
  let z := θ^(1/3:ℝ)
  have hz : 0 < z := Real.rpow_pos_of_pos hθ _
  have h₃ : z^3 = θ := by
    dsimp [z]
    rw [← Real.rpow_natCast,← Real.rpow_mul hθ.le]
    norm_num
  have h₂ : z^2 = θ^(2/3:ℝ) := by
    dsimp [z]
    rw [← Real.rpow_natCast,← Real.rpow_mul hθ.le]
    norm_num
  have hZ : z ≤ 0.2 := by
    apply le_of_pow_le_pow_left₀ (n := 3) (by decide) (by norm_num : (0:ℝ) ≤ 0.2)
    exact h₃.trans_le (ht.trans_eq (by norm_num))
  simpa only [h₃,h₂] using signed_inner_008 hδ hn hz hZ

theorem signed_outer_frequency {n δ : ℕ} (hδ : δ ≤ 1) (hm : 1 ≤ 2*n+δ)
    {θ c : ℝ} {L : ℕ} (hL : 0 < L) (hc : 0 ≤ c) (h : KilledBound (θ/2) L (Real.exp (-c*L))) :
    ‖coeff (2*n+δ+1) (fairSeries (areaCharacter (θ/2)) strictWords)‖/survival ((2*n+δ+1)/2) ≤
      16*Real.exp (c*L-c*(63/64)*(2*n+δ)) := by
  apply (signed_conditional_le_corank _ n δ hδ).trans
  rw [norm_corankCharacteristic]
  exact conditional_rank_arc hL hc h n δ hδ hm

end CentralUnimodality
