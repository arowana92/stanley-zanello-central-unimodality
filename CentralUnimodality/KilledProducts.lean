module

public import CentralUnimodality.OuterArcs

/-! Splitting a positive walk at a fixed time multiplies its endpoint
kernels. Thus the verified Fourier rates apply to any number of full blocks,
with the exact survival probability available on the prefix. -/
@[expose] public section

namespace CentralUnimodality

private def ends (a : ℤ) (m : ℕ) : Finset ℤ :=
  ((words m).image fun w => a+displacement w).filter (0 < ·)

private theorem outside_ends (ω : ℝ) (a : ℤ) (m : ℕ) {z : ℤ} (hz : z ∉ ends a m) :
    killedAt ω a m z = 0 := by
  apply Finset.sum_eq_zero
  intro w hw
  rw [ite_eq_right]
  rintro ⟨hs,rfl⟩
  exact hz (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨w,hw,rfl⟩,
    hs _ (endpoint_mem_vertices a w)⟩)

private theorem kernel_product (ω : ℝ) (a : ℤ) (m n : ℕ) (z : ℤ) :
    killedAt ω a (m+n) z = ∑ y ∈ ends a m, killedAt ω a m y*killedAt ω y n z := by
  induction n generalizing z with
  | zero =>
    simp only [Nat.add_zero]
    have h : ∀ y ∈ ends a m, killedAt ω a m y*killedAt ω y 0 z =
        if y=z then killedAt ω a m z else 0 := by
      intro y hy
      rw [killedAt_zero _ (Finset.mem_filter.mp hy).2]
      by_cases he : y=z
      · subst z
        simp
      · simp [he,Ne.symm he]
    rw [Finset.sum_congr rfl h]
    by_cases hz : z ∈ ends a m
    · simp [hz]
    · simp [outside_ends ω a m hz]
  | succ n ih =>
    by_cases hz : 0 < z
    · rw [← Nat.add_assoc,killedAt_step _ _ _ hz,ih,ih,← Finset.sum_add_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [killedAt_step _ _ _ hz]
      ring
    · have hz' := le_of_not_gt hz
      simp [killedAt_nonpos _ _ _ hz']

/-- A normalized bound on the sum of endpoint norms from each positive height. -/
def KilledBound (ω : ℝ) (n : ℕ) (q : ℝ) : Prop :=
  ∀ (a : ℕ), 0 < a → ∀ s : Finset ℤ, (∑ z ∈ s, ‖killedAt ω a n z‖) ≤ 2^n*q

private theorem product_norm {ω q : ℝ} {n : ℕ} (hn : KilledBound ω n q)
    (a m : ℕ) (s : Finset ℤ) :
    (∑ z ∈ s, ‖killedAt ω a (m+n) z‖) ≤
      (∑ y ∈ ends a m, ‖killedAt ω a m y‖)*(2^n*q) := by
  simp_rw [kernel_product ω (a:ℤ) m n]
  apply (Finset.sum_le_sum (fun _ _ => norm_sum_le ..)).trans
  simp only [norm_mul]
  rw [Finset.sum_comm,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro y hy
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hp : 0 < y := (Finset.mem_filter.mp hy).2
  simpa only [Int.toNat_of_nonneg hp.le] using hn y.toNat (by omega) s

theorem killedBound_mul {ω q r : ℝ} {m n : ℕ} (hm : KilledBound ω m q)
    (hn : KilledBound ω n r) (hr : 0 ≤ r) : KilledBound ω (m+n) (q*r) := by
  intro a ha s
  apply (product_norm hn a m s).trans
  calc
    _ ≤ (2^m*q)*(2^n*r) := mul_le_mul_of_nonneg_right (hm a ha _) (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem killedBound_one (ω : ℝ) (n : ℕ) : KilledBound ω n 1 := by
  intro a ha s
  have hh := survivor_hit_total ha n
  have hs : (survivors a n).card ≤ 2^n := by omega
  simpa using (killed_norm_le_survivors ω a n s).trans (by exact_mod_cast hs : ((survivors a n).card:ℝ) ≤ 2^n)

theorem killedBound_blocks {ω q : ℝ} {L : ℕ} (h : KilledBound ω L q) (hq : 0 ≤ q) (k : ℕ) :
    KilledBound ω (k*L) (q^k) := by
  induction k with
  | zero => simpa using killedBound_one ω 0
  | succ k ih => simpa only [Nat.succ_mul,pow_succ] using killedBound_mul ih h hq

theorem killed_prefix_blocks {ω q : ℝ} {L : ℕ} (h : KilledBound ω L q) (hq : 0 ≤ q)
    (a p k : ℕ) (s : Finset ℤ) :
    (∑ z ∈ s, ‖killedAt ω a (p+k*L) z‖)/(2:ℝ)^(p+k*L) ≤
      ((survivors a p).card/(2:ℝ)^p)*q^k := by
  rw [div_le_iff₀ (by positivity)]
  apply (product_norm (killedBound_blocks h hq k) a p s).trans
  calc
    _ ≤ ((survivors a p).card:ℝ)*(2^(k*L)*q^k) :=
      mul_le_mul_of_nonneg_right (killed_norm_le_survivors ..) (by positivity)
    _ = _ := by rw [pow_add]; field_simp

theorem outer_blocks_008 {θ : ℝ} (ht : 0.008 ≤ θ) (hπ : θ ≤ Real.pi) :
    KilledBound (θ/2) 216 (Real.exp (-0.0078*216)) := by
  intro a ha s
  have h := (div_lt_iff₀ (by positivity)).mp (killed_arc_008 ht hπ ha s)
  linarith only [h]

theorem outer_blocks_032 {θ : ℝ} (ht : 0.032 ≤ θ) (hπ : θ ≤ Real.pi) :
    KilledBound (θ/2) 112 (Real.exp (-0.0155*112)) := by
  intro a ha s
  have h := (div_lt_iff₀ (by positivity)).mp (killed_arc_032 ht hπ ha s)
  linarith only [h]

private theorem sum_kernel_ends (ω : ℝ) (m : ℕ) :
    (∑ z ∈ ends 1 m, killedAt ω 1 m z) =
      ∑ w ∈ ballots m, areaCharacter ω ((heights 1 w).sum) := by
  simp only [killedAt,Finset.sum_comm (s := ends 1 m),ballots,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hb : BallotFrom 0 w
  · have hp := (positive_one_iff w).mpr hb
    have he : 1+displacement w ∈ ends 1 m := Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨w,hw,rfl⟩,hp _ (endpoint_mem_vertices 1 w)⟩
    simp [hp,hb,eq_comm (a := 1+displacement w),he]
  · simp [positive_one_iff,hb]

private theorem character_even (ω : ℝ) (k : ℕ) :
    areaCharacter ω (2*(k:ℤ)) = (areaCharacter ω 2)^k := by
  induction k with
  | zero => simp [areaCharacter_zero]
  | succ k ih => rw [Nat.cast_succ,mul_add,mul_one,areaCharacter_add,ih,pow_succ]

/-- The absolute characteristic sum of the staircase coranks obeys the
block bound with the survival probability of the retained prefix. -/
theorem rank_fourier_blocks {ω q : ℝ} {L : ℕ} (h : KilledBound ω L q) (hq : 0 ≤ q)
    (n δ : ℕ) (hδ : δ ≤ 1) (p k : ℕ) (hm : 2*n+δ = p+k*L) :
    ‖∑ j ∈ Finset.range (n*(n+δ)+1),
      rankCount (2*n+δ) j • (areaCharacter ω 2)^(n*(n+δ)-j)‖/(2:ℝ)^(2*n+δ) ≤
      ((survivors 1 p).card/(2:ℝ)^p)*q^k := by
  let m := 2*n+δ
  have he : (∑ z ∈ ends 1 m, killedAt ω 1 m z) =
      areaCharacter ω ((m:ℤ)+((m+1)/2:ℕ)) * corankSum (areaCharacter ω 2) (ballots m) := by
    rw [sum_kernel_ends,corankSum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    obtain ⟨hl,hb⟩ := mem_ballots.mp hw
    rw [sum_heights,one_mul,walkArea_eq_corank hb,hl,
      show (m:ℤ)+(2*(walkCorank w:ℤ)+((m+1)/2:ℕ)) =
        ((m:ℤ)+((m+1)/2:ℕ))+2*(walkCorank w:ℤ) by omega,areaCharacter_add,character_even]
  have hn := congrArg norm he
  rw [norm_mul,norm_areaCharacter,one_mul] at hn
  rw [← ballot_rank_polynomial _ n δ hδ,← hn]
  apply (div_le_div_of_nonneg_right (norm_sum_le ..) (by positivity)).trans
  change (∑ z ∈ ends 1 m, ‖killedAt ω 1 m z‖)/(2:ℝ)^m ≤ _
  have e : m = p+k*L := hm
  simpa only [← e,Nat.cast_one] using killed_prefix_blocks h hq 1 p k (ends 1 m)

end CentralUnimodality
