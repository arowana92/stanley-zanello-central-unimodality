module

public import CentralUnimodality.PackedBase
public import CentralUnimodality.PeakWindowReduction

/-! The exact row check supplies both families through 191 rows in the
induction whose only large-length analytic input is the peak window. -/
@[expose] public section

namespace CentralUnimodality

private theorem small_start_le_midpoint {n δ : ℕ} (hn : 96≤n) (hs : n≤2048) (hδ : δ≤1) :
    centralStart n (2*n+δ) ≤ n*(n+δ)/2 := by
  let m := 2*n+δ
  have hn₀ : (96:ℝ)≤n := by exact_mod_cast hn
  have hn' : 0≤(n:ℝ) := Nat.cast_nonneg _
  have hM : (m:ℝ) ≤ 3*n := by exact_mod_cast (show m≤3*n by dsimp only [m]; omega)
  have hr : Real.sqrt m ≤ n := (Real.sqrt_le_left hn').mpr
    (hM.trans (by nlinarith only [mul_le_mul_of_nonneg_right hn₀ hn']))
  have hb := mul_le_mul hM hr (Real.sqrt_nonneg _) (by positivity)
  have hD : (n:ℝ)*n ≤ (n*(n+δ):ℕ) := by push_cast; nlinarith only [mul_nonneg hn' (Nat.cast_nonneg (α:=ℝ) δ)]
  change centralStart n m ≤ _
  rw [centralStart,ite_eq_left hs,Nat.le_div_iff_mul_le (by decide : 0<2)]
  have hl := Nat.floor_le (by positivity : 0≤0.1*(m:ℝ)*Real.sqrt m)
  have H : (⌊0.1*(m:ℝ)*Real.sqrt m⌋₊:ℝ)*2 ≤ (n*(n+δ):ℕ) := by
    linarith only [hl,hb,hD,sq_nonneg (n:ℝ)]
  exact_mod_cast H

theorem midpoint_of_full_row {n δ : ℕ} (hn : 96≤n) (hbase : n≤2048) (hδ : δ≤1)
    (hu : UnimodalOn (rankCount (2*n+δ)) 0 (n*(n+δ))) : CentralToMidpoint n δ := by
  have H := (unimodalOn_iff_no_valley _ (Nat.zero_le _)).mp hu.reverse
  apply (unimodalOn_iff_no_valley _ (small_start_le_midpoint hn hbase hδ)).mpr
  intro i j _ hij hj hf
  exact H i j (Nat.zero_le _) hij (by omega) hf

theorem midpoint_through_191 {n δ : ℕ} (hn : 96≤n) (hbase : n≤191) (hδ : δ≤1) :
    CentralToMidpoint n δ := by
  apply midpoint_of_full_row hn (by omega) hδ
  rcases (show δ=0 ∨ δ=1 by omega) with rfl|rfl
  · simpa using (central_through_191 hbase).1
  · exact (central_through_191 hbase).2

theorem conjecture34_from_192 (hD : DyckComparisons)
    (hsmall : ∀ n ≥ 192, ∀ δ ≤ 1, 2*n+δ < 4096 → CentralToMidpoint n δ)
    (hbig : ∀ n ≥ 192, ∀ δ ≤ 1, 4096 ≤ 2*n+δ → CentralPeakWindow n δ) :
    Conjecture34 := by
  apply conjecture34_of_peak_windows hD
  · intro n hn δ hδ hm
    by_cases h : 192≤n
    · exact hsmall n h δ hδ hm
    · exact midpoint_through_191 hn (by omega) hδ
  · intro n _ δ hδ hm
    exact hbig n (by omega) δ hδ hm

end CentralUnimodality
