module

public import CentralUnimodality.PeakFirstCharge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Sum the signed, restored first-hit differences using disjoint odd
lattice cells. Every time bin is charged its exact width. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
open Real

theorem sum_cell_charges {L T m N : ℕ} (hm : 0<m) (hLT : L≤T) (e F cost : ℕ→ℝ)
    (he : Monotone e) (hlo : e 0*m≤2*((L+1)/2:ℕ)) (hhi : 2*((T+1)/2:ℕ)≤e N*m)
    (hw : ∀ i<N,e i<e (i+1)) (hc : ∀ i<N,0≤cost i)
    (H : ∀ d, L<2*d+1 → 2*d+1≤T → ∀ i<N, e i*m-1≤2*(d:ℝ)+1 → 2*(d:ℝ)+1≤e (i+1)*m+1 →
      (e (i+1)-e i)/2*((m:ℝ)*F d)≤cost i) :
    ∑ d∈Finset.Ico ((L+1)/2) ((T+1)/2),F d≤∑ i∈Finset.range N,cost i := by
  let x (d : ℕ) := 2*(d:ℝ)
  let E (i : ℕ) := e i*m
  let W (i : ℕ) := 2*cost i/((m:ℝ)*(e (i+1)-e i))
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hu (i) (hi : i<N) : 0<(m:ℝ)*(e (i+1)-e i) := mul_pos hm' (sub_pos.mpr (hw i hi))
  have H' := cell_partition_bound (show (L+1)/2≤(T+1)/2 by omega) x E F W
    (by intro a b hab; dsimp [x]; gcongr)
    (fun a b hab => mul_le_mul_of_nonneg_right (he hab) hm'.le) hlo hhi
    (fun i hi => div_nonneg (mul_nonneg (by norm_num) (hc i hi)) (hu i hi).le) (by
      intro d hd i hi hl hh
      have ht := Finset.mem_Ico.mp hd
      have B := H d (by omega) (by omega) i hi
      dsimp only [x,E] at hl hh; push_cast at hl
      have B' := B (by linarith only [hl]) (by linarith only [hh])
      apply (le_div_iff₀ (hu i hi)).mpr; linarith only [B'])
  have A (d : ℕ) : x (d+1)-x d=2 := by dsimp [x]; push_cast; ring
  have B (i : ℕ) (hi : i∈Finset.range N) : (E (i+1)-E i)*W i=2*cost i := by
    have hv := (hu i (Finset.mem_range.mp hi)).ne'
    dsimp only [E,W]
    rw [show e (i+1)*m-e i*m=(m:ℝ)*(e (i+1)-e i) by ring,mul_div_cancel₀ _ hv]
  rw [Finset.sum_congr rfl B] at H'
  simp_rw [A] at H'
  rw [← Finset.mul_sum,← Finset.mul_sum] at H'
  linarith only [H']

theorem all_first_charges {m j : ℕ} {i : Fin 7} {c : ℝ} (h : SaddleAt (tabulated i) m c)
    (hj : meanRank c m=(j+1:ℕ)) :
    let L := timeCut m firstCut
    let T := timeCut m finalCut
    let σ := √(suffixVariance c (m-L))
    let P := live c (c*m) L 1
    (∑ d∈Finset.Ico ((L+1)/2) ((T+1)/2), σ^2/P*
      growthDifference c (j+1:ℕ) (prefixEventSiteMass c m (2*d+1) (hitWords 1 (2*d+1)))) ≤ (earlyTotal i:ℝ) := by
  let L := timeCut m firstCut
  let T := timeCut m finalCut
  let σ := √(suffixVariance c (m-L))
  let P := live c (c*m) L 1
  let G (d : ℕ) := growthDifference c (j+1:ℕ) (prefixEventSiteMass c m (2*d+1) (hitWords 1 (2*d+1)))
  let e (k : ℕ) : ℝ := timeEdge i k
  let cost (k : ℕ) : ℝ := (timeUnits i k:ℝ)/scale
  have hM : (4096:ℝ)≤m := by exact_mod_cast h.large
  have hm : (0:ℝ)<m := by linarith only [hM]
  have hLT : L≤T := Nat.ceil_mono (mul_le_mul_of_nonneg_right (by norm_num [firstCut,finalCut] : (firstCut:ℝ)≤finalCut) hm.le)
  have he : Monotone e := by
    intro j k hjk; apply (Rat.cast_le (K:=ℝ)).mpr
    apply min_le_min_left
    exact add_le_add (le_refl _) (div_le_div_of_nonneg_right (by exact_mod_cast hjk) (Nat.cast_nonneg _))
  have h₀ : timeEdge i 0=firstCut := by simp [timeEdge,firstCut,finalCut,epsilon]; norm_num
  have h₁ : timeEdge i (timeBins i)=finalCut+2*epsilon := by fin_cases i <;> decide +kernel
  have hloe : e 0*m≤2*((L+1)/2:ℕ) := by
    dsimp only [e]; rw [h₀]
    have hh : (firstCut:ℝ)*m≤L := Nat.le_ceil _
    exact hh.trans (by exact_mod_cast (show L≤2*((L+1)/2) by omega))
  have hhie : 2*((T+1)/2:ℕ)≤e (timeBins i)*m := by
    have hT : (T:ℝ)<(finalCut:ℝ)*m+1 := Nat.ceil_lt_add_one (by norm_num [finalCut])
    have hodd : (2:ℝ)*((T+1)/2:ℕ)≤T+1 := by exact_mod_cast (show 2*((T+1)/2)≤T+1 by omega)
    dsimp only [e]; rw [h₁]; dsimp only [epsilon]; push_cast
    linarith only [hT,hodd,hM]
  have hwidth (k : ℕ) (hk : k<timeBins i) : e k<e (k+1) := (Rat.cast_lt (K:=ℝ)).mpr
    (of_decide_eq_true ((checked_growth_budgets i).2.2.1 ⟨k,hk⟩)).2.1
  have HC := sum_cell_charges (by exact_mod_cast hm) hLT e (fun d => σ^2/P*G d) cost he hloe hhie hwidth
    (fun k _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by
      intro d _ _ k hk hl hh
      have H := actual_first_cell hk h hj hl hh
      have hr := (Rat.cast_le (K:=ℝ)).mpr (charge_upper (timeCost (tabulated i) (timeBin i k)))
      change _≤(charge (timeCost (tabulated i) (timeBin i k)):ℝ) at hr
      have hh₁ : (charge (timeCost (tabulated i) (timeBin i k)):ℝ)=cost k := by
        dsimp only [charge,cost,timeUnits]; push_cast; rfl
      rw [hh₁] at hr
      apply le_trans (le_of_eq _) (H.trans hr)
      change (e (k+1)-e k)/2*((m:ℝ)*(σ^2/P*G d))=(e (k+1)-e k)/2*(σ^2/(P/m)*G d)
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
      ring)
  apply HC.trans_eq
  dsimp only [earlyTotal,cost]; push_cast; rw [Finset.sum_div]

end CentralUnimodality.MarkedExcursion.BinArithmetic.Peak
