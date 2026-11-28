module

public import CentralUnimodality.SmoothBallotAmplitude
public import CentralUnimodality.ReturnSplitQuadrature

/-! Write the actual residual of an arbitrary ballot Fourier proposal as
a split average and compare it with quadrature at a fixed, finite anchor. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open PowerSeries

noncomputable def complexAverage (N : ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ k ∈ Finset.range (N+1), (weight N k:ℂ)*f k

noncomputable def freeSymbol (ω : ℝ) (σ N : ℕ) : ℂ :=
  coeff (2*N+σ) (fairSeries (areaCharacter ω) words)

/-- Divide both factors by their survival weights before averaging. -/
noncomputable def profile (ω : ℝ) (V : PowerSeries ℂ) (σ N k : ℕ) : ℂ :=
  (coeff (2*k) (fairSeries (areaCharacter ω) bridges)/(survival k:ℂ)) *
    (coeff (2*(N-k)+σ) V/(survival (N-k):ℂ))

theorem residual_split (ω : ℝ) (V : PowerSeries ℂ) (N σ : ℕ) (hs : σ≤1) :
    parityResidual ω V σ N=freeSymbol ω σ N-complexAverage N (profile ω V σ N) := by
  rw [parityResidual,map_sub,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  congr 1
  let B := fairSeries (areaCharacter ω) bridges
  let f := fun k => coeff k B * coeff (2*N+σ-k) V
  have noOdd (k : ℕ) : f (2*k+1)=0 := by
    have emp : bridges (2*k+1)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      obtain ⟨hl,hz⟩ := Finset.mem_filter.mp hw
      have := mem_words.mp hl
      have := bridge_length hz
      omega
    simp [f,B,coeff_walkSeries,emp]
  rw [sum_even_indices f noOdd N σ hs,complexAverage]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have sv (i : ℕ) : (survival i:ℂ)≠0 := by exact_mod_cast (survival_pos i).ne'
  simp only [f,B,profile,weight,Complex.ofReal_mul,show 2*N+σ-2*k=2*(N-k)+σ by omega]
  field_simp [sv]

theorem norm_average_minus {N : ℕ} (f g : ℕ → ℂ) {v : ℝ}
    (h : ∀ k≤N, ‖f k-g k‖≤v) : ‖complexAverage N f-complexAverage N g‖≤v := by
  rw [complexAverage,complexAverage,← Finset.sum_sub_distrib,← average_const N v]
  apply (norm_sum_le ..).trans
  apply Finset.sum_le_sum
  intro k hk
  rw [← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (weight_pos _ _)]
  exact mul_le_mul_of_nonneg_left (h k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))) (weight_pos _ _).le

private theorem complex_sample (N : ℕ) (g : ℝ → ℝ) :
    complexAverage N (fun k => (g ((k:ℝ)/N):ℂ)) = sample N g := by
  simp [complexAverage,sample,average]

theorem residual_anchor {A N σ : ℕ} (hs : σ≤1) (hA : 2≤A) (hN : A≤N)
    (ω : ℝ) (V : PowerSeries ℂ) (g slope : ℝ → ℝ) {M v : ℝ}
    (hM : 0≤M) (hr : QuadraticRemainder g slope M)
    (hprod : ∀ k≤N, ‖profile ω V σ N k - g ((k:ℝ)/N)‖≤v) :
    ‖parityResidual ω V σ N-(freeSymbol ω σ N-(sample A g:ℂ))‖ ≤
      (M/8)*(1/((A:ℝ)-1)-1/((N:ℝ)-1))+v := by
  rw [residual_split _ _ _ _ hs,sub_sub_sub_cancel_left]
  have hnum := norm_average_minus (profile ω V σ N) (fun k => (g ((k:ℝ)/N):ℂ)) hprod
  rw [complex_sample,norm_sub_rev] at hnum
  have htime := sample_anchor hM hr hA hN
  have dist : ‖(sample A g:ℂ)-(sample N g:ℂ)‖≤(M/8)*(1/((A:ℝ)-1)-1/((N:ℝ)-1)) := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]; exact htime
  have tri := norm_add_le ((sample A g:ℂ)-(sample N g:ℂ))
    ((sample N g:ℂ)-complexAverage N (profile ω V σ N))
  rw [sub_add_sub_cancel] at tri
  exact tri.trans (add_le_add dist hnum)

end CentralUnimodality.ReturnSplit
