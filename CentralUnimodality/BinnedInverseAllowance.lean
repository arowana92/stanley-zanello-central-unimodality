module

public import CentralUnimodality.CorrectedTimeBins

/-! Compute a single inverse allowance from the certified half-unit
costs. The estimate is uniform in every half-length from 10,000 onward. -/
@[expose] public section

namespace CentralUnimodality.ReturnSplit
open Real Set

noncomputable def lateFraction (i k : ℕ) : ℝ := max (1/20) (1-((k:ℝ)+1)/i)

noncomputable def lateAllowance (N i : ℕ) (C : ℕ → ℝ) :=
  ∑ k ∈ Finset.range (19*(i+1)/20+1),
    (1/(i:ℝ)+1/(N:ℝ))*((501/1000:ℝ)/(lateFraction i k*sqrt (lateFraction i k)))*C k

theorem conditioned_zero_bin {N : ℕ} (hn : 0<N) (K : ℕ → ℝ) {C : ℝ}
    (pos : 0≤K N) (cap : ∀ j≤N, K j≤C) : conditionedCost N K≤4*sqrt N*C := by
  have c0 := pos.trans (cap N le_rfl)
  have z := conditionedCost_split hn (Finset.range (N+1)) (by rfl) K c0 pos
    (fun j _ => cap _ (Nat.sub_le ..))
  simp only [Finset.sdiff_self,Finset.sum_empty,add_zero] at z
  apply z.trans
  have := mul_le_mul_of_nonneg_left (cap N le_rfl) (sqrt_nonneg (N:ℝ))
  linarith only [this]

theorem conditioned_half_bin {N i : ℕ} (hn : 10000≤N) (ip : 0< i) {u : ℝ} (hu : u∈halfInterval i)
    (K C : ℕ → ℝ) (c0 : ∀ k, 0≤C k) (kn : 0≤K N) (capN : K N≤C i)
    (caps : ∀ j≤N, K (N-j)≤C (cappedBin i (((N-j:ℕ):ℝ)*(u/N))))
    {E : ℝ} (e0 : 0≤E) (early : ∀ k, 19*i/20≤k → k≤ i → C k≤E) :
    conditionedCost N K≤2*sqrt N*(C i+E)+lateAllowance N i C := by
  classical
  let R := Finset.range (N+1)
  let A := R.filter fun j => 20*j≤N
  let L := R \ A
  let tag := fun j : ℕ => cappedBin i (((N-j:ℕ):ℝ)*(u/N))
  let bins := Finset.range (19*(i+1)/20+1)
  let f := fun j : ℕ => returnMass j/survival N*K (N-j)
  have sub : A⊆R := Finset.filter_subset ..
  have n0 : 0<N := by omega
  have ip' : (0:ℝ)< i := by exact_mod_cast ip
  have ulo : (i:ℝ)/2≤u := hu.1
  have up : 0<u := by linarith only [ulo,ip']
  have jle {j : ℕ} (h : j∈L) : j≤N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_sdiff.mp h).1)
  have late {j : ℕ} (h : j∈L) : N<20*j := by
    by_contra! bad
    exact (Finset.mem_sdiff.mp h).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp h).1,bad⟩)
  have hA (j : ℕ) (hj : j∈A) : K (N-j)≤E := by
    obtain ⟨r,small⟩ := Finset.mem_filter.mp hj
    have le : j≤N := Nat.le_of_lt_succ (Finset.mem_range.mp r)
    have H := return_bin_index n0 le hu
    exact (caps j le).trans (early _ (H.2.2.1 small) H.2.1)
  have reduce := conditionedCost_split n0 A sub K e0 kn hA
  have group : (∑ k ∈ bins, ∑ j ∈ L.filter (fun j => tag j=k), f j)=∑ j ∈ L, f j := by
    apply Finset.sum_fiberwise_of_maps_to
    intro j hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((return_bin_index n0 (jle hj) hu).2.2.2 (late hj).le).1)
  change conditionedCost N K≤2*sqrt N*(K N+E)+∑ j ∈ L, f j at reduce
  apply reduce.trans
  rw [← group]
  apply add_le_add (mul_le_mul_of_nonneg_left (add_le_add capN le_rfl) (by positivity)) _
  apply Finset.sum_le_sum
  intro k _
  let I := L.filter (fun j => tag j=k)
  let p := lateFraction i k
  have p0 : 0<p := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/20) (le_max_left ..)
  have points (j : ℕ) (hj : j∈I) : 501≤j ∧ j≤N ∧ (N:ℝ)*p≤j ∧
      ((N-j:ℕ):ℝ)*(u/N)∈Icc ((k:ℝ)/2) (((k:ℝ)+1)/2) := by
    obtain ⟨hl,t⟩ := Finset.mem_filter.mp hj
    have le := jle hl
    have large := late hl
    have H := return_bin_index n0 le hu
    have last := H.2.2.2 large.le
    change tag j=k at t
    have share : (N:ℝ)*p≤j := by
      dsimp only [p,lateFraction]
      rw [mul_max_of_nonneg _ _ (Nat.cast_nonneg (α:=ℝ) N)]
      refine max_le ?_ ?_
      · linarith only [last.2.1]
      · rw [← t]; exact last.2.2 ip
    have mem : ((N-j:ℕ):ℝ)*(u/N)∈halfInterval (tag j) := H.1
    rw [t] at mem
    exact ⟨by omega,le,share,mem.1,by exact_mod_cast mem.2⟩
  have Kcap (j : ℕ) (hj : j∈I) : K (N-j)≤C k := by
    obtain ⟨hl,t⟩ := Finset.mem_filter.mp hj
    exact t ▸ caps j (jle hl)
  have B := return_bin_cost I n0 up (show (k:ℝ)/2≤((k:ℝ)+1)/2 by linarith) p0 (c0 k) K points Kcap
  apply B.trans
  have width : (((k:ℝ)+1)/2-k/2)/u≤1/(i:ℝ) := by
    apply (div_le_div_iff₀ up ip').mpr; linarith only [ulo]
  apply mul_le_mul_of_nonneg_right _ (c0 k)
  apply mul_le_mul_of_nonneg_right (add_le_add width le_rfl)
  positivity

end CentralUnimodality.ReturnSplit
