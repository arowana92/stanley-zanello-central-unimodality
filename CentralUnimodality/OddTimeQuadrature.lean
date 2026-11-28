module

public import CentralUnimodality.RankLossBins

/-! Charge the two neighbors of each odd hitting time to actual bin
lengths. A lattice cell meeting an internal cut contributes its two
pieces to the adjacent bins. -/
@[expose] public section

namespace CentralUnimodality.MarkedExcursion
open Real

private def clip (a b x : ℝ) : ℝ := min b (max a x)
private def overlap (a b u v : ℝ) : ℝ := max 0 (min b v-max a u)

private theorem overlap_eq {a b u v : ℝ} (hab : a≤b) (huv : u≤v) :
    overlap a b u v=clip a b v-clip a b u := by
  simp only [overlap,clip,min_def,max_def]; split_ifs <;> linarith

private theorem overlap_comm (a b u v : ℝ) : overlap a b u v=overlap u v a b := by
  simp only [overlap,min_comm b v,max_comm a u]

private theorem clip_full {a b u v : ℝ} (hab : a≤b) (hu : u≤a) (hv : b≤v) :
    clip a b v-clip a b u=b-a := by
  simp [clip,max_eq_left hu,max_eq_right (hab.trans hv),min_eq_left hv,min_eq_right hab]

/-- Compare a weighted sum on consecutive cells with a different contiguous
partition. The values being bounded may have either sign. -/
theorem cell_partition_bound {D₀ D₁ N : ℕ} (hD : D₀≤D₁) (x e F cap : ℕ→ℝ)
    (hx : Monotone x) (he : Monotone e)
    (ha : e 0≤x D₀) (hb : x D₁≤e N) (hc : ∀ i<N, 0≤cap i)
    (hbound : ∀ d∈Finset.Ico D₀ D₁, ∀ i<N, e i<x (d+1) → x d<e (i+1) → F d≤cap i) :
    ∑ d∈Finset.Ico D₀ D₁, (x (d+1)-x d)*F d ≤ ∑ i∈Finset.range N, (e (i+1)-e i)*cap i := by
  let D := Finset.Ico D₀ D₁
  let I := Finset.range N
  let W (d i : ℕ) := overlap (x d) (x (d+1)) (e i) (e (i+1))
  have hW (d i : ℕ) : 0≤W d i := le_max_left ..
  have hrow (d : ℕ) (hd : d∈D) : ∑ i∈I, W d i=x (d+1)-x d := by
    have hd' := Finset.mem_Ico.mp hd
    simp only [I,W,overlap_eq (hx (Nat.le_succ d)) (he (Nat.le_succ _))]
    rw [Finset.sum_range_sub (fun i => clip (x d) (x (d+1)) (e i))]
    exact clip_full (hx (Nat.le_succ d)) (ha.trans (hx hd'.1)) ((hx hd'.2).trans hb)
  have hcol (i : ℕ) : ∑ d∈D, W d i≤e (i+1)-e i := by
    simp_rw [W,overlap_comm (x _) (x _) (e i) _,overlap_eq (he (Nat.le_succ i)) (hx (Nat.le_succ _))]
    rw [show D=Finset.Ico D₀ D₁ from rfl,Finset.sum_Ico_eq_sub _ hD,Finset.sum_range_sub (fun d => clip (e i) (e (i+1)) (x d)),
      Finset.sum_range_sub (fun d => clip (e i) (e (i+1)) (x d))]
    dsimp only [clip]
    linarith only [min_le_left (e (i+1)) (max (e i) (x D₁)),
      le_min (he (Nat.le_succ i)) (le_max_left (e i) (x D₀))]
  have point (d : ℕ) (hd : d∈D) (i : ℕ) (hi : i∈I) : W d i*F d≤W d i*cap i := by
    by_cases hp : 0<W d i
    · have hs : max (x d) (e i)<min (x (d+1)) (e (i+1)) := by
        change 0<max 0 _ at hp
        exact sub_pos.mp ((lt_max_iff.mp hp).resolve_left (lt_irrefl _))
      exact mul_le_mul_of_nonneg_left (hbound d hd i (Finset.mem_range.mp hi)
        ((le_max_right ..).trans_lt (hs.trans_le (min_le_left ..))) ((le_max_left ..).trans_lt (hs.trans_le (min_le_right ..)))) (hW d i)
    · rw [le_antisymm (le_of_not_gt hp) (hW d i),zero_mul,zero_mul]
  change ∑ d∈D, (x (d+1)-x d)*F d ≤ ∑ i∈I, (e (i+1)-e i)*cap i
  calc
    _ = ∑ d∈D, ∑ i∈I, W d i*F d := Finset.sum_congr rfl (fun d hd => by rw [← Finset.sum_mul,hrow d hd])
    _ ≤ ∑ d∈D, ∑ i∈I, W d i*cap i := Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (point d hd))
    _ = ∑ i∈I, (∑ d∈D,W d i)*cap i := by rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
    _ ≤ _ := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (hcol i) (hc i (Finset.mem_range.mp hi)))

/-- With L=ceil(l*m), T=ceil(h*m), odd times L<t≤T fill disjoint
cells [(t-1)/m,(t+1)/m]. At an overlapping frequency-independent time
bin [e_i,e_(i+1)], the hit lies within one lattice step of the bin. -/
theorem early_loss_cell_bound {m L T N : ℕ} (hLT : L≤T)
    (c : ℝ) (r : Fin 3) (j : ℤ) (e cap : ℕ→ℝ) (he : Monotone e)
    (hlo : e 0*m≤2*((L+1)/2:ℕ)) (hhi : (2:ℝ)*((T+1)/2:ℕ)≤e N*m) (hc : ∀ i<N, 0≤cap i)
    (hbound : ∀ d : ℕ, L<2*d+1 → 2*d+1≤T → ∀ i<N,
      e i*m-1≤2*(d:ℝ)+1 → 2*(d:ℝ)+1≤e (i+1)*m+1 → firstRankLoss c m (2*d+1) r j≤cap i) :
    earlyRankLoss c m L T r j ≤ (m:ℝ)/2*∑ i∈Finset.range N, (e (i+1)-e i)*cap i := by
  let D₀ := (L+1)/2
  let D₁ := (T+1)/2
  let x (d : ℕ) := 2*(d:ℝ)
  let E (i : ℕ) := e i*m
  let F (d : ℕ) := firstRankLoss c m (2*d+1) r j
  have hD : D₀≤D₁ := by dsimp only [D₀,D₁]; omega
  have H := cell_partition_bound hD x E F cap (by intro a b hab; dsimp [x]; gcongr)
    (fun i k hik => mul_le_mul_of_nonneg_right (he hik) (Nat.cast_nonneg _)) hlo hhi hc (by
      intro d hd i hi hl hh
      have hd' := Finset.mem_Ico.mp hd
      dsimp only [D₀,D₁] at hd'
      apply hbound d (by omega) (by omega) i hi
      · dsimp only [E,x] at hl; push_cast at hl; linarith only [hl]
      · dsimp only [E,x] at hh; linarith only [hh])
  have h₁ (i : ℕ) : x (i+1)-x i=2 := by dsimp [x]; push_cast; ring
  have h₂ (i : ℕ) : (E (i+1)-E i)*cap i=(m:ℝ)*((e (i+1)-e i)*cap i) := by dsimp [E]; ring
  simp_rw [h₁,h₂] at H
  rw [← Finset.mul_sum,← Finset.mul_sum] at H
  rw [early_loss_odd]
  dsimp only [D₀,D₁,F] at H
  linarith only [H]

end CentralUnimodality.MarkedExcursion
