module

public import CentralUnimodality.ConditionedReturnCost
public import CentralUnimodality.GridPointCount

/-! Localize the normalized first-return sum by the remaining trial time.
The bin size includes one possible lattice point on its boundary. -/
@[expose] public section

namespace CentralUnimodality
open Real

theorem return_ratio_at_fraction {N j : ℕ} (hj : 501≤j) (hle : j≤N) {p : ℝ}
    (p0 : 0<p) (fraction : (N:ℝ)*p≤j) :
    returnMass j/survival N≤(501/1000:ℝ)/(p*sqrt p)/N := by
  have j0 : (0:ℝ)<j := by exact_mod_cast (show 0<j by omega)
  have n0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have sq := sqrt_le_sqrt fraction
  rw [sqrt_mul n0.le] at sq
  have h := mul_le_mul fraction sq (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) j0.le
  apply (returnMass_ratio hj hle).trans
  field_simp [p0,n0,j0,sqrt_pos.mpr p0,sqrt_pos.mpr j0]
  nlinarith only [h]

theorem return_bin_cost (I : Finset ℕ) {N : ℕ} (hn : 0<N) {u lo hi p C : ℝ}
    (u0 : 0<u) (hlh : lo≤hi) (p0 : 0<p) (c0 : 0≤C) (K : ℕ → ℝ)
    (times : ∀ j∈I, 501≤j ∧ j≤N ∧ (N:ℝ)*p≤j ∧ (N-j:ℕ)*(u/N)∈Set.Icc lo hi)
    (cost : ∀ j∈I, K (N-j)≤C) :
    (∑ j ∈ I, returnMass j/survival N*K (N-j))≤
      ((hi-lo)/u+1/N)*((501/1000:ℝ)/(p*sqrt p))*C := by
  have n0 : (0:ℝ)<N := by exact_mod_cast hn
  let τ := u/(N:ℝ)
  have et : τ*(N:ℝ)=u := div_mul_cancel₀ _ n0.ne'
  have num := grid_spacing_card I (div_nonneg u0.le n0.le) (by linarith only [hlh] : u-hi≤u-lo)
    (fun j hj => by
      obtain ⟨_,le,_,time⟩ := times j hj
      rw [Nat.cast_sub le] at time
      change u-hi≤τ*j ∧ τ*j≤u-lo
      change lo≤((N:ℝ)-j)*τ ∧ ((N:ℝ)-j)*τ≤hi at time
      constructor <;> linarith only [time.1,time.2,et])
  have card : (I.card:ℝ)/N≤(hi-lo)/u+1/N := by
    apply le_of_mul_le_mul_left (a:=u) _ u0
    calc
      u*((I.card:ℝ)/N) = (u/N)*I.card := by ring
      _ ≤ (u-lo)-(u-hi)+u/N := num
      _ = u*((hi-lo)/u+1/N) := by field_simp; ring
  let rate := (501/1000:ℝ)/(p*sqrt p)
  have r0 : 0≤rate := by dsimp only [rate]; positivity
  have sum : (∑ j ∈ I, returnMass j/survival N*K (N-j))≤∑ _j ∈ I, (rate/N)*C := by
    apply Finset.sum_le_sum; intro j hj
    obtain ⟨bound,le,frac,_⟩ := times j hj
    have w : 0≤returnMass j/survival N := div_nonneg (by unfold returnMass; positivity) (survival_pos _).le
    exact (mul_le_mul_of_nonneg_left (cost j hj) w).trans
      (mul_le_mul_of_nonneg_right (return_ratio_at_fraction bound le p0 frac) c0)
  apply sum.trans
  rw [Finset.sum_const,nsmul_eq_mul]
  change (I.card:ℝ)*(rate/N*C)≤_*rate*C
  rw [show (I.card:ℝ)*(rate/N*C)=((I.card:ℝ)/N)*rate*C by ring]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right card r0) c0

theorem conditionedCost_split {N : ℕ} (hn : 0<N) (I : Finset ℕ) (sub : I⊆Finset.range (N+1))
    (K : ℕ → ℝ) {C : ℝ} (c0 : 0≤C) (KN : 0≤K N) (early : ∀ j∈I, K (N-j)≤C) :
    conditionedCost N K≤2*sqrt N*(K N+C)+
      ∑ j ∈ Finset.range (N+1) \ I, returnMass j/survival N*K (N-j) := by
  let r := survival N
  have r0 : 0<r := survival_pos N
  have positive (j : ℕ) : 0≤returnMass j := by unfold returnMass; positivity
  have mass : (∑ j ∈ I, returnMass j)≤1 := calc
    _ ≤ ∑ j ∈ Finset.range (N+1), returnMass j := Finset.sum_le_sum_of_subset_of_nonneg sub (fun i _ _ => positive i)
    _ ≤ 1 := by rw [returnMass_sum]; linarith only [survival_pos N]
  have bound : (∑ j ∈ I, returnMass j*K (N-j))≤C := calc
    _ ≤ ∑ j ∈ I, returnMass j*C :=
      Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (early j hj) (positive j))
    _ ≤ C := by rw [← Finset.sum_mul]; exact mul_le_of_le_one_left c0 mass
  have part := Finset.sum_sdiff (f:=fun j => returnMass j*K (N-j)) sub
  have eq : conditionedCost N K=(K N+∑ j ∈ I, returnMass j*K (N-j))/r+
      ∑ j ∈ Finset.range (N+1) \ I, returnMass j/survival N*K (N-j) := by
    unfold conditionedCost; rw [← part,add_comm (∑ j ∈ _ \ _, _),← add_assoc,add_div]
    congr 1
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro j _; ring
  rw [eq]
  apply add_le_add _ le_rfl
  apply (div_le_div_of_nonneg_right (add_le_add le_rfl bound) r0.le).trans
  rw [div_eq_mul_inv,mul_comm]
  exact mul_le_mul_of_nonneg_right (survival_inv_le hn) (add_nonneg KN c0)

end CentralUnimodality
