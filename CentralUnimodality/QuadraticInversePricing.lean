module

public import CentralUnimodality.QuadraticAmplitude
public import CentralUnimodality.RationalCellWeights

/-! A common inverse price for any nonnegative table of half-unit cell costs
at every half-length from 10,000. Apply it once to each residual order. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Real ReturnSplit

def unitPrice (c : ℕ → ℕ) (k : ℕ) := (c k:ℚ)/10^30
def earlyPrice (c : ℕ → ℕ) (i : ℕ) :=
  ((((Finset.range (i+1)).filter fun k => 19*i/20≤k).sup c:ℕ):ℚ)/10^30
def discountedPrice (c : ℕ → ℕ) (i k : ℕ) := returnDiscount i k*unitPrice c k
def tenThousandWeight (i k : ℕ) : ℚ :=
  let p := latePart i k
  (1/(i:ℚ)+1/10000)*(501/1000)/(p*rootLow p)

def latePrice (c : ℕ → ℕ) (i : ℕ) : ℚ :=
  if i=0 then 0 else ∑ k ∈ Finset.range (19*(i+1)/20+1), roundUpper (tenThousandWeight i k*discountedPrice c i k)

noncomputable def pricedResidual (c : ℕ → ℕ) (i N : ℕ) (u : ℝ) (j : ℕ) : ℝ :=
  timeDiscount i N u j*(unitPrice c (cappedBin i ((j:ℝ)*(u/N))):ℝ)

private theorem weight_upper {N i : ℕ} (hn : 10000≤N) (k : ℕ) :
    (1/(i:ℝ)+1/(N:ℝ))*((501/1000:ℝ)/(lateFraction i k*sqrt (lateFraction i k)))≤(tenThousandWeight i k:ℝ) := by
  let p := latePart i k
  have hp : (1/20:ℚ)≤p := le_max_left ..
  have pr : lateFraction i k=(p:ℝ) := by simp [p,latePart,lateFraction]
  have pr0 : 0<(p:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℚ)<1/20) hp)
  have rpr : 0<(rootLow p:ℝ) := by exact_mod_cast rootLow_pos hp
  have root := (root_brackets (x:=p) (by exact_mod_cast pr0.le)).1
  have inv := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<10000) (by exact_mod_cast hn : (10000:ℝ)≤N)
  rw [pr,← mul_div_assoc]
  unfold tenThousandWeight; push_cast
  change _≤(1/(i:ℝ)+1/10000)*(501/1000)/((p:ℝ)*(rootLow p:ℝ))
  apply div_le_div₀ (by positivity) (by gcongr) (mul_pos pr0 rpr) (mul_le_mul_of_nonneg_left root pr0.le)

theorem quadratic_inverse_price (c : ℕ → ℕ) {N i : ℕ} (hn : 10000≤N) {u : ℝ} (hu : u∈halfInterval i) :
    conditionedCost N (pricedResidual c i N u)≤2*sqrt N*((unitPrice c i:ℝ)+(earlyPrice c i:ℝ))+(latePrice c i:ℝ) := by
  have pos (k : ℕ) : 0≤unitPrice c k := by unfold unitPrice; positivity
  have disc (k : ℕ) : 0≤(discountedPrice c i k:ℝ) := by
    exact_mod_cast mul_nonneg (discount_bounds i k).1 (pos k)
  have early (k : ℕ) (h : 19*i/20≤k) (h' : k≤ i) : (discountedPrice c i k:ℝ)≤(earlyPrice c i:ℝ) := by
    have mem : k∈(Finset.range (i+1)).filter (fun j => 19*i/20≤j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),h⟩
    have cap : unitPrice c k≤earlyPrice c i := div_le_div_of_nonneg_right
      (by exact_mod_cast (Finset.le_sup (f:=c) mem)) (by positivity)
    exact_mod_cast (mul_le_of_le_one_left (pos k) (discount_bounds i k).2).trans cap
  have np : (N:ℝ)≠0 := by exact_mod_cast (by omega : N≠0)
  have bin : cappedBin i u=i := by
    have lo : (i:ℝ)/2≤u := hu.1
    have nz : 0≤2*u := by linarith only [lo,Nat.cast_nonneg (α:=ℝ) i]
    exact min_eq_left ((Nat.le_floor_iff nz).mpr (by linarith only [lo]))
  have eq (j : ℕ) : pricedResidual c i N u j=(discountedPrice c i (cappedBin i ((j:ℝ)*(u/N))):ℝ) := by
    simp [pricedResidual,discountedPrice,timeDiscount]
  have self : discountedPrice c i i=unitPrice c i := by simp [discountedPrice]
  have endpoint : pricedResidual c i N u N=(unitPrice c i:ℝ) := by rw [eq,show (N:ℝ)*(u/N)=u by field_simp,bin,self]
  by_cases e : i=0
  · subst i
    have cap (j : ℕ) (_ : j≤N) : pricedResidual c 0 N u j≤(unitPrice c 0:ℝ) := by simp [eq,cappedBin,discountedPrice]
    have h := conditioned_zero_bin (by omega : 0<N) _ (by rw [endpoint]; exact_mod_cast pos 0) cap
    apply h.trans
    have a := mul_le_mul_of_nonneg_left (early 0 (by decide) le_rfl) (sqrt_nonneg (N:ℝ))
    rw [self] at a
    rw [show (latePrice c 0:ℝ)=0 by simp [latePrice]]
    linarith only [a]
  · have ei := early i (by omega) le_rfl
    have h := conditioned_half_bin hn (Nat.pos_of_ne_zero e) hu (pricedResidual c i N u) _ disc
      (by rw [endpoint]; exact_mod_cast pos i) (by rw [endpoint,self]) (fun _ _ => (eq _).le) ((disc i).trans ei) early
    rw [self] at h
    apply h.trans
    refine add_le_add le_rfl ?_
    simp only [latePrice,ite_eq_right e,lateAllowance,Rat.cast_sum]
    apply Finset.sum_le_sum
    intro k _
    have w := mul_le_mul_of_nonneg_right (weight_upper (i:=i) hn k) (disc k)
    have ru := (Rat.cast_le (K:=ℝ)).mpr (round_upper (tenThousandWeight i k*discountedPrice c i k))
    rw [Rat.cast_mul] at ru
    exact w.trans ru

end CentralUnimodality.PolynomialTrial
