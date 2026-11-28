module

public import CentralUnimodality.QuadraticPrices

/-! Uniform prices for powers of the mesh after conditioning the return sum. -/
@[expose] public section

namespace CentralUnimodality.PolynomialTrial
open Real ReturnSplit

theorem quadratic_scaled_steps {N : ℕ} (hn : 10000≤N) {u H : ℝ} (hu : 0≤u) (uh : u≤H) :
    u/N≤H/10000 ∧ sqrt N*(u/N)≤100*(H/10000) := by
  have nr : (10000:ℝ)≤N := by exact_mod_cast hn
  have np : 0<(N:ℝ) := by linarith
  have root : sqrt (10000:ℝ)=100 := by rw [show (10000:ℝ)=100^2 by norm_num,Real.sqrt_sq (by norm_num)]
  have sp : 100≤sqrt (N:ℝ) := root ▸ sqrt_le_sqrt nr
  have eq : sqrt N*(u/N)=u/sqrt N := by
    have h := sq_sqrt np.le
    field_simp [(sqrt_pos_of_pos np).ne',np.ne']; nlinarith only [congrArg (u*·) h]
  refine ⟨div_le_div₀ (hu.trans uh) uh (by norm_num) nr,?_⟩
  rw [eq]
  exact (div_le_div₀ (hu.trans uh) uh (by norm_num) sp).trans_eq (by ring)

private theorem late_nonneg (c : ℕ → ℕ) (i : ℕ) : 0≤latePrice c i := by
  unfold latePrice
  split
  · exact le_rfl
  · apply Finset.sum_nonneg
    intro k _; unfold roundUpper; positivity

theorem scaled_inverse_price (c : ℕ → ℕ) (r : ℕ) {N i : ℕ} (hn : 10000≤N)
    {u H : ℝ} (cell : u∈halfInterval i) (hu : 0≤u) (uh : u≤H) :
    (u/N)^(r+1)*conditionedCost N (pricedResidual c i N u)≤(H/10000)^(r+1)*(inverseQuote c i:ℝ) := by
  let t := H/10000
  let τ := u/N
  let a := (unitPrice c i:ℝ)+(earlyPrice c i:ℝ)
  let b := (latePrice c i:ℝ)
  have a0 : 0≤2*a := by dsimp [a,unitPrice,earlyPrice]; push_cast; positivity
  have b0 : 0≤b := by dsimp only [b]; exact_mod_cast late_nonneg c i
  have h0 : 0≤t := div_nonneg (hu.trans uh) (by norm_num)
  have t0 : 0≤τ := div_nonneg hu (Nat.cast_nonneg _)
  obtain ⟨step,first⟩ := quadratic_scaled_steps hn hu uh
  have weighted : sqrt N*τ^(r+1)≤100*t^(r+1) := by
    rw [pow_succ',pow_succ',← mul_assoc,← mul_assoc]
    exact mul_le_mul first (pow_le_pow_left₀ t0 step r) (pow_nonneg t0 _) (mul_nonneg (by norm_num) h0)
  calc
    _≤τ^(r+1)*(2*sqrt N*a+b) := mul_le_mul_of_nonneg_left (quadratic_inverse_price c hn cell) (pow_nonneg t0 _)
    _=2*a*(sqrt N*τ^(r+1))+b*τ^(r+1) := by ring
    _≤2*a*(100*t^(r+1))+b*t^(r+1) := add_le_add (mul_le_mul_of_nonneg_left weighted a0)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ t0 step (r+1)) b0)
    _=_ := by simp only [inverseQuote,Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat]; dsimp only [a,b,t]; ring

theorem quadratic_allowance_nonneg (i : ℕ) : 0≤quadraticFrequencyAllowance i := by
  by_cases hi : i<228
  · have q (c : ℕ → ℕ) : 0≤ inverseQuote c i := by
      have h := late_nonneg c i
      unfold inverseQuote unitPrice earlyPrice
      positivity
    have a := q secondPrice
    have b := q cubicPrice
    simp only [quadraticFrequencyAllowance,ite_eq_left hi]
    unfold topFrequency topTime rootHigh
    positivity
  · simpa only [quadraticFrequencyAllowance,frequencyAllowance,ite_eq_right hi] using frequencyAllowance_nonneg i

end CentralUnimodality.PolynomialTrial
