module

public import CentralUnimodality.AliasBounds
public import CentralUnimodality.Corank
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! Exponential tilting gives a Gaussian upper bound on the upper corank
tail in either staircase. The unrestricted signs have the exact product
of hyperbolic cosines, and every ballot corank is bounded by half the area. -/
@[expose] public section

namespace CentralUnimodality

def squareWeights (m : ℕ) : ℕ := ∑ i ∈ Finset.range m, (i+1)^2

theorem squareWeights_succ (m : ℕ) : squareWeights (m+1) = squareWeights m+(m+1)^2 :=
  Finset.sum_range_succ _ _

theorem squareWeights_closed (m : ℕ) : 6*squareWeights m = m*(m+1)*(2*m+1) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [squareWeights_succ]; nlinarith only [ih]

private theorem free_tilt (t : ℝ) (m : ℕ) :
    (∑ w ∈ words m, Real.exp (t*walkArea w)) ≤ 2^m*Real.exp (t^2*(squareWeights m:ℝ)/2) := by
  let χ (z : ℤ) := Real.exp (t*z)
  have hc : ∀ x y, χ (x+y) = χ x*χ y := by intro x y; simp [χ,mul_add,Real.exp_add]
  induction m with
  | zero => simp [words,walkArea,heights,squareWeights]
  | succ m ih =>
    change (∑ w ∈ words (m+1), χ (walkArea w)) ≤ _
    rw [free_step χ hc]
    have hfac : χ (m+1) + χ (-(m+1:ℤ)) ≤ 2*Real.exp ((t*((m:ℝ)+1))^2/2) := by
      have h := Real.cosh_le_exp_half_sq (t*((m:ℝ)+1))
      rw [Real.cosh_eq] at h
      dsimp [χ]
      push_cast
      rw [mul_neg]
      linarith only [h]
    calc
      _ ≤ (2^m*Real.exp (t^2*(squareWeights m:ℝ)/2))*(2*Real.exp ((t*((m:ℝ)+1))^2/2)) :=
        mul_le_mul ih hfac (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (by positivity)
      _ = (2:ℝ)^(m+1)*Real.exp ((t^2*(squareWeights m:ℝ)/2)+(t*((m:ℝ)+1))^2/2) := by
        rw [Real.exp_add,pow_succ]; ring
      _ = _ := by rw [squareWeights_succ]; push_cast; congr 2; ring

private theorem restricted_tilt (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    corankSum (Real.exp (2*t)) (ballots m) ≤
      2^m*Real.exp (t^2*(squareWeights m:ℝ)/2) := by
  unfold corankSum
  apply le_trans _ (free_tilt t _)
  calc
    _ ≤ ∑ w ∈ ballots m, Real.exp (t*walkArea w) := by
      apply Finset.sum_le_sum
      intro w hw
      rw [← Real.exp_nat_mul,Real.exp_le_exp,walkArea_eq_corank (mem_ballots.mp hw).2]
      simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
      calc
        _ = t*(2*(walkCorank w:ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) ht
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) (fun _ _ _ => (Real.exp_pos _).le)

noncomputable def corankTail (n δ : ℕ) (x : ℝ) : ℕ :=
  ∑ j ∈ Finset.range (n*(n+δ)+1), if x ≤ ((n*(n+δ)-j:ℕ):ℝ) then rankCount (2*n+δ) j else 0

theorem corankTail_chernoff (n δ : ℕ) (hδ : δ ≤ 1) (hm : 0 < 2*n+δ) {x : ℝ} (hx : 0 ≤ x) :
    (corankTail n δ x:ℝ) ≤ 2^(2*n+δ)*Real.exp (-2*x^2/(squareWeights (2*n+δ):ℝ)) := by
  let W : ℝ := squareWeights (2*n+δ)
  have hw' : 0 < squareWeights (2*n+δ) := by
    obtain ⟨k,h⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    rw [h,squareWeights_succ]
    positivity
  have hw : 0 < W := by dsimp only [W]; exact_mod_cast hw'
  let t := 2*x/W
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hsum : Real.exp (2*t*x)*(corankTail n δ x:ℝ) ≤ corankSum (Real.exp (2*t)) (ballots (2*n+δ)) := by
    rw [ballot_rank_polynomial _ n δ hδ,corankTail,Nat.cast_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [nsmul_eq_mul,← Real.exp_nat_mul]
    split
    next h =>
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      rw [Real.exp_le_exp,mul_comm ((n*(n+δ)-j:ℕ):ℝ)]
      exact mul_le_mul_of_nonneg_left h (by positivity)
    next => simp; positivity
  have hh := hsum.trans (restricted_tilt (2*n+δ) ht)
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (2*t*x))).mp
  calc
    _ ≤ _ := hh
    _ = Real.exp (2*t*x)*(2^(2*n+δ)*Real.exp (-2*x^2/W)) := by
      rw [mul_left_comm,← Real.exp_add]
      change _*Real.exp (t^2*W/2) = _*Real.exp _
      congr 2
      dsimp [t]
      field_simp
      ring

end CentralUnimodality
